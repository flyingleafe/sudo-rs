import SudoRsProofs.SanitizeAliases
import SudoRsProofs.GetAliases

/-!
# Alias preprocessing: the order is a sorted permutation

Partial correctness of the extracted `sanitize_alias_table`: a successful return is assumed,
termination is not proved here. The proof relies on the `HashSet` model (a list of
keys; `insert` tests membership with the key's equality) and on the `alias_diagnostic` model
(appends exactly one error) of `SudoRs/FunsExternal.lean`.

* `sanitize_alias_table_distinct`: the returned positions are pairwise distinct and the
  diagnostics passed in are a prefix of the returned ones.
* `sanitize_alias_table_sorted`: if no diagnostic was added, the abstracted table is a
  permutation of the definitions with unique names in which every referenced alias is defined
  earlier (`SudoersSpec.Sorted`).
* `sanitize_alias_table_demonstration`, `sanitize_find_item_expanded`: the alias
  demonstration of the specification for that table, at spec level and through the extracted
  `get_aliases`/`find_item`.

The visitor proof is a mutual `fixpoint_induct` over `visit`/`visit_loop` with the
postcondition `Post`: the invariant `Inv` (distinct positions, each one visited), growth of
`seen` and of `order` by fresh positions only, diagnostics only appended, and a potential
(`pot`, members of unvisited definitions) bounding the number of diagnostics, used by the
termination proof.
-/

open Aeneas Aeneas.Std Result Lean.Order
open Aeneas.Std.alloc.vec (Vec)
open sudo_rs sudo_rs.sudoers

namespace SudoRsProofs
namespace Sanitize

/-! ## Primitive operations -/

theorem anyM_ok {α : Type} (p : α → Bool) (l : List α) :
    l.anyM (m := Result) (fun x => ok (p x)) = ok (l.any p) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.anyM, List.any_cons]
    cases p a <;> simp [ih]; rfl

theorem any_eq_decide_mem {K : Type} [BEq K] [LawfulBEq K] (keys : List K) (key : K) :
    keys.any (fun x => key == x) = decide (key ∈ keys) := by
  rw [Bool.eq_iff_iff]
  simp only [List.any_eq_true, beq_iff_eq, decide_eq_true_eq]
  exact ⟨fun ⟨_, hx, h⟩ => h ▸ hx, fun h => ⟨key, h, rfl⟩⟩

theorem decide_eq_beq {K : Type} [BEq K] [LawfulBEq K] [DecidableEq K] (a b : K) :
    decide (a = b) = (a == b) := by
  rw [Bool.eq_iff_iff, decide_eq_true_iff, beq_iff_eq]

theorem hashSet_insert_eq {K S A H : Type} [BEq K] [LawfulBEq K] (eq : core.cmp.Eq K)
    (hash : core.hash.Hash K) (bh : sudo_rs.core.hash.BuildHasher S H)
    (heq : ∀ a b, eq.partialEqInst.eq a b = ok (a == b))
    (keys : std.collections.hash.set.HashSet K S A) (key : K) :
    std.collections.hash.set.HashSet.insert eq hash bh keys key =
      if key ∈ keys then ok (false, keys) else ok (true, key :: keys) := by
  have h : keys.anyM (m := Result) (eq.partialEqInst.eq key) = ok (decide (key ∈ keys)) := by
    rw [show eq.partialEqInst.eq key = fun x => ok (key == x) from funext (heq key),
      anyM_ok, any_eq_decide_mem]
  unfold std.collections.hash.set.HashSet.insert
  rw [h]
  by_cases hk : key ∈ keys <;> simp [hk]

theorem insert_usize (seen : std.collections.hash.set.HashSet Usize
      std.hash.random.RandomState alloc.alloc.Global) (pos : Usize) :
    std.collections.hash.set.HashSet.insert core.cmp.EqUsize Usize.Insts.CoreHashHash
      std.hash.random.RandomState.Insts.CoreHashBuildHasherDefaultHasher seen pos =
      if pos ∈ seen then ok (false, seen) else ok (true, pos :: seen) :=
  hashSet_insert_eq _ _ _ (fun a b => by simp [decide_eq_beq]) _ _

theorem insert_string (dupe : std.collections.hash.set.HashSet String
      std.hash.random.RandomState alloc.alloc.Global) (k : String) :
    std.collections.hash.set.HashSet.insert
      (Shared0A.Insts.CoreCmpEq alloc.string.String.Insts.CoreCmpEq)
      (Shared0T.Insts.CoreHashHash alloc.string.String.Insts.CoreHashHash)
      std.hash.random.RandomState.Insts.CoreHashBuildHasherDefaultHasher dupe k =
      if k ∈ dupe then ok (false, dupe) else ok (true, k :: dupe) :=
  hashSet_insert_eq _ _ _ (fun a b => by
    simp [alloc.string.String.Insts.CoreCmpPartialEqString.eq]) _ _

theorem contains_usize (s : Slice Usize) (pos : Usize) :
    core.slice.Slice.contains core.cmp.PartialEqUsize s pos = ok (decide (pos ∈ s.val)) := by
  unfold core.slice.Slice.contains
  rw [show core.cmp.PartialEqUsize.eq pos = fun x => ok (pos == x) by funext x; simp [decide_eq_beq],
    anyM_ok, any_eq_decide_mem]

theorem index_ok {α : Type} {defs : Vec α} {i : Usize} {x : α}
    (h : alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice α) defs i = ok x) :
    ∃ hi : i.val < defs.val.length, x = defs.val[i.val] := by
  have hi := index_lt_of_ok h
  refine ⟨hi, ?_⟩
  rw [alloc.vec.Vec.index_slice_index, alloc.vec.Vec.index_usize] at h
  have he : defs.val[i.val]? = some defs.val[i.val] := by simp [hi]
  simp only [Vec.getElem?_Nat_eq] at h
  simp [he] at h
  exact h.symm

theorem push_ok {α : Type} {v v' : Vec α} {x : α} (h : alloc.vec.Vec.push v x = ok v') :
    v'.val = v.val ++ [x] := by
  unfold alloc.vec.Vec.push at h
  dsimp only at h
  split at h
  · obtain rfl := Result.ok_injective h
    simp
  · simp at h

theorem push_eq {α : Type} (v : Vec α) (x : α) (h : v.val.length < Usize.max) :
    ∃ v', alloc.vec.Vec.push v x = ok v' ∧ v'.val = v.val ++ [x] :=
  exists_eq_ok_of_spec (alloc.vec.Vec.push_spec v x h)

theorem alias_diagnostic_ok {d d' : Vec sudoers.Error} {kind : sudoers.AliasDiagnostic}
    {s : Str} (h : sudoers.alias_diagnostic d kind s = ok d') :
    ∃ e, d'.val = d.val ++ [e] := by
  unfold sudoers.alias_diagnostic at h
  exact ⟨_, push_ok h⟩

theorem alias_diagnostic_eq (d : Vec sudoers.Error) (kind : sudoers.AliasDiagnostic) (s : Str)
    (h : d.val.length < Usize.max) :
    ∃ d', sudoers.alias_diagnostic d kind s = ok d' ∧ d'.val.length = d.val.length + 1 := by
  unfold sudoers.alias_diagnostic
  obtain ⟨d', h1, h2⟩ := push_eq d _ h
  exact ⟨d', h1, by simp [h2]⟩

theorem slice_next_nil {α : Type} (it : core.slice.iter.Iter α)
    (h : it.slice.val.drop it.i = []) :
    core.slice.iter.IteratorSliceIter.next it = ok (none, it) := by
  unfold core.slice.iter.IteratorSliceIter.next
  rw [List.drop_eq_nil_iff] at h
  split
  · rename_i hlt; simp [Slice.len] at hlt; omega
  · rfl

theorem slice_next_cons {α : Type} (it : core.slice.iter.Iter α) {s : α} {rest : List α}
    (h : it.slice.val.drop it.i = s :: rest) :
    core.slice.iter.IteratorSliceIter.next it = ok (some s, { it with i := it.i + 1 }) ∧
      it.slice.val.drop (it.i + 1) = rest := by
  have hlt : it.i < it.slice.val.length := by
    by_contra hc
    rw [List.drop_eq_nil_of_le (by omega)] at h
    cases h
  rw [List.drop_eq_getElem_cons hlt] at h
  obtain ⟨rfl, rfl⟩ := List.cons.inj h
  refine ⟨?_, rfl⟩
  unfold core.slice.iter.IteratorSliceIter.next
  split
  · rfl
  · rename_i hge; simp [Slice.len] at hge; omega

/-! ## Positions, names and references -/

variable {T : Type}

/-- The name of a definition (a wrapper: `RDef T` only unfolds to a pair at default
transparency). -/
def defName (d : RDef T) : String := d.1

/-- The members of a definition. -/
def defItems (d : RDef T) : List (RSpec T) := d.2.val

@[simp] theorem defName_mk (s : String) (m : Vec (RSpec T)) : defName ((s, m) : RDef T) = s := rfl
@[simp] theorem defItems_mk (s : String) (m : Vec (RSpec T)) :
    defItems ((s, m) : RDef T) = m.val := rfl

/-- The name defined at a position, if the position is valid. -/
def nameAt (D : List (RDef T)) (q : Usize) : Option String := D[q.val]?.map defName

/-- The members of the definition at a position (none if the position is invalid). -/
def itemsAt (D : List (RDef T)) (q : Usize) : List (RSpec T) := (D[q.val]?.map defItems).getD []

/-- Every alias referenced by the definition at a position of `o` is the name of a definition
at an earlier position. -/
def Closed (D : List (RDef T)) (o : List Usize) : Prop :=
  ∀ pre p post, o = pre ++ p :: post → ∀ s ∈ itemsAt D p, ∀ k, aliasName s = some k →
    ∃ q ∈ pre, nameAt D q = some k

theorem Closed.nil (D : List (RDef T)) : Closed D [] := by
  intro pre p post h
  cases pre <;> cases h

theorem Closed.snoc {D : List (RDef T)} {o : List Usize} {p : Usize} (h : Closed D o)
    (hp : ∀ s ∈ itemsAt D p, ∀ k, aliasName s = some k → ∃ q ∈ o, nameAt D q = some k) :
    Closed D (o ++ [p]) := by
  intro pre x post hsplit
  rcases List.eq_nil_or_concat post with rfl | ⟨post', y, rfl⟩
  · obtain ⟨rfl, hx⟩ := List.append_inj' hsplit rfl
    simp only [List.cons.injEq, and_true] at hx
    exact hx ▸ hp
  · have hsplit' : o ++ [p] = (pre ++ x :: post') ++ [y] := by simpa using hsplit
    obtain ⟨ho, -⟩ := List.append_inj' hsplit' rfl
    exact h pre x post' ho

/-- The number of members of the definition at index `i`. -/
def memCount (D : List (RDef T)) (i : Nat) : Nat := (D[i]?.map fun d => (defItems d).length).getD 0

/-- Members of definitions not yet visited: an upper bound on the diagnostics the remaining
visits can add. -/
def pot (D : List (RDef T)) (seen : List Usize) : Nat :=
  ∑ i ∈ Finset.range D.length, if i ∈ seen.map (·.val) then 0 else memCount D i

theorem mem_map_val {seen : List Usize} {q : Usize} : q.val ∈ seen.map (·.val) ↔ q ∈ seen := by
  constructor
  · intro h
    obtain ⟨r, hr, hrq⟩ := List.mem_map.1 h
    rwa [← UScalar.val_eq_imp_iff.mpr hrq]
  · exact List.mem_map_of_mem

theorem pot_insert {D : List (RDef T)} {seen : List Usize} {p : Usize}
    (hp : p.val < D.length) (hns : p ∉ seen) :
    pot D (p :: seen) + (itemsAt D p).length = pot D seen := by
  have hmem : p.val ∈ Finset.range D.length := Finset.mem_range.2 hp
  unfold pot
  rw [← Finset.add_sum_erase _ _ hmem, ← Finset.add_sum_erase _ _ hmem]
  have hrest : ∑ i ∈ (Finset.range D.length).erase p.val,
        (if i ∈ (p :: seen).map (·.val) then 0 else memCount D i) =
      ∑ i ∈ (Finset.range D.length).erase p.val,
        (if i ∈ seen.map (·.val) then 0 else memCount D i) := by
    apply Finset.sum_congr rfl
    intro i hi
    have hne : i ≠ p.val := Finset.ne_of_mem_erase hi
    simp [hne]
  have hcount : (itemsAt D p).length = memCount D p.val := by
    simp only [itemsAt, memCount, List.getElem?_eq_getElem hp, Option.map_some, Option.getD_some]
  rw [hrest, hcount, List.map_cons]
  simp only [List.mem_cons, true_or, ↓reduceIte, mt mem_map_val.1 hns]
  omega

/-! ## Invariant and postcondition of the visitor -/

/-- The visitor state: `order` holds distinct visited positions, every visited position is
valid and recorded once. -/
structure Inv (D : List (RDef T)) (seen order : List Usize) : Prop where
  order_nodup : order.Nodup
  order_sub : ∀ q ∈ order, q ∈ seen
  seen_lt : ∀ q ∈ seen, q.val < D.length
  seen_nodup : seen.Nodup

/-- What a successful return of `visit` or of its member loop guarantees, from state
`(seen, order, diags)` to `(seen', order', diags')`: the invariant, growth of `seen`, `order`
only extended by positions not seen before, diagnostics only appended, at most `c`
diagnostics beyond the consumed potential, and `clean` if no diagnostic was added. -/
structure Post (D : List (RDef T)) (seen order : List Usize) (diags : List sudoers.Error)
    (seen' order' : List Usize) (diags' : List sudoers.Error) (c : Nat) (clean : Prop) :
    Prop where
  inv : Inv D seen' order'
  seen_sub : ∀ q ∈ seen, q ∈ seen'
  ext : ∃ added, order' = order ++ added ∧ ∀ q ∈ added, q ∉ seen
  diag_prefix : diags <+: diags'
  pot : diags'.length + pot D seen' ≤ diags.length + pot D seen + c
  clean : diags' = diags → clean

variable {D : List (RDef T)} {seen order seen1 order1 seen2 order2 : List Usize}
  {diags diags1 diags2 : List sudoers.Error} {c c1 c2 : Nat} {P P1 P2 : Prop}

theorem Post.refl (h : Inv D seen order) (hc : P) : Post D seen order diags seen order diags c P :=
  ⟨h, fun _ hq => hq, ⟨[], by simp, by simp⟩, List.prefix_refl _, by omega, fun _ => hc⟩

theorem Post.diag {e : sudoers.Error} (h : Inv D seen order) (hd : diags1 = diags ++ [e])
    (hc : 1 ≤ c) : Post D seen order diags seen order diags1 c P := by
  subst hd
  refine ⟨h, fun _ hq => hq, ⟨[], by simp, by simp⟩, List.prefix_append _ _, ?_, ?_⟩
  · simp only [List.length_append, List.length_singleton]; omega
  · intro he
    have := congrArg List.length he
    simp at this

theorem prefix_eq_of_eq {a b c : List α} (hab : a <+: b) (hbc : b <+: c) (hca : c = a) :
    b = a := by
  subst hca
  exact (hab.eq_of_length (Nat.le_antisymm hab.length_le hbc.length_le)).symm

theorem Post.trans (h1 : Post D seen order diags seen1 order1 diags1 c1 P1)
    (h2 : Post D seen1 order1 diags1 seen2 order2 diags2 c2 P2) (hc : c1 + c2 ≤ c)
    (hP : P1 → P2 → P) : Post D seen order diags seen2 order2 diags2 c P := by
  obtain ⟨-, hs1, ⟨a1, ho1, ha1⟩, hp1, hpot1, hc1⟩ := h1
  obtain ⟨hinv2, hs2, ⟨a2, ho2, ha2⟩, hp2, hpot2, hc2⟩ := h2
  refine ⟨hinv2, fun q hq => hs2 q (hs1 q hq), ⟨a1 ++ a2, by rw [ho2, ho1, List.append_assoc], ?_⟩,
    hp1.trans hp2, by omega, ?_⟩
  · intro q hq
    rcases List.mem_append.1 hq with hq | hq
    · exact ha1 q hq
    · exact fun hs => ha2 q hq (hs1 q hs)
  · intro he
    have he1 := prefix_eq_of_eq hp1 hp2 he
    exact hP (hc1 he1) (hc2 (he.trans he1.symm))

theorem Post.weaken (h : Post D seen order diags seen1 order1 diags1 c1 P1) (hc : c1 ≤ c)
    (hP : P1 → P) : Post D seen order diags seen1 order1 diags1 c P :=
  ⟨h.inv, h.seen_sub, h.ext, h.diag_prefix, by have := h.pot; omega, fun he => hP (h.clean he)⟩

theorem Post.order_sub (h : Post D seen order diags seen1 order1 diags1 c P) :
    ∀ q ∈ order, q ∈ order1 := by
  obtain ⟨a, ho, -⟩ := h.ext
  intro q hq
  rw [ho]
  exact List.mem_append_left _ hq

theorem dependency_position_loop_spec (table : Slice (RDef T)) (k : String) (i : Usize) :
    sanitize_alias_table.dependency_position_loop table k i ⦃ o =>
      ∀ q, o = some q → ∃ h : q.val < table.val.length, defName table.val[q.val] = k ⦄ := by
  unfold sanitize_alias_table.dependency_position_loop
  simp only [alloc.string.String.Insts.CoreCmpPartialEqString.eq]
  split
  · have hlt : i.val < table.val.length := by scalar_tac
    apply WP.spec_bind (Slice.index_usize_spec table i hlt)
    intro d hd
    obtain ⟨s, members⟩ := d
    simp only [uncurry_apply_pair]
    by_cases hb : s = k
    · simp [hb]
      exact ⟨hlt, by rw [← hd, hb, defName_mk]⟩
    · simp [hb]
      step as ⟨i2, hi2⟩
      exact dependency_position_loop_spec table k i2
  · simp
termination_by table.val.length - i.val
decreasing_by all_goals (simp_all; scalar_tac)

/-- `dependency_position` returns a valid position holding the requested name, if any. -/
theorem dependency_position_eq (table : Slice (RDef T)) (k : String) :
    ∃ o, sanitize_alias_table.dependency_position table k = ok o ∧
      ∀ q, o = some q → q.val < table.val.length ∧
        table.val[q.val]?.map defName = some k := by
  obtain ⟨o, ho, hpost⟩ := exists_eq_ok_of_spec (dependency_position_loop_spec table k 0#usize)
  refine ⟨o, ho, fun q hq => ?_⟩
  obtain ⟨hlt, hname⟩ := hpost q hq
  exact ⟨hlt, by simp [List.getElem?_eq_getElem hlt, hname]⟩

theorem Inv.insert {pos : Usize} (h : Inv D seen order) (hns : pos ∉ seen)
    (hlt : pos.val < D.length) : Inv D (pos :: seen) order :=
  ⟨h.order_nodup, fun q hq => List.mem_cons_of_mem _ (h.order_sub q hq),
    fun q hq => by
      rcases List.mem_cons.1 hq with rfl | hq
      · exact hlt
      · exact h.seen_lt q hq,
    List.nodup_cons.2 ⟨hns, h.seen_nodup⟩⟩

/-- The fresh branch of `visit`: the member loop ran from `pos :: seen`, then `pos` is pushed. -/
theorem Post.visit_fresh {pos : Usize} (hinv : Inv D seen order) (hns : pos ∉ seen)
    (hlt : pos.val < D.length)
    (h : Post D (pos :: seen) order diags seen2 order2 diags2 (itemsAt D pos).length
      ((Closed D order → Closed D order2) ∧
        ∀ s ∈ itemsAt D pos, ∀ k, aliasName s = some k → ∃ q ∈ order2, nameAt D q = some k)) :
    Post D seen order diags seen2 (order2 ++ [pos]) diags2 1
      (pos ∈ order2 ++ [pos] ∧ (Closed D order → Closed D (order2 ++ [pos]))) := by
  obtain ⟨hinv2, hs2, ⟨added, ho2, hadded⟩, hpre, hpot, hclean⟩ := h
  have hpos2 : pos ∈ seen2 := hs2 pos List.mem_cons_self
  have hno : pos ∉ order2 := by
    rw [ho2]
    intro hm
    rcases List.mem_append.1 hm with hm | hm
    · exact hns (hinv.order_sub pos hm)
    · exact hadded pos hm List.mem_cons_self
  refine ⟨⟨?_, ?_, hinv2.seen_lt, hinv2.seen_nodup⟩, fun q hq => hs2 q (List.mem_cons_of_mem _ hq),
    ⟨added ++ [pos], by rw [ho2, List.append_assoc], ?_⟩, hpre, ?_, ?_⟩
  · rw [List.nodup_append]
    exact ⟨hinv2.order_nodup, List.nodup_singleton _, by
      intro a ha b hb hab
      rw [List.mem_singleton] at hb
      exact hno (by rw [← hb, ← hab]; exact ha)⟩
  · intro q hq
    rcases List.mem_append.1 hq with hq | hq
    · exact hinv2.order_sub q hq
    · rw [List.mem_singleton] at hq
      exact hq ▸ hpos2
  · intro q hq
    rcases List.mem_append.1 hq with hq | hq
    · exact fun hs => hadded q hq (List.mem_cons_of_mem _ hs)
    · rw [List.mem_singleton] at hq
      exact hq ▸ hns
  · have := pot_insert hlt hns
    omega
  · intro he
    obtain ⟨hcl, hrefs⟩ := hclean he
    exact ⟨List.mem_append_right _ List.mem_cons_self, fun hc => (hcl hc).snoc hrefs⟩

theorem OnReturn.mono {r : Result α} {P Q : α → Prop} (h : OnReturn r P)
    (hPQ : ∀ x, P x → Q x) : OnReturn r Q :=
  fun x hx => hPQ x (h x hx)

/-! ## The visitor: `visit` and its member loop -/

/-- Specification of the member loop of `visit`; `rem` are the members still to process. -/
def LoopSpec (loop : core.slice.iter.Iter (RSpec T) → (Diags → Diags) → HashKeys Usize →
      Vec (RDef T) → Vec Usize → Diags → Result (MembersResult T)) : Prop :=
  ∀ it back seen defs order diags, (∀ x, back x = x) → Inv defs.val seen order.val →
    OnReturn (loop it back seen defs order diags) fun r =>
      r.2.1 = defs ∧ (∀ x, r.2.2.2.2 x = x) ∧
      Post defs.val seen order.val diags.val r.1 r.2.2.1.val r.2.2.2.1.val
        (it.slice.val.drop it.i).length
        ((Closed defs.val order.val → Closed defs.val r.2.2.1.val) ∧
          ∀ s ∈ it.slice.val.drop it.i, ∀ k, aliasName s = some k →
            ∃ q ∈ r.2.2.1.val, nameAt defs.val q = some k)

/-- Specification of `visit`. -/
def VisitSpec (visit : AliasVisitor T → Usize → Result (VisitResult T)) : Prop :=
  ∀ V pos, Inv V.table.val V.seen V.order.val →
    OnReturn (visit V pos) fun r =>
      r.1.table = V.table ∧ (∀ W, (r.2 W).diagnostics = W.diagnostics) ∧
      Post V.table.val V.seen V.order.val V.diagnostics.val r.1.seen r.1.order.val
        r.1.diagnostics.val 1
        (pos ∈ r.1.order.val ∧ (Closed V.table.val V.order.val → Closed V.table.val r.1.order.val))

theorem visitor_spec : LoopSpec (@sanitize_alias_table.Visitor.visit_loop T) ∧
    VisitSpec (@sanitize_alias_table.Visitor.visit T) := by
  apply sanitize_alias_table.Visitor.visit_loop.mutual_fixpoint_induct
    (motive_1 := LoopSpec) (motive_2 := VisitSpec)
  · intro c hc hAll it back seen defs order diags hback hinv
    prove_return_admissible hAll
  · intro c hc hAll V pos hinv
    prove_return_admissible hAll
  · intro loop visit ihLoop ihVisit it back seen defs order diags hback hinv
    simp only
    rcases hrem : it.slice.val.drop it.i with _ | ⟨elem, rest⟩
    · rw [slice_next_nil it hrem]
      simp only [Std.bind_ok, uncurry_apply_pair]
      exact OnReturn.pure ⟨rfl, hback, Post.refl hinv ⟨id, by simp⟩⟩
    · obtain ⟨hnext, hrest⟩ := slice_next_cons it hrem
      rw [hnext]
      simp only [Std.bind_ok, uncurry_apply_pair]
      have hcont : ∀ back1 seen1 order1 diags1, (∀ x, back1 x = x) →
          Inv defs.val seen1 order1.val →
          OnReturn (loop { it with i := it.i + 1 } back1 seen1 defs order1 diags1) fun r =>
            r.2.1 = defs ∧ (∀ x, r.2.2.2.2 x = x) ∧
            Post defs.val seen1 order1.val diags1.val r.1 r.2.2.1.val r.2.2.2.1.val rest.length
              ((Closed defs.val order1.val → Closed defs.val r.2.2.1.val) ∧
                ∀ s ∈ rest, ∀ k, aliasName s = some k →
                  ∃ q ∈ r.2.2.1.val, nameAt defs.val q = some k) := by
        intro back1 seen1 order1 diags1 hback1 hinv1
        have := ihLoop { it with i := it.i + 1 } back1 seen1 defs order1 diags1 hback1 hinv1
        simpa only [hrest] using this
      -- an entry that is not an alias reference
      have hskip : aliasName elem = none →
          OnReturn (loop { it with i := it.i + 1 } back seen defs order diags) fun r =>
            r.2.1 = defs ∧ (∀ x, r.2.2.2.2 x = x) ∧
            Post defs.val seen order.val diags.val r.1 r.2.2.1.val r.2.2.2.1.val
              (elem :: rest).length
              ((Closed defs.val order.val → Closed defs.val r.2.2.1.val) ∧
                ∀ s ∈ elem :: rest, ∀ k, aliasName s = some k →
                  ∃ q ∈ r.2.2.1.val, nameAt defs.val q = some k) := by
        intro hnone
        refine OnReturn.mono (hcont back seen order diags hback hinv) ?_
        rintro r ⟨htab, hb, hpost⟩
        refine ⟨htab, hb, hpost.weaken (by simp) ?_⟩
        rintro ⟨hcl, hrefs⟩
        refine ⟨hcl, fun s hs k hk => ?_⟩
        rcases List.mem_cons.1 hs with rfl | hs
        · rw [hnone] at hk; cases hk
        · exact hrefs s hs k hk
      -- an alias reference
      have halias : ∀ k, aliasName elem = some k →
          OnReturn (do
            let o1 ← sanitize_alias_table.dependency_position (alloc.vec.Vec.deref defs) k
            match o1 with
            | none => do
              let s1 ← alloc.string.String.Insts.CoreOpsDerefDerefStr.deref k
              let v3 ← sudoers.alias_diagnostic diags sudoers.AliasDiagnostic.Undefined s1
              loop { it with i := it.i + 1 } back seen defs order v3
            | some dependency => do
              let (self, visit_back) ←
                visit { seen := seen, table := defs, order := order, diagnostics := diags }
                  dependency
              loop { it with i := it.i + 1 }
                (fun v3 => back (visit_back { self with diagnostics := v3 }).diagnostics)
                self.seen self.table self.order self.diagnostics) fun r =>
            r.2.1 = defs ∧ (∀ x, r.2.2.2.2 x = x) ∧
            Post defs.val seen order.val diags.val r.1 r.2.2.1.val r.2.2.2.1.val
              (elem :: rest).length
              ((Closed defs.val order.val → Closed defs.val r.2.2.1.val) ∧
                ∀ s ∈ elem :: rest, ∀ k, aliasName s = some k →
                  ∃ q ∈ r.2.2.1.val, nameAt defs.val q = some k) := by
        intro k hk
        obtain ⟨o1, ho1, hpos⟩ := dependency_position_eq (alloc.vec.Vec.deref defs) k
        rw [ho1]
        simp only [Std.bind_ok]
        cases o1 with
        | none =>
          apply OnReturn.bind
          intro s1 _
          apply OnReturn.bind
          intro diags1 hd1
          obtain ⟨e, he⟩ := alias_diagnostic_ok hd1
          refine OnReturn.mono (hcont back seen order diags1 hback hinv) ?_
          rintro r ⟨htab, hb, hpost⟩
          exact ⟨htab, hb, (Post.diag (P := False) hinv he le_rfl).trans hpost
            (by simp; omega) (fun h _ => h.elim)⟩
        | some q =>
          obtain ⟨hq, hname⟩ := hpos q rfl
          apply OnReturn.bind
          rintro ⟨V1, vb⟩ hv
          obtain ⟨htab1, hvb, hpost1⟩ := ihVisit _ q hinv _ hv
          simp only at htab1 hvb hpost1
          simp only [uncurry_apply_pair]
          rw [htab1]
          refine OnReturn.mono (hcont _ V1.seen V1.order V1.diagnostics
            (fun x => by simp [hvb, hback]) hpost1.inv) ?_
          rintro r ⟨htab, hb, hpost⟩
          refine ⟨htab, hb, hpost1.trans hpost (by simp; omega) ?_⟩
          rintro ⟨hqo, hcl1⟩ ⟨hcl2, hrefs⟩
          refine ⟨hcl2 ∘ hcl1, fun s hs k' hk' => ?_⟩
          rcases List.mem_cons.1 hs with rfl | hs
          · rw [hk] at hk'
            cases hk'
            exact ⟨q, hpost.order_sub q hqo, by simpa [nameAt] using hname⟩
          · exact hrefs s hs k' hk'
      cases elem with
      | Allow m | Forbid m =>
        simp only [sanitize_alias_table.remqualify, Std.bind_ok]
        cases m with
        | All => exact hskip rfl
        | Only _ => exact hskip rfl
        | Alias k => exact halias k rfl
  · intro loop ihLoop V pos hinv
    simp only
    rw [insert_usize]
    by_cases hs : pos ∈ V.seen
    · simp only [hs, ↓reduceIte, Std.bind_ok, uncurry_apply_pair, Bool.false_eq_true]
      rw [contains_usize]
      simp only [Std.bind_ok, Vec.deref_val]
      by_cases ho : pos ∈ V.order.val
      · simp only [ho, decide_true, ↓reduceIte]
        exact OnReturn.pure ⟨rfl, fun _ => rfl, Post.refl hinv ⟨ho, id⟩⟩
      · simp only [ho, decide_false, Bool.false_eq_true, ↓reduceIte]
        apply OnReturn.bind
        rintro ⟨_, _⟩ _
        simp only [uncurry_apply_pair]
        apply OnReturn.bind
        intro _ _
        apply OnReturn.bind
        intro diags1 hd1
        obtain ⟨e, he⟩ := alias_diagnostic_ok hd1
        exact OnReturn.pure ⟨rfl, fun _ => rfl, Post.diag hinv he le_rfl⟩
    · simp only [hs, ↓reduceIte, Std.bind_ok, uncurry_apply_pair]
      apply OnReturn.bind
      rintro ⟨nm, members⟩ hindex
      obtain ⟨hlt, hd⟩ := index_ok hindex
      have hitems : itemsAt V.table.val pos = members.val := by
        rw [itemsAt, List.getElem?_eq_getElem hlt, ← hd]; rfl
      simp only [uncurry_apply_pair, core.slice.Slice.iter, Std.bind_ok]
      apply OnReturn.bind
      rintro ⟨seen2, defs2, order2, diags2, back2⟩ hloop
      obtain ⟨htab, hback2, hpost⟩ :=
        ihLoop _ (fun v3 => v3) _ _ _ _ (fun _ => rfl) (hinv.insert hs hlt) _ hloop
      simp only [Vec.deref_val, List.drop_zero, ← hitems] at htab hback2 hpost
      simp only [uncurry_apply_pair]
      apply OnReturn.bind
      intro order3 hpush
      have ho3 := push_ok hpush
      refine OnReturn.pure ⟨htab, fun W => by simp [hback2], ?_⟩
      simp only [ho3]
      exact Post.visit_fresh hinv hs hlt hpost

/-! ## The loop over the definitions -/

theorem enumerate_next_nil {α : Type}
    (e : core.iter.adapters.enumerate.Enumerate (core.slice.iter.Iter α))
    (h : e.iter.slice.val.drop e.iter.i = []) :
    core.iter.adapters.enumerate.IteratorEnumerate.next
      (core.iter.traits.iterator.IteratorSliceIter α) e = ok (none, e) := by
  unfold core.iter.adapters.enumerate.IteratorEnumerate.next
  simp only [slice_next_nil _ h, Std.bind_ok, uncurry_apply_pair]

theorem enumerate_next_cons {α : Type}
    (e : core.iter.adapters.enumerate.Enumerate (core.slice.iter.Iter α)) {d : α}
    {rest : List α} (h : e.iter.slice.val.drop e.iter.i = d :: rest)
    (hc : e.count.val + 1 ≤ Usize.max) :
    ∃ c : Usize, c.val = e.count.val + 1 ∧
      core.iter.adapters.enumerate.IteratorEnumerate.next
        (core.iter.traits.iterator.IteratorSliceIter α) e =
        ok (some (e.count, d), { iter := { e.iter with i := e.iter.i + 1 }, count := c }) := by
  obtain ⟨c, hc1, hc2⟩ :=
    exists_eq_ok_of_spec (Usize.add_spec (x := e.count) (y := 1#usize) (by simpa using hc))
  refine ⟨c, by simpa using hc2, ?_⟩
  unfold core.iter.adapters.enumerate.IteratorEnumerate.next
  simp only [(slice_next_cons _ h).1, Std.bind_ok, uncurry_apply_pair, hc1]

/-- Specification of the loop of `sanitize_alias_table` over the definitions, from index
`e.iter.i` on; `dupe` holds the names of the definitions before it. -/
def RootsSpec (loop : core.iter.adapters.enumerate.Enumerate (core.slice.iter.Iter (RDef T)) →
      (Diags → Diags) → HashKeys Usize → Vec (RDef T) → Vec Usize → Diags → HashKeys String →
      Result (Vec Usize × Diags)) : Prop :=
  ∀ e back seen defs order diags dupe, (∀ x, back x = x) →
    e.iter.slice.val = defs.val → e.count.val = e.iter.i →
    Inv defs.val seen order.val →
    (∀ k, k ∈ dupe ↔ k ∈ (defs.val.take e.iter.i).map defName) →
    OnReturn (loop e back seen defs order diags dupe) fun r =>
      (∃ seen', Inv defs.val seen' r.1.val) ∧ diags.val <+: r.2.val ∧
      (r.2.val = diags.val →
        (Closed defs.val order.val → Closed defs.val r.1.val) ∧
        (((defs.val.take e.iter.i).map defName).Nodup → (defs.val.map defName).Nodup) ∧
        ((∀ j < e.iter.i, ∃ q ∈ order.val, q.val = j) →
          ∀ j < defs.val.length, ∃ q ∈ r.1.val, q.val = j))

theorem roots_spec : RootsSpec (@sanitize_alias_table_loop T) := by
  apply sanitize_alias_table_loop.fixpoint_induct (motive := RootsSpec)
  · intro c hc hAll e back seen defs order diags dupe hback hsl hcnt hinv hdupe
    prove_return_admissible hAll
  · intro loop ihLoop e back seen defs order diags dupe hback hsl hcnt hinv hdupe
    simp only
    rcases hrem : defs.val.drop e.iter.i with _ | ⟨d, rest⟩
    · rw [enumerate_next_nil e (by rw [hsl]; exact hrem)]
      simp only [Std.bind_ok, uncurry_apply_pair, hback]
      have hge : defs.val.length ≤ e.iter.i := List.drop_eq_nil_iff.1 hrem
      refine OnReturn.pure ⟨⟨seen, hinv⟩, List.prefix_refl _, fun _ => ⟨id, ?_, ?_⟩⟩
      · rw [List.take_of_length_le hge]; exact id
      · intro h j hj; exact h j (by omega)
    · have hlt : e.iter.i < defs.val.length := by
        by_contra hc
        rw [List.drop_eq_nil_of_le (by omega)] at hrem
        cases hrem
      have hmax : defs.val.length ≤ Usize.max := by scalar_tac
      obtain ⟨c, hc, hnext⟩ := enumerate_next_cons e (by rw [hsl]; exact hrem) (by omega)
      rw [hnext]
      simp only [Std.bind_ok, uncurry_apply_pair]
      have hDi : defs.val[e.iter.i]? = some d := by rw [← List.head?_drop, hrem]; rfl
      obtain ⟨nm, members⟩ := d
      have htake : (defs.val.take (e.iter.i + 1)).map defName =
          (defs.val.take e.iter.i).map defName ++ [nm] := by
        rw [List.take_add_one, hDi, List.map_append]; rfl
      have hcnt' : c.val = e.iter.i + 1 := by rw [hc, hcnt]
      simp only [uncurry_apply_pair]
      rw [insert_string]
      by_cases hn : nm ∈ dupe
      · simp only [hn, ↓reduceIte, Std.bind_ok, uncurry_apply_pair, Bool.false_eq_true]
        apply OnReturn.bind
        intro _ _
        apply OnReturn.bind
        intro diags1 hd1
        obtain ⟨err, he⟩ := alias_diagnostic_ok hd1
        refine OnReturn.mono (ihLoop _ back seen defs order diags1 dupe hback hsl hcnt' hinv ?_) ?_
        · intro k
          rw [hdupe, htake, List.mem_append, List.mem_singleton]
          constructor
          · exact Or.inl
          · rintro (hk | rfl)
            · exact hk
            · exact (hdupe _).1 hn
        · rintro r ⟨hinvr, hpre, -⟩
          refine ⟨hinvr, (he ▸ List.prefix_append _ _ : diags.val <+: diags1.val).trans hpre,
            fun heq => ?_⟩
          have := hpre.length_le
          rw [heq, he] at this
          simp at this
      · simp only [hn, ↓reduceIte, Std.bind_ok, uncurry_apply_pair]
        apply OnReturn.bind
        rintro ⟨V1, vb⟩ hv
        obtain ⟨htab1, hvb, hpost1⟩ :=
          visitor_spec.2 { seen := seen, table := defs, order := order, diagnostics := diags }
            e.count hinv _ hv
        simp only at htab1 hvb hpost1
        simp only [uncurry_apply_pair]
        rw [htab1]
        refine OnReturn.mono (ihLoop _ _ V1.seen defs V1.order V1.diagnostics (nm :: dupe)
          (fun x => by simp [hvb, hback]) hsl hcnt' hpost1.inv ?_) ?_
        · intro k
          rw [List.mem_cons, hdupe, htake, List.mem_append, List.mem_singleton]
          exact Or.comm
        · rintro r ⟨hinvr, hpre, hclean⟩
          refine ⟨hinvr, hpost1.diag_prefix.trans hpre, fun heq => ?_⟩
          have he1 := prefix_eq_of_eq hpost1.diag_prefix hpre heq
          obtain ⟨hpos1, hcl1⟩ := hpost1.clean he1
          obtain ⟨hcl2, hnd2, hall2⟩ := hclean (heq.trans he1.symm)
          refine ⟨hcl2 ∘ hcl1, fun hnd => hnd2 ?_, fun hall => hall2 ?_⟩
          · rw [htake, List.nodup_append]
            refine ⟨hnd, List.nodup_singleton _, ?_⟩
            intro a ha b hb hab
            rw [List.mem_singleton] at hb
            exact hn ((hdupe _).2 (by rw [← hb, ← hab]; exact ha))
          · intro j hj
            rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
            · obtain ⟨q, hq, hqj⟩ := hall j hj
              exact ⟨q, hpost1.order_sub q hq, hqj⟩
            · exact ⟨e.count, hpos1, hcnt⟩

/-- Everything a successful return of `sanitize_alias_table` guarantees about the order:
distinct valid positions, diagnostics only appended, and, if no diagnostic was added, every
position once, unique names, and every reference resolved to an earlier position. -/
theorem sanitize_facts (defs : Vec (RDef T)) (diags : Diags) {order : Vec Usize}
    {diags' : Diags} (h : sanitize_alias_table defs diags = ok (order, diags')) :
    order.val.Nodup ∧ TableWF (order, defs) ∧ diags.val <+: diags'.val ∧
    (diags'.val.length = diags.val.length →
      Closed defs.val order.val ∧ (defs.val.map defName).Nodup ∧
      ∀ j < defs.val.length, ∃ q ∈ order.val, q.val = j) := by
  unfold sanitize_alias_table at h
  simp only [std.collections.hash.set.HashSetTRandomStateGlobal.new, core.slice.Slice.iter,
    core.iter.traits.iterator.Iterator.enumerate.trait_default,
    core.iter.traits.iterator.Iterator.enumerate.default, Std.bind_ok] at h
  have hinv0 : Inv defs.val [] (alloc.vec.Vec.with_capacity Usize (alloc.vec.Vec.len defs)).val :=
    ⟨by simp [alloc.vec.Vec.with_capacity, alloc.vec.Vec.new],
      by simp [alloc.vec.Vec.with_capacity, alloc.vec.Vec.new], by simp, List.nodup_nil⟩
  obtain ⟨⟨seen', hinv'⟩, hpre, hclean⟩ :=
    roots_spec _ _ [] defs _ diags [] (fun _ => rfl) (by simp) (by simp) hinv0 (by simp) _ h
  refine ⟨hinv'.order_nodup, fun q hq => hinv'.seen_lt q (hinv'.order_sub q hq), hpre,
    fun hlen => ?_⟩
  obtain ⟨hcl, hnd, hall⟩ := hclean (hpre.eq_of_length hlen.symm).symm
  refine ⟨hcl ?_, hnd (by simp), hall (by simp)⟩
  simpa [alloc.vec.Vec.with_capacity, alloc.vec.Vec.new] using Closed.nil defs.val

/-! ## From positions to the abstract table -/

theorem filterMap_range_getElem? {α : Type} (D : List α) :
    (List.range D.length).filterMap (fun j => D[j]?) = D := by
  induction D using List.reverseRecOn with
  | nil => rfl
  | append_singleton D x ih =>
    rw [List.length_append, List.length_singleton, List.range_succ, List.filterMap_append]
    have hpre : (List.range D.length).filterMap (fun j => (D ++ [x])[j]?) =
        (List.range D.length).filterMap (fun j => D[j]?) := by
      apply List.filterMap_congr
      intro j hj
      rw [List.getElem?_append_left (List.mem_range.1 hj)]
    rw [hpre, ih]
    simp

theorem tableDefs_perm {defs : Vec (RDef T)} {order : Vec Usize} (hnd : order.val.Nodup)
    (hwf : TableWF (order, defs))
    (hall : ∀ j < defs.val.length, ∃ q ∈ order.val, q.val = j) :
    (tableDefs (order, defs)).Perm defs.val := by
  have hinj : Function.Injective (fun q : Usize => q.val) :=
    fun a b h => UScalar.val_eq_imp_iff.mpr h
  have hL : (order.val.map (·.val)).Perm (List.range defs.val.length) := by
    rw [List.perm_ext_iff_of_nodup (hnd.map hinj) List.nodup_range]
    intro j
    rw [List.mem_range, List.mem_map]
    constructor
    · rintro ⟨q, hq, rfl⟩
      exact hwf q hq
    · exact hall j
  have h := hL.filterMap (fun j => defs.val[j]?)
  rw [List.filterMap_map, filterMap_range_getElem?] at h
  exact h

theorem who_absSpec_alias {β : Type} (f : T → β) (s : RSpec T) (k : String) :
    (absSpec f s).who = .alias k ↔ aliasName s = some k := by
  rcases s with m | m <;> rcases m with _ | _ | n <;>
    simp [absSpec, absQualified, absMeta, aliasName, SudoersSpec.Qualified.who]

theorem Closed.sorted {β : Type} (f : T → β) {defs : Vec (RDef T)} {order : Vec Usize}
    (hcl : Closed defs.val order.val) : SudoersSpec.Sorted (absTable f (order, defs)) := by
  intro pre d post hsplit s hs k hk
  simp only [absTable, tableDefs] at hsplit
  obtain ⟨A, B, hAB, hA, hB⟩ := List.map_eq_append_iff.1 hsplit
  obtain ⟨d0, B', rfl, hd0, -⟩ := List.map_eq_cons_iff.1 hB
  obtain ⟨o1, o2, ho, ho1, ho2⟩ := List.filterMap_eq_append_iff.1 hAB
  obtain ⟨l1, a, l2, rfl, hl1, ha, -⟩ := List.filterMap_eq_cons_iff.1 ho2
  subst hd0 hA
  obtain ⟨s0, hs0, rfl⟩ := List.mem_map.1 hs
  have hitems : itemsAt defs.val a = defItems d0 := by
    simp [itemsAt, ha]
  obtain ⟨q, hq, hqn⟩ := hcl (o1 ++ l1) a l2 (by rw [ho, List.append_assoc]) s0
    (by rw [hitems]; exact hs0) k ((who_absSpec_alias f s0 k).1 hk)
  rcases List.mem_append.1 hq with hq | hq
  · obtain ⟨dq, hdq, hqk⟩ := Option.map_eq_some_iff.1 hqn
    have hmem : dq ∈ List.filterMap (fun i => defs.val[i.val]?) o1 :=
      List.mem_filterMap.2 ⟨q, hq, hdq⟩
    rw [ho1] at hmem
    simp only [SudoersSpec.names, List.map_map]
    exact List.mem_map.2 ⟨dq, hmem, hqk⟩
  · exfalso
    have := hl1 q hq
    simp only [nameAt] at hqn
    simp_all

end Sanitize

open Sanitize in
/-- **Positions are distinct** in every successfully returned order, and the diagnostics
passed in are kept as a prefix. No premise on diagnostics. -/
theorem sanitize_alias_table_distinct {T : Type} (defs : Vec (RDef T)) (diags : Vec sudoers.Error)
    {order : Vec Usize} {diags' : Vec sudoers.Error}
    (h : sanitize_alias_table defs diags = ok (order, diags')) :
    order.val.Nodup ∧ diags.val <+: diags'.val :=
  let hf := sanitize_facts defs diags h
  ⟨hf.1, hf.2.2.1⟩

open Sanitize in
/-- **Order soundness.** If `sanitize_alias_table` returns without adding a diagnostic, the
processing order it computed lists every definition exactly once (a permutation of the file
order), the names are unique, and every alias referenced by a definition is defined earlier
(`SudoersSpec.Sorted`), for every abstraction `f` of the elements. -/
theorem sanitize_alias_table_sorted {T β : Type} (f : T → β) (defs : Vec (RDef T))
    (diags : Vec sudoers.Error) {order : Vec Usize} {diags' : Vec sudoers.Error}
    (h : sanitize_alias_table defs diags = ok (order, diags'))
    (hclean : diags'.val.length = diags.val.length) :
    (defs.val.map (absDef f)).Perm (absTable f (order, defs)) ∧
    (SudoersSpec.names (absTable f (order, defs))).Nodup ∧
    SudoersSpec.Sorted (absTable f (order, defs)) := by
  obtain ⟨hnd, hwf, -, hc⟩ := sanitize_facts defs diags h
  obtain ⟨hcl, hnames, hall⟩ := hc hclean
  have hperm := tableDefs_perm hnd hwf hall
  refine ⟨(hperm.map (absDef f)).symm, ?_, hcl.sorted f⟩
  have hn : SudoersSpec.names (absTable f (order, defs)) = (tableDefs (order, defs)).map defName := by
    simp only [SudoersSpec.names, absTable, List.map_map]; rfl
  rw [hn]
  exact (hperm.map defName).nodup_iff.2 hnames

/-- **The alias demonstration for the sanitizer's output**: `SudoersSpec.demonstration`
instantiated with the file-order table and the order `sanitize_alias_table` computed, when
it added no diagnostic. -/
theorem sanitize_alias_table_demonstration {T β τ : Type} (f : T → β) (defs : Vec (RDef T))
    (diags : Vec sudoers.Error) {order : Vec Usize} {diags' : Vec sudoers.Error}
    (h : sanitize_alias_table defs diags = ok (order, diags'))
    (hclean : diags'.val.length = diags.val.length) (pred : β → Bool)
    (items : List (SudoersSpec.Spec β × τ)) (S : SudoersSpec.FoundAliases)
    (hdef : SudoersSpec.RefsIn (defs.val.map (absDef f)) items) :
    SudoersSpec.AliasFree (SudoersSpec.expandAll (defs.val.map (absDef f)) items) ∧
      SudoersSpec.findItem pred S (SudoersSpec.expandAll (defs.val.map (absDef f)) items) =
        SudoersSpec.findItem pred (SudoersSpec.getAliases (absTable f (order, defs)) pred) items := by
  obtain ⟨hperm, hnd, hs⟩ := sanitize_alias_table_sorted f defs diags h hclean
  refine SudoersSpec.demonstration _ _ pred items S hperm hnd hs ?_
  intro x hx k hk
  exact ((hperm.map (·.name)).mem_iff).1 (hdef x hx k hk)

/-- **Rust-level demonstration**: with the order computed by a clean `sanitize_alias_table`,
the extracted `get_aliases` followed by `find_item` decides exactly as `SudoersSpec.findItem`
on the fully expanded item list (which no longer mentions aliases, so any table `S` gives the
same answer), provided every alias the items name is defined. -/
theorem sanitize_find_item_expanded {P T β : Type} (inst : core.ops.function.Fn P T Bool)
    (pred : P) (f : T → β) (p : β → Bool) (Good : T → Prop)
    (hp : ∀ x, Good x → inst.call pred x = ok (p (f x)))
    (defs : Vec (RDef T)) (diags : Vec sudoers.Error) {order : Vec Usize}
    {diags' : Vec sudoers.Error} (h : sanitize_alias_table defs diags = ok (order, diags'))
    (hclean : diags'.val.length = diags.val.length)
    (hfit : TableFits (order, defs)) (hgood : TableGood Good (order, defs))
    (items : Slice (RSpec T)) (hi : ItemsFit items.val) (hg : ItemsGood Good items.val)
    (hdef : SudoersSpec.RefsIn (defs.val.map (absDef f))
      (SudoersSpec.withUnit (absSpecList f items.val)))
    (S : SudoersSpec.FoundAliases) :
    SudoersSpec.AliasFree (SudoersSpec.expandAll (defs.val.map (absDef f))
      (SudoersSpec.withUnit (absSpecList f items.val))) ∧
    ∃ v, sudo_rs.sudoers.get_aliases inst (order, defs) pred = ok v ∧
      sudo_rs.sudoers.find_item inst items pred v =
        ok (SudoersSpec.findItem p S (SudoersSpec.expandAll (defs.val.map (absDef f))
          (SudoersSpec.withUnit (absSpecList f items.val)))).isSome := by
  have hwf := sanitize_alias_table_tableWF defs diags h
  obtain ⟨hfree, heq⟩ := sanitize_alias_table_demonstration f defs diags h hclean p
    (SudoersSpec.withUnit (absSpecList f items.val)) S hdef
  obtain ⟨v, hv, habs, hvfit⟩ :=
    exists_eq_ok_of_spec (get_aliases_spec inst pred f p Good hp (order, defs) hwf hfit hgood)
  refine ⟨hfree, v, hv, ?_⟩
  rw [find_item_eq inst pred f p Good hp items v hvfit hi hg, heq, habs]

end SudoRsProofs
