import SudoersSpec.Grammar.List

/-!
# IPv4-like host names, declaratively

`Hostname::construct` refuses a name when the pieces of `text.rsplitn(5, '.')` are at most four,
each non-empty, at most 3 bytes and `char::is_numeric` (`Hostname.looksLikeIPv4`). Declaratively
(`IPv4Like`): the name is one to four dot-separated parts, each non-empty, at most 3 bytes long,
of numeric characters other than `.`. `looksLikeIPv4_iff` proves the two equal, for every
oracle.
-/

namespace SudoersSpec.Grammar

open SudoersSpec.Syntax

/-- `parts` joined with the separator `sep`. -/
def joinWith (sep : Char) : List (List Char) → List Char
  | [] => []
  | [p] => p
  | p :: q :: ps => p ++ sep :: joinWith sep (q :: ps)

/-- A part of an IPv4-like name. -/
def IPv4Part (O : CharOracle) (p : List Char) : Prop :=
  p ≠ [] ∧ utf8Len p ≤ 3 ∧ ∀ x ∈ p, O.isNumeric x = true ∧ x ≠ '.'

/-- A host name that `Hostname::construct` refuses: one to four dot-separated `IPv4Part`s
(`1.2.3.4`, but also `1.2.3` and `123`). -/
def IPv4Like (O : CharOracle) (raw : List Char) : Prop :=
  ∃ parts : List (List Char), parts ≠ [] ∧ parts.length ≤ 4 ∧ raw = joinWith '.' parts ∧
    ∀ p ∈ parts, IPv4Part O p

/-! ## `splitn` -/

theorem span_loop_eq {α : Type} (p : α → Bool) :
    ∀ (l acc : List α), List.span.loop p l acc = (acc.reverse ++ l.takeWhile p, l.dropWhile p)
  | [], acc => by simp [List.span.loop]
  | a :: l, acc => by
    cases h : p a <;> simp [List.span.loop, h, span_loop_eq p l]

theorem span_eq {α : Type} {p : α → Bool} {l : List α} :
    l.span p = (l.takeWhile p, l.dropWhile p) := by
  simp [List.span, span_loop_eq]

theorem takeWhile_of_prefix {f : Char → Bool} {bs r : List Char} (hb : ∀ x ∈ bs, f x = true)
    (hr : NextNot (fun d => f d = true) r) : (bs ++ r).takeWhile f = bs := by
  induction bs with
  | nil =>
    cases r with
    | nil => rfl
    | cons d r =>
      have : f d = false := by simpa using NextNot.cons_iff.mp hr
      simp [List.takeWhile_cons, this]
  | cons x bs ih =>
    simp only [List.mem_cons, forall_eq_or_imp] at hb
    simp [List.takeWhile_cons, hb.1, ih hb.2]

theorem span_of_prefix {sep : Char} {p r : List Char} (hp : sep ∉ p) :
    (p ++ sep :: r).span (· != sep) = (p, sep :: r) := by
  have hb : ∀ x ∈ p, (x != sep) = true := by
    intro x hx; simp only [bne_iff_ne, ne_eq]; rintro rfl; exact hp hx
  have hr : NextNot (fun d => (d != sep) = true) (sep :: r) := by
    apply NextNot.cons_iff.mpr; simp
  rw [span_eq, takeWhile_of_prefix hb hr, dropWhile_of_prefix hb hr]

theorem span_of_no_sep {sep : Char} {p : List Char} (hp : sep ∉ p) :
    p.span (· != sep) = (p, []) := by
  have := span_of_prefix (r := []) hp
  have hb : ∀ x ∈ p, (x != sep) = true := by
    intro x hx; simp only [bne_iff_ne, ne_eq]; rintro rfl; exact hp hx
  rw [span_eq]
  have e1 : p.takeWhile (· != sep) = p := by
    have := takeWhile_of_prefix (r := []) hb (NextNot.nil _); simpa using this
  have e2 : p.dropWhile (· != sep) = [] := by
    have := dropWhile_of_prefix (r := []) hb (NextNot.nil _); simpa using this
  rw [e1, e2]

/-- `splitn` gives back pieces that join to the input; if it made fewer pieces than allowed,
none of them contains the separator. -/
theorem splitn_spec (sep : Char) :
    ∀ (n : Nat) (s : List Char),
      splitn (n + 1) sep s ≠ [] ∧ joinWith sep (splitn (n + 1) sep s) = s ∧
        (splitn (n + 1) sep s).length ≤ n + 1 ∧
        ((splitn (n + 1) sep s).length < n + 1 → ∀ p ∈ splitn (n + 1) sep s, sep ∉ p) := by
  intro n
  induction n with
  | zero => intro s; simp [splitn, joinWith]
  | succ n ih =>
    intro s
    rw [show n + 1 + 1 = n + 2 from rfl]
    simp only [splitn]
    have hsp := span_eq (p := (· != sep)) (l := s)
    have hsplit := (List.takeWhile_append_dropWhile (p := (· != sep)) (l := s))
    have hnot : sep ∉ s.takeWhile (· != sep) := by
      intro h
      have := all_takeWhile (f := (· != sep)) (l := s) sep h
      simp at this
    split
    · rename_i piece e
      rw [hsp] at e
      simp only [Prod.mk.injEq] at e
      obtain ⟨e1, e2⟩ := e
      refine ⟨by simp, ?_, by simp, ?_⟩
      · simp only [joinWith]; have := hsplit; rw [e1, e2] at this; simpa using this
      · intro _ p hp; simp only [List.mem_singleton] at hp; subst hp; rw [← e1]; exact hnot
    · rename_i piece x rest e
      rw [hsp] at e
      simp only [Prod.mk.injEq] at e
      obtain ⟨e1, e2⟩ := e
      have hx : x = sep := by
        have := head_dropWhile (f := (· != sep)) (l := s) x (by rw [e2]; rfl)
        simpa using this
      subst hx
      obtain ⟨hne, hj, hl, hs⟩ := ih rest
      refine ⟨by simp, ?_, by simp; omega, ?_⟩
      · obtain ⟨q, qs, hq⟩ : ∃ q qs, splitn (n + 1) x rest = q :: qs := by
          cases h : splitn (n + 1) x rest with
          | nil => exact absurd h hne
          | cons q qs => exact ⟨q, qs, rfl⟩
        rw [hq] at hj ⊢
        simp only [joinWith]
        rw [hj]; have := hsplit; rw [e1, e2] at this; exact this
      · intro hlt p hp
        simp only [List.length_cons] at hlt
        simp only [List.mem_cons] at hp
        rcases hp with rfl | hp
        · rw [← e1]; exact hnot
        · exact hs (by omega) p hp

/-- `splitn` on separator-free parts joined by the separator gives the parts back. -/
theorem splitn_joinWith (sep : Char) :
    ∀ (parts : List (List Char)) (k : Nat), parts ≠ [] → parts.length ≤ k →
      (∀ p ∈ parts, sep ∉ p) → splitn k sep (joinWith sep parts) = parts
  | [], _, h, _, _ => absurd rfl h
  | [p], k, _, hk, hs => by
    have hp := hs p (by simp)
    match k, hk with
    | 1, _ => rfl
    | n + 2, _ => simp [joinWith, splitn, span_of_no_sep hp]
  | p :: q :: ps, k, _, hk, hs => by
    have hp := hs p (by simp)
    match k, hk with
    | n + 2, hk =>
      simp only [joinWith, splitn, span_of_prefix hp]
      rw [splitn_joinWith sep (q :: ps) (n + 1) (by simp) (by simp at hk ⊢; omega)
        (fun p' h' => hs p' (List.mem_cons_of_mem _ h'))]

theorem joinWith_append_single (sep : Char) (y : List Char) :
    ∀ xs : List (List Char), xs ≠ [] → joinWith sep (xs ++ [y]) = joinWith sep xs ++ sep :: y
  | [], h => absurd rfl h
  | [x], _ => rfl
  | x :: x' :: xs, _ => by
    simp only [List.cons_append, joinWith]
    rw [show x' :: (xs ++ [y]) = (x' :: xs) ++ [y] from rfl,
      joinWith_append_single sep y (x' :: xs) (by simp)]
    simp

theorem joinWith_reverse (sep : Char) :
    ∀ parts : List (List Char),
      (joinWith sep parts).reverse = joinWith sep (parts.reverse.map List.reverse)
  | [] => rfl
  | [p] => rfl
  | p :: q :: ps => by
    simp only [joinWith, List.reverse_append, List.reverse_cons, List.append_assoc,
      List.singleton_append]
    rw [joinWith_reverse sep (q :: ps)]
    rw [show (q :: ps).reverse = ps.reverse ++ [q] from List.reverse_cons ..]
    simp only [List.map_append, List.map_cons, List.map_nil, List.append_assoc,
      List.singleton_append]
    rw [show (List.map List.reverse ps.reverse ++ q.reverse :: [p.reverse]) =
      (List.map List.reverse ps.reverse ++ [q.reverse]) ++ [p.reverse] by simp]
    rw [joinWith_append_single sep p.reverse _ (by simp)]

/-- The declarative description of the IPv4 test of `Hostname::construct`. -/
theorem looksLikeIPv4_iff (O : CharOracle) (raw : List Char) :
    Hostname.looksLikeIPv4 O raw = true ↔ IPv4Like O raw := by
  unfold Hostname.looksLikeIPv4 rsplitn
  obtain ⟨hne, hj, hl, hs⟩ := splitn_spec '.' 4 raw.reverse
  generalize hch : splitn (4 + 1) '.' raw.reverse = ch at hne hj hl hs
  have good_iff : ∀ p : List Char,
      ((!p.isEmpty && decide (utf8Len p ≤ 3) && p.all O.isNumeric) = true) ↔
        (p ≠ [] ∧ utf8Len p ≤ 3 ∧ ∀ x ∈ p, O.isNumeric x = true) := by
    intro p; simp [List.isEmpty_iff, List.all_eq_true, and_assoc]
  constructor
  · intro h
    simp only [Bool.and_eq_true] at h
    obtain ⟨hgood, hdrop⟩ := h
    rw [List.isEmpty_iff] at hdrop
    have hlen : ch.length ≤ 4 := by
      have := congrArg List.length hdrop
      simp at this; omega
    have hsep := hs (by omega)
    refine ⟨(ch.map List.reverse).reverse, by simpa using hne, by simpa using hlen, ?_, ?_⟩
    · rw [← List.reverse_reverse raw, ← hj, joinWith_reverse, List.map_reverse]
    · intro p hp
      rw [List.mem_reverse] at hp
      have hp4 : p ∈ (ch.map List.reverse).take 4 := by
        rw [List.take_of_length_le (by simpa using hlen)]; exact hp
      obtain ⟨h1, h2, h3⟩ := (good_iff p).mp (List.all_eq_true.mp hgood p hp4)
      refine ⟨h1, h2, fun x hx => ⟨h3 x hx, ?_⟩⟩
      rintro rfl
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
      exact hsep q hq (List.mem_reverse.mp hx)
  · rintro ⟨parts, hpne, hplen, rfl, hparts⟩
    have hrev := joinWith_reverse '.' parts
    have hsplit : splitn (4 + 1) '.' (joinWith '.' parts).reverse = parts.reverse.map List.reverse := by
      rw [hrev]
      apply splitn_joinWith
      · simpa using hpne
      · simp; omega
      · intro p hp
        obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
        intro hx
        exact (hparts q (List.mem_reverse.mp hq)).2.2 '.' (List.mem_reverse.mp hx) |>.2 rfl
    rw [hch] at hsplit
    subst hsplit
    have e : (parts.reverse.map List.reverse).map List.reverse = parts.reverse := by
      simp [List.map_map, Function.comp_def]
    rw [e]
    simp only [Bool.and_eq_true]
    refine ⟨List.all_eq_true.mpr ?_, List.isEmpty_iff.mpr ?_⟩
    · intro p hp
      have hp' : p ∈ parts := List.mem_reverse.mp (List.mem_of_mem_take hp)
      obtain ⟨h1, h2, h3⟩ := hparts p hp'
      exact (good_iff p).mpr ⟨h1, h2, fun x hx => (h3 x hx).1⟩
    · apply List.drop_eq_nil_of_le; simp; omega

instance (O : CharOracle) (raw : List Char) : Decidable (IPv4Like O raw) :=
  decidable_of_iff _ (looksLikeIPv4_iff O raw)

end SudoersSpec.Grammar
