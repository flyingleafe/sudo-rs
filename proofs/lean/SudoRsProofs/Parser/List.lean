import SudoRsProofs.Parser.Combinators

/-!
# `parse_list` and `impl Parse for Vec<T>`

For any extracted `Parse T` instance refining a reference production (`ParseRefines P f p`)
with a matching description (`DescRel UF d`):

* `parse_list_loop_eq`: the loop of `parse_list` (failure flag, `Vec` accumulator) refines
  `whileMaybe (trySyntax sep) .. (parseListBody max d p)`; the `Vec::push` cannot fail because
  the list is shorter than `max` (a `usize`) when it pushes;
* `parse_list_refines`: `parse_list` refines `parseList`;
* `vec_refines`: the `Vec<T>` instance refines `parseVec` for a `Many` instance that refines the
  reference `Many` (`ManyRefines`). Vectors are abstracted elementwise (`absVec f`).
-/

open Aeneas Aeneas.Std Result
open SudoersSpec.Syntax (Stream ErrKind Parser Parsed)

namespace SudoRsProofs.Parser

variable {T α : Type} {P : sudo_rs.sudoers.basic_parser.Parse T}
  {UF : sudo_rs.sudoers.ast_names.UserFriendly T} {f : T → α} {p : Parser α} {d : String}

/-- A `Vec<T>` as the list of its abstracted elements. -/
def absVec (f : T → α) (v : alloc.vec.Vec T) : List α := v.val.map f

/-- The reference loop of `parse_list` from the elements `elems` read so far. -/
abbrev refListLoop (sep : Char) (max : Nat) (d : String) (p : Parser α) (elems : List α) :
    Parser (List α) :=
  Parser.whileMaybe (SudoersSpec.Syntax.trySyntax sep) (SudoersSpec.Syntax.trySyntax_consumes sep)
    (SudoersSpec.Syntax.parseListBody max d p) id elems

theorem parse_list_loop_false (sep : Char) (max : Usize) (st : CS) (elems : alloc.vec.Vec T)
    (failure : Option RStatus) :
    sudo_rs.sudoers.basic_parser.parse_list_loop P UF sep max st elems failure false =
      ok (st.src, st.pos, st.line, st.col, elems, failure) := by
  rw [sudo_rs.sudoers.basic_parser.parse_list_loop]; simp

theorem parse_list_loop_eq (hP : ParseRefines P f p) (hD : DescRel UF d) (sep : Char)
    (max : Usize) (st : CS) (h : StreamOK st) (elems : alloc.vec.Vec T) :
    ∃ (s' : CS) (elems' : alloc.vec.Vec T) (failure : Option RStatus),
      sudo_rs.sudoers.basic_parser.parse_list_loop P UF sep max st elems none true =
        ok (s'.src, s'.pos, s'.line, s'.col, elems', failure) ∧ StreamOK s' ∧
      ResultRel (absVec f) (match failure with | none => .Ok elems' | some e => .Err e)
        ((refListLoop sep max.val d p (absVec f elems)).run (absStream st)).1 ∧
      absStream s' = ((refListLoop sep max.val d p (absVec f elems)).run (absStream st)).2 := by
  obtain ⟨r, s1, e1, hr, h1, a1⟩ := try_syntax_refines h sep
  rw [sudo_rs.sudoers.basic_parser.parse_list_loop]
  simp only [↓reduceIte, e1, bind_ok, uncurry_apply_pair]
  unfold refListLoop Parser.whileMaybe
  rw [Parser.loop_run]
  simp only [Parser.whileMaybeBody, Parser.run_bind, Parser.run_maybe]
  rcases hR : (SudoersSpec.Syntax.trySyntax sep).run (absStream st) with ⟨r', s''⟩
  rw [hR] at hr a1
  subst a1
  rcases r with ⟨⟩ | (⟨sp, k⟩ | _) <;> rcases r' with (⟨sp', k'⟩ | _) | ⟨⟩ <;>
    simp only [ResultRel, StatusRel.fatal_reject, StatusRel.reject_fatal] at hr
  · -- a separator: the length check, then one element
    simp only [SudoersSpec.Syntax.maybe, SudoersSpec.Syntax.parseListBody]
    by_cases hge : (absVec f elems).length ≥ max.val
    · have hge' : alloc.vec.Vec.len elems ≥ max := by
        simp only [absVec, List.length_map] at hge; scalar_tac
      refine ⟨s1, elems, some (.Fatal ⟨(s1.line, s1.col), (s1.line, s1.col)⟩ .TooManyItems),
        ?_, h1, ?_, ?_⟩
      · simp [hge', parse_list_loop_false]
      · simp [hge, Parser.run_fatalHere]
      · simp [hge, Parser.run_fatalHere]
    · have hge' : ¬ alloc.vec.Vec.len elems ≥ max := by
        simp only [absVec, List.length_map] at hge; scalar_tac
      obtain ⟨r2, s2, e2, hr2, h2, a2⟩ := expect_nonterminal_refines hP hD h1
      simp only [hge, hge', ↓reduceIte, e2, bind_ok, uncurry_apply_pair, Parser.run_bind]
      rcases hE : (SudoersSpec.Syntax.expectNonterminal d p).run (absStream s1) with ⟨r2', s3⟩
      rw [hE] at hr2 a2
      subst a2
      rcases r2 with x | st2 <;> rcases r2' with e2' | a <;> simp only [ResultRel] at hr2
      · -- an element: push it and continue
        have hlen : elems.val.length < Usize.max := by
          simp only [absVec, List.length_map] at hge; scalar_tac
        obtain ⟨elems1, hpush, hpv⟩ := exists_eq_ok_of_spec (alloc.vec.Vec.push_spec elems x hlen)
        have hc := (SudoersSpec.Syntax.trySyntax_consumes sep) _ _ _ hR
        have hl2 := SudoersSpec.Syntax.Parser.length_le_of_run hE
        have hlt : s2.src.val.length - s2.pos.val < st.src.val.length - st.pos.val := by
          simp only [absStream_rest, List.length_drop] at hc hl2; omega
        obtain ⟨s', elems', failure, e', h', hr', a'⟩ :=
          parse_list_loop_eq hP hD sep max s2 h2 elems1
        have habs : absVec f elems1 = absVec f elems ++ [a] := by
          simp [absVec, hpv, hr2]
        simp only [hpush, bind_ok, Parser.run_pure]
        rw [habs] at hr' a'
        exact ⟨s', elems', failure, e', h', hr', a'⟩
      · -- an error of the element: the loop stops with it
        refine ⟨s2, elems, some st2, by simp [parse_list_loop_false], h2, ?_, ?_⟩ <;> simp [hr2]
  · -- a fatal error of the separator
    refine ⟨s1, elems, some (.Fatal sp k), by simp [parse_list_loop_false], h1, ?_, ?_⟩ <;>
      simp [SudoersSpec.Syntax.maybe, hr]
  · -- no separator: the list ends
    refine ⟨s1, elems, none, by simp [parse_list_loop_false], h1, ?_, ?_⟩ <;>
      simp [SudoersSpec.Syntax.maybe, Parser.run_pure]
termination_by (absStream st).rest.length

/-- **`parse_list` refines `parseList`.** -/
theorem parse_list_refines (hP : ParseRefines P f p) (hD : DescRel UF d) (sep : Char)
    (max : Usize) {s : CS} (h : StreamOK s) :
    Refines (absVec f) (sudo_rs.sudoers.basic_parser.parse_list P UF sep max s)
      ((SudoersSpec.Syntax.parseList sep max.val d p).run (absStream s)) := by
  obtain ⟨r, s1, e1, hr, h1, a1⟩ := try_nonterminal_refines hP h
  unfold sudo_rs.sudoers.basic_parser.parse_list
  simp only [SudoersSpec.Syntax.parseList, Parser.run_bind, e1, bind_ok, uncurry_apply_pair]
  rcases hR : (SudoersSpec.Syntax.tryNonterminal p).run (absStream s) with ⟨r', s''⟩
  rw [hR] at hr a1
  subst a1
  rcases r with x | st <;> rcases r' with e' | a <;> simp only [ResultRel] at hr
  · obtain ⟨elems, hpush, hpv⟩ := exists_eq_ok_of_spec
      (alloc.vec.Vec.push_spec (alloc.vec.Vec.new T) x (by simp; scalar_tac))
    obtain ⟨s', elems', failure, e', h', hr', a'⟩ :=
      parse_list_loop_eq hP hD sep max s1 h1 elems
    have habs : absVec f elems = [a] := by simp [absVec, hpv, hr]
    rw [habs] at hr' a'
    simp only [branch_Ok, hpush, bind_ok, e', uncurry_apply_pair]
    rcases hW : (refListLoop sep max.val d p [a]).run (absStream s1) with ⟨w, s3⟩
    rw [hW] at hr' a'
    simp only at a'
    subst a'
    rcases failure with _ | st <;> rcases w with e3 | l <;> simp only [ResultRel] at hr' <;>
      simp [h', hr']
  · simp [hr, h1]

/-- **The `Vec<T>` instance refines `parseVec`.** -/
theorem vec_refines {M : sudo_rs.sudoers.basic_parser.Many T} {m : SudoersSpec.Syntax.Many}
    (hP : ParseRefines P f p) (hM : ManyRefines M m) (hD : DescRel UF d) :
    ParseRefines (sudo_rs.alloc.vec.Vec.Insts.Sudo_rsSudoersBasic_parserParse P M UF) (absVec f)
      (SudoersSpec.Syntax.parseVec m d p) := by
  constructor
  intro s h
  obtain ⟨n, hn, hnv⟩ := hM.limit
  show Refines (absVec f)
    (sudo_rs.alloc.vec.Vec.Insts.Sudo_rsSudoersBasic_parserParse.parse P M UF s) _
  unfold sudo_rs.alloc.vec.Vec.Insts.Sudo_rsSudoersBasic_parserParse.parse
  simp only [hM.sep, hn, bind_ok, SudoersSpec.Syntax.parseVec]
  rw [← hnv]
  exact parse_list_refines hP hD m.sep n h

end SudoRsProofs.Parser
