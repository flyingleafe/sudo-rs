import SudoRsProofs.Parser.Analysis.Provenance.Common

/-! Successful returns of the raw list and line accumulators preserve element predicates. -/

open Aeneas Aeneas.Std Result Lean.Order
open Aeneas.Std.alloc.vec (Vec)
open sudo_rs.sudoers
open scoped SudoRsProofs

namespace SudoRsProofs.Parser.Analysis

variable {T : Type} {P : basic_parser.Parse T} {UF : ast_names.UserFriendly T}
  {good : T → Prop}

private theorem all_on_new {pred : T → Prop} : AllOn pred (alloc.vec.Vec.new T) := by
  simp [AllOn, alloc.vec.Vec.new]

private def ListLoopPreserves (pred : T → Prop)
    (loop : CS → Vec T → Option RStatus → Bool →
      Result (Slice Char × Usize × Usize × Usize × Vec T × Option RStatus)) : Prop :=
  ∀ s acc failure more, AllOn pred acc →
    OnReturn (loop s acc failure more) (fun x => AllOn pred x.2.2.2.2.1)

private theorem parse_list_loop_on_return
    (hP : ∀ s, OnReturn (P.parse s) (fun x => OkOn good x.1)) (sep : Char) (max : Usize) :
    ListLoopPreserves good (basic_parser.parse_list_loop P UF sep max) := by
  apply basic_parser.parse_list_loop.fixpoint_induct (motive := ListLoopPreserves good)
  · intro c hc hAll s acc failure more hall
    prove_return_admissible hAll
  · intro loop ihLoop s acc failure more hall
    simp only
    split
    · provenance_bind ⟨r, s1⟩ _hSep
      simp only [uncurry_apply_pair]
      cases r with
      | Ok _ =>
        by_cases hLimit : alloc.vec.Vec.len acc ≥ max
        · simp only [hLimit, ↓reduceIte]
          provenance_bind _ _hPos
          exact ihLoop _ _ _ _ hall
        · simp only [hLimit, ↓reduceIte]
          provenance_bind ⟨r1, s2⟩ hElem
          have he := expect_nonterminal_on_return (UF := UF) hP s1 (r1, s2) hElem
          simp only [uncurry_apply_pair]
          cases r1 with
          | Ok elem =>
            provenance_bind acc' hPush
            exact ihLoop _ _ _ _ (push_all_on hall he hPush)
          | Err _ => exact ihLoop _ _ _ _ hall
      | Err status => cases status <;> exact ihLoop _ _ _ _ hall
    · exact OnReturn.pure hall

private theorem parse_list_on_return
    (hP : ∀ s, OnReturn (P.parse s) (fun x => OkOn good x.1))
    (sep : Char) (max : Usize) (s : CS) :
    OnReturn (basic_parser.parse_list P UF sep max s) (fun x => OkOn (AllOn good) x.1) := by
  unfold basic_parser.parse_list
  provenance_bind ⟨r, s1⟩ hFirst
  have hr := try_nonterminal_on_return hP s (r, s1) hFirst
  simp only [uncurry_apply_pair]
  cases r with
  | Ok elem =>
    simp only [branch_Ok, bind_ok]
    provenance_bind acc hPush
    have hall : AllOn good acc := push_all_on all_on_new hr hPush
    provenance_bind ⟨_, _, _, _, out, failure⟩ hLoop
    have hout : AllOn good out :=
      parse_list_loop_on_return (UF := UF) hP sep max s1 acc none true hall _ hLoop
    simp only [uncurry_apply_pair]
    cases failure with
    | none =>
      simp only [make_eq, bind_ok]
      exact OnReturn.pure hout
    | some _ => exact OnReturn.pure True.intro
  | Err _ =>
    simp only [branch_Err, from_residual_Err, bind_ok]
    exact OnReturn.pure True.intro

/-- If successful element parses satisfy `good`, so do all elements of a parsed vector. -/
theorem vec_parse_on_return {M : basic_parser.Many T}
    (hP : ∀ s, OnReturn (P.parse s) (fun x => OkOn good x.1)) (s : CS) :
    OnReturn ((sudo_rs.alloc.vec.Vec.Insts.Sudo_rsSudoersBasic_parserParse P M UF).parse s)
      (fun x => OkOn (AllOn good) x.1) := by
  change OnReturn (sudo_rs.alloc.vec.Vec.Insts.Sudo_rsSudoersBasic_parserParse.parse P M UF s) _
  unfold sudo_rs.alloc.vec.Vec.Insts.Sudo_rsSudoersBasic_parserParse.parse
  provenance_bind sep _hSep
  provenance_bind max _hMax
  exact parse_list_on_return (UF := UF) hP sep max s

private def LinesLoopPreserves (pred : T → Prop)
    (loop : CS → Vec (RParsed T) → Bool →
      Result (Slice Char × Usize × Usize × Usize × Vec (RParsed T))) : Prop :=
  ∀ s acc more, AllOn (OkOn pred) acc →
    OnReturn (loop s acc more) (fun x => AllOn (OkOn pred) x.2.2.2.2)

private theorem parse_lines_loop_on_return
    (hP : ∀ s, OnReturn (P.parse s) (fun x => OkOn good x.1)) :
    LinesLoopPreserves good (basic_parser.parse_lines_loop P UF) := by
  apply basic_parser.parse_lines_loop.fixpoint_induct (motive := LinesLoopPreserves good)
  · intro c hc hAll s acc more hall
    prove_return_admissible hAll
  · intro loop ihLoop s acc more hall
    simp only
    split
    · provenance_bind ⟨item, s1⟩ hItem
      have hi := expect_nonterminal_on_return (UF := UF) hP s (item, s1) hItem
      simp only [uncurry_apply_pair]
      provenance_bind parsed _hParsed
      provenance_bind acc1 hPush
      have hall1 := push_all_on hall hi hPush
      provenance_bind ⟨_, s2⟩ _hComment
      simp only [uncurry_apply_pair]
      provenance_bind _ _hMaybe
      provenance_bind ⟨newline, s3⟩ _hEat
      simp only [uncurry_apply_pair]
      cases newline with
      | true =>
        simp only [↓reduceIte, bind_ok, uncurry_apply_pair]
        provenance_bind ⟨more1, s5⟩ _hNext
        exact ihLoop s5 acc1 more1 hall1
      | false =>
        cases parsed with
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte, bind_ok, uncurry_apply_pair, Std.bind_assoc]
          provenance_bind _ _hSkip
          provenance_bind ⟨more1, s5⟩ _hNext
          exact ihLoop s5 acc1 more1 hall1
        | true =>
          simp only [Bool.false_eq_true, ↓reduceIte, bind_ok, uncurry_apply_pair, Std.bind_assoc]
          provenance_bind _ _hPeek
          provenance_bind _ _hKind
          simp only [fatal_here_eq, bind_ok]
          provenance_bind acc4 hDiag
          provenance_bind _ _hSkip
          provenance_bind ⟨more1, s5⟩ _hNext
          refine ihLoop s5 acc4 more1 (push_all_on hall1 ?_ hDiag)
          exact True.intro
    · exact OnReturn.pure hall

/-- Every returned line item is a diagnostic or a successful item satisfying `good`. -/
theorem parse_lines_on_return
    (hP : ∀ s, OnReturn (P.parse s) (fun x => OkOn good x.1)) (s : CS) :
    OnReturn (basic_parser.parse_lines P UF s) (fun x => AllOn (OkOn good) x.1) := by
  unfold basic_parser.parse_lines
  provenance_bind ⟨more, s1⟩ _hFirst
  simp only [uncurry_apply_pair]
  provenance_bind ⟨_, _, _, _, out⟩ hLoop
  exact OnReturn.pure (parse_lines_loop_on_return (UF := UF) hP s1 _ more all_on_new _ hLoop)

end SudoRsProofs.Parser.Analysis
