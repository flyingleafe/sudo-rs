import SudoRsProofs.Parser.Ast
import SudoRsProofs.Parser.Lines

/-!
# Non-vacuity of the P1 theorems

The refinement theorems assume `UnicodeOracle O`: the three `opaque` Unicode predicates return
`ok` with the values of `O`. Nothing about the opaque constants can be proved, so a witness is
necessarily conditional. The condition used here is the evidence recorded in
`proofs/spec/SudoersSpec/Syntax/README.md`: on the code points `U+0000..U+00FF` the Rust
predicates are `CharOracle.latin1` (compared with the pinned `rustc` on all 256 code points).
Under `UnicodeOracle O` and `Latin1Agrees O`, the extracted `host_list` is run on a concrete
input and its result is computed: the other hypotheses (representable stream, input length,
descriptions) are discharged, and the reference side is evaluated by the kernel (`rfl`) for an
arbitrary `O` that agrees with `latin1` on Latin-1.
-/

open Aeneas Aeneas.Std Result
open SudoersSpec.Syntax (Stream CharOracle)

namespace SudoRsProofs.Parser

/-- `O` agrees with `CharOracle.latin1` on `U+0000..U+00FF`. -/
def Latin1Agrees (O : CharOracle) : Prop :=
  ∀ c : Char, c.val < 256 →
    O.isAlphanumeric c = CharOracle.latin1.isAlphanumeric c ∧
    O.isUppercase c = CharOracle.latin1.isUppercase c ∧
    O.isNumeric c = CharOracle.latin1.isNumeric c ∧
    O.isControl c = CharOracle.latin1.isControl c ∧
    O.isWhitespace c = CharOracle.latin1.isWhitespace c

/-- `latin1` below `U+0100`, `O` above: equal to `O` when `O` agrees with `latin1`, and
computable by the kernel on Latin-1 inputs whatever `O` is. -/
def latin1Below (O : CharOracle) : CharOracle where
  isAlphanumeric c := if c.val < 256 then CharOracle.latin1.isAlphanumeric c else O.isAlphanumeric c
  isUppercase c := if c.val < 256 then CharOracle.latin1.isUppercase c else O.isUppercase c
  isNumeric c := if c.val < 256 then CharOracle.latin1.isNumeric c else O.isNumeric c
  isControl c := if c.val < 256 then CharOracle.latin1.isControl c else O.isControl c
  isWhitespace c := if c.val < 256 then CharOracle.latin1.isWhitespace c else O.isWhitespace c

theorem latin1Below_eq {O : CharOracle} (h : Latin1Agrees O) : latin1Below O = O := by
  rcases O with ⟨a, u, n, k, w⟩
  simp only [latin1Below, CharOracle.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> funext c <;> split <;> simp_all [Latin1Agrees]

/-- The input `web1, !db` as a slice. -/
def hostsSrc : Slice Char :=
  Slice.from "web1, !db".toList (by
    have : "web1, !db".toList.length = 9 := by decide
    rw [this]; scalar_tac)

/-- **Non-vacuity of `host_list_refines`.** On `web1, !db` the extracted `host_list` returns
`Ok` with the host list `[allow (only "web1"), forbid (only "db")]` and a cursor at the end of
the input (line 1, column 10), for every oracle `O` that the opaque predicates agree with and
that agrees with `rustc` on Latin-1. -/
theorem host_list_example {O : CharOracle} (hO : UnicodeOracle O) (hL : Latin1Agrees O) :
    ∃ v s', sudo_rs.sudoers.ast.host_list ⟨hostsSrc, 0#usize, 1#usize, 1#usize⟩ = ok (.Ok v, s') ∧
      absHostList v = [.allow (.only "web1"), .forbid (.only "db")] ∧
      absStream s' = ⟨[], 1, 10⟩ := by
  have hlen : hostsSrc.val.length < Usize.max := by
    have : hostsSrc.val.length = 9 := by simp [hostsSrc]
    rw [this]; scalar_tac
  obtain ⟨r, s', e, hr, -, a⟩ := host_list_refines_text hO hostsSrc hlen
  rw [← latin1Below_eq hL] at hr a
  have hrun : (SudoersSpec.Syntax.specListHostname
      (latin1Below O) SudoersSpec.Syntax.Descriptions.release).run (Stream.new hostsSrc.val) =
      (.ok [.allow (.only "web1"), .forbid (.only "db")], ⟨[], 1, 10⟩) := by
    simp only [hostsSrc, Slice.from_val]
    rfl
  rw [hrun] at hr a
  rcases r with v | st
  · exact ⟨v, s', e, hr, a⟩
  · simp [ResultRel] at hr

/-- A `UserFriendly` instance for host lists (the generic theorem takes any instance). -/
def hostListUF :
    sudo_rs.sudoers.ast_names.UserFriendly
      (alloc.vec.Vec (sudo_rs.sudoers.ast.Qualified (sudo_rs.sudoers.tokens.Meta
        sudo_rs.sudoers.tokens.Hostname))) where
  DESCRIPTION := ok (toStr "host name")

/-- The input `web1, !db⏎ALL⏎`. -/
def linesSrc : Slice Char :=
  Slice.from "web1, !db\nALL\n".toList (by
    have : "web1, !db\nALL\n".toList.length = 14 := by decide
    rw [this]; scalar_tac)

/-- **Non-vacuity of `parse_lines_refines`**, with host lists as the items: two lines, two
results, the cursor at line 3, column 1. -/
theorem parse_lines_example {O : CharOracle} (hO : UnicodeOracle O) (hL : Latin1Agrees O) :
    ∃ v s', sudo_rs.sudoers.basic_parser.parse_lines specListHostnameInst hostListUF
        ⟨linesSrc, 0#usize, 1#usize, 1#usize⟩ = ok (v, s') ∧
      List.Forall₂ (ResultRel absHostList) v.val
        [.ok [.allow (.only "web1"), .forbid (.only "db")], .ok [.allow .all]] ∧
      absStream s' = ⟨[], 3, 1⟩ := by
  have hlen : 2 * linesSrc.val.length ≤ Usize.max := by
    have : linesSrc.val.length = 14 := by simp [linesSrc]
    rw [this]; scalar_tac
  have hD : DescRel hostListUF SudoersSpec.Syntax.Descriptions.release.hostname :=
    ⟨_, rfl, toStr_val _ _⟩
  obtain ⟨v, s', items, e, hrun, hF, -⟩ :=
    parse_lines_refines_text (spec_list_hostname_refines hO _ rfl) hD linesSrc hlen
  rw [← latin1Below_eq hL] at hrun
  have hval : (SudoersSpec.Syntax.parseLines SudoersSpec.Syntax.Descriptions.release.hostname
      (SudoersSpec.Syntax.specListHostname (latin1Below O)
        SudoersSpec.Syntax.Descriptions.release)).run (Stream.new linesSrc.val) =
      (.ok [.ok [.allow (.only "web1"), .forbid (.only "db")], .ok [.allow .all]],
        ⟨[], 3, 1⟩) := by
    simp only [linesSrc, Slice.from_val]
    rfl
  rw [hval] at hrun
  simp only [Prod.mk.injEq, Except.ok.injEq] at hrun
  obtain ⟨rfl, ha⟩ := hrun
  exact ⟨v, s', e, hF, ha.symm⟩

/-- An oracle-free instantiation of the generic line theorem: one syntax item, one newline. -/
theorem parse_lines_syntax_example :
    let src := Slice.from ['x', '\n'] (by simp; scalar_tac)
    let parser : sudo_rs.sudoers.basic_parser.Parse Unit :=
      ⟨sudo_rs.sudoers.basic_parser.try_syntax 'x'⟩
    let names : sudo_rs.sudoers.ast_names.UserFriendly Unit := ⟨ok (toStr "x")⟩
    ∃ v s', sudo_rs.sudoers.basic_parser.parse_lines parser names
        ⟨src, 0#usize, 1#usize, 1#usize⟩ = ok (v, s') ∧
      List.Forall₂ (ResultRel (id : Unit → Unit)) v.val [.ok ()] ∧
      absStream s' = ⟨[], 2, 1⟩ := by
  dsimp only
  have hp : ParseRefines ⟨sudo_rs.sudoers.basic_parser.try_syntax 'x'⟩ id
      (SudoersSpec.Syntax.trySyntax 'x') := ⟨fun _ h => try_syntax_refines h 'x'⟩
  have hd : DescRel (T := Unit) ⟨ok (toStr "x")⟩ "x" := ⟨_, rfl, toStr_val _ _⟩
  obtain ⟨v, s', items, e, hr, hF, -⟩ :=
    parse_lines_refines_text hp hd (Slice.from ['x', '\n'] (by simp; scalar_tac))
      (by simp; scalar_tac)
  have he : (SudoersSpec.Syntax.parseLines "x" (SudoersSpec.Syntax.trySyntax 'x')).run
      (Stream.new ['x', '\n']) = (.ok [(.ok ())], ⟨[], 2, 1⟩) := rfl
  rw [Slice.from_val, he] at hr
  simp only [Prod.mk.injEq, Except.ok.injEq] at hr
  obtain ⟨rfl, hs⟩ := hr
  exact ⟨v, s', e, hF, hs.symm⟩

end SudoRsProofs.Parser
