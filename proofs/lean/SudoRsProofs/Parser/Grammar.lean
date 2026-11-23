import SudoRsProofs.Parser.Ast
import SudoRsProofs.Parser.Lines
import SudoersSpec.Grammar.RoundTrip
import SudoersSpec.Syntax.Recovery

/-!
# From extracted parsers to their grammars

The reference parser is the common middle term: its implementation refinement and its grammar
proofs compose without a second abstraction of input, output, positions or remainders.
-/

open Aeneas Aeneas.Std Result
open SudoersSpec (Hostname SpecList)
open SudoersSpec.Syntax (Stream Parsed CharOracle Descriptions)
open SudoersSpec.Grammar (HostListG)

namespace SudoRsProofs.Parser

/-- A grammar written on reference streams can constrain a successful Rust parser's remainder
without having to construct an extracted cursor or guess a concrete AST representative. -/
theorem Refines.success_iff {f : T → α} {x : Result (RParsed T × CS)} {out : Parsed α × Stream}
    (h : Refines f x out) (a : α) (post : Stream → Prop) :
    (∃ raw stop, x = ok (.Ok raw, stop) ∧ f raw = a ∧ post (absStream stop)) ↔
      out.1 = .ok a ∧ post out.2 := by
  obtain ⟨r, stop, rfl, hr, _, hs⟩ := h
  rcases out with ⟨result, final⟩
  change absStream stop = final at hs
  subst final
  cases r <;> cases result <;> simp_all [ResultRel]

/-- An extracted host list consumes exactly the grammar-derived prefix, returns its value,
and leaves precisely the specified suffix. Invalid starts and inadmissible followers are
not silently accepted by this statement: `HostListG` checks the right context. -/
theorem host_list_grammar_iff {O : CharOracle} (hO : UnicodeOracle O) {s : CS} (hs : StreamOK s)
    {consumed rest : List Char} (splitInput : (absStream s).rest = consumed ++ rest)
    (hosts : SpecList Hostname) :
    (∃ raw stop, sudo_rs.sudoers.ast.host_list s = ok (.Ok raw, stop) ∧
      absHostList raw = hosts ∧ (absStream stop).rest = rest) ↔ HostListG O consumed hosts rest := by
  have h := host_list_refines hO Descriptions.release rfl hs
  rw [h.success_iff hosts (fun t => t.rest = rest)]
  rw [← SudoersSpec.Grammar.specListHostname_run_ok_iff O Descriptions.release splitInput]
  cases (SudoersSpec.Syntax.specListHostname O Descriptions.release).run (absStream s) with
  | mk r t => simp

/-- PT5 transferred to the extracted Rust. The printer and the implementation need not
represent names, aliases or position counters by the same data structures. -/
theorem host_list_printed {O : CharOracle} (hO : UnicodeOracle O) (laws : SudoersSpec.Grammar.HostOracle O)
    {hosts : SpecList Hostname} (printable : SudoersSpec.Grammar.Printable O hosts)
    {rest : List Char} (follow : SudoersSpec.Grammar.PrintFollow O rest) {s : CS} (hs : StreamOK s)
    (text : (absStream s).rest = SudoersSpec.Grammar.printHostList hosts ++ rest) :
    ∃ raw stop, sudo_rs.sudoers.ast.host_list s = ok (.Ok raw, stop) ∧
      absHostList raw = hosts ∧ (absStream stop).rest = rest :=
  (host_list_grammar_iff hO hs text hosts).mpr (SudoersSpec.Grammar.print_derives laws printable follow)

/-- PT7 for the actual generic Rust line driver: for any refining item production, all
reported items are related to exactly the reference recovery trace and the driver reaches the
end of the input. This does not assume that the `Sudo` production has already been refined. -/
theorem parse_lines_recovery {P : sudo_rs.sudoers.basic_parser.Parse T} {f : T → α}
    {p : SudoersSpec.Syntax.Parser α} {UF : sudo_rs.sudoers.ast_names.UserFriendly T} {d : String}
    (hP : ParseRefines P f p) (hD : DescRel UF d) (src : Slice Char)
    (hlen : 2 * src.val.length ≤ Usize.max) :
    ∃ v stop rs, sudo_rs.sudoers.basic_parser.parse_lines P UF ⟨src, 0#usize, 1#usize, 1#usize⟩ =
      ok (v, stop) ∧ SudoersSpec.Syntax.Recovery.Trace d p (Stream.new src.val) rs (absStream stop) ∧
      List.Forall₂ (ResultRel f) v.val rs ∧ StreamOK stop ∧
      absStream stop = (Stream.new src.val).advance src.val.length := by
  obtain ⟨v, stop, rs, run, reference, rel, wf⟩ := parse_lines_refines_text hP hD src hlen
  refine ⟨v, stop, rs, run, (SudoersSpec.Syntax.Recovery.parseLines_iff_trace ..).mp reference, rel, wf, ?_⟩
  have endPos := SudoersSpec.Syntax.Recovery.parseLines_end d p (Stream.new src.val)
  rwa [reference] at endPos

end SudoRsProofs.Parser
