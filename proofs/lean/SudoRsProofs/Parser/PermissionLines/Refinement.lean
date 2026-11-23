import SudoRsProofs.Parser.PermissionLines.UserRefinement
import SudoRsProofs.Parser.PermissionLines.Tags
import SudoRsProofs.Parser.PermissionLines.Commands
import SudoRsProofs.Parser.PermissionLines.Tuples
import SudoRsProofs.Parser.AliasName
import SudoRsProofs.Parser.Command

/-!
# Permission-line parser refinement

The named entries use the release descriptions. `Refines` covers the returned AST or status
and the final cursor together, with no rollback assumption for a rejected parser. The only
extra cursor condition, `QuoteRoom`, accounts for re-escaping a quoted user in a temporary
stream. It holds at an original input's start from the bound in the text-level statements and
persists until each named entry by `quoteRoom_stable`.
-/

open Aeneas Aeneas.Std SudoersSpec

namespace SudoRsProofs.Parser

private abbrev D := Syntax.Descriptions.release

variable {O : Syntax.Oracles} {A : GlobAbs}

theorem meta_or_tag_refines_release (hO : P2CharOracle O.char) :
    ParseRefines sudo_rs.sudoers.ast.MetaOrTag.Insts.Sudo_rsSudoersBasic_parserParse
      (absMeta absModifier) (Syntax.metaOrTag O D) :=
  meta_or_tag_refines O alias_name_parse_refines (chdir_parse_refines hO)
    (string_parameter_parse_refines hO)

theorem command_spec_refines_release (hO : P2Oracle A O) :
    ParseRefines sudo_rs.sudoers.ast.CommandSpec.Insts.Sudo_rsSudoersBasic_parserParse
      (absCommandSpec (absCommand A)) (Syntax.commandSpec O D) :=
  command_spec_refines (meta_or_tag_refines_release hO.chars) (meta_command_parse_refines_at hO)
    command_description .tooManyTags

theorem runas_command_refines (hO : P2Oracle A O) :
    ParseRefinesOn QuoteRoom runasCommandInst (absRunasCommand A) (Syntax.runasCommand O D) :=
  runas_command_refines_of_parts (run_as_refines hO.chars) (command_spec_refines_release hO)

theorem hosts_runas_commands_refines (hO : P2Oracle A O) :
    ParseRefinesOn QuoteRoom hostsRunasCommandsInst (absSeg A) (Syntax.hostsRunasCommands O D) :=
  hosts_runas_commands_refines_of_parts hO.chars.unicode (runas_command_refines hO)

theorem permissions_refines (hO : P2Oracle A O) {s : CS} (hs : StreamOK s)
    (hq : QuoteRoom (absStream s)) :
    Refines (absVec (absSeg A)) (sudo_rs.sudoers.ast.permissions s)
      ((Syntax.expectNonterminal D.hostsRunasCommands (Syntax.permissions O D)).run (absStream s)) :=
  permissions_refines_of_segments (hosts_runas_commands_refines hO) hs hq

/-- P2 permissions entry, on an original input at position `(1,1)`. -/
theorem permissions_refines_text (hO : P2Oracle A O) (src : Slice Char)
    (hlen : 1 + 2 * src.val.length ≤ Usize.max) :
    Refines (absVec (absSeg A)) (sudo_rs.sudoers.ast.permissions ⟨src, 0#usize, 1#usize, 1#usize⟩)
      ((Syntax.expectNonterminal D.hostsRunasCommands (Syntax.permissions O D)).run
        (Syntax.Stream.new src.val)) :=
  permissions_refines hO (StreamOK.initial src (by omega)) (QuoteRoom.initial src hlen)

end SudoRsProofs.Parser
