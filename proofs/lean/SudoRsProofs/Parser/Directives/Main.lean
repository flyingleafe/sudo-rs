import SudoRsProofs.Parser.Directives.Sudo
import SudoRsProofs.Parser.Directives.Defs
import SudoRsProofs.Parser.Directives.Include
import SudoRsProofs.Parser.Directives.IncludeTokens
import SudoRsProofs.Parser.DefaultsParse.Main
import SudoRsProofs.Parser.PermissionLines.Refinement

/-! The stable extracted parser. The default build has no remote sudoers production:
`parse_remote` is the checked unknown-directive branch. Include paths are parsed as strings;
reading files and traversing include directories belong to `Analysis`, not this refinement. -/

open Aeneas Aeneas.Std Result SudoersSpec
open sudo_rs

namespace SudoRsProofs.Parser

private theorem directive_leaves {A : GlobAbs} {O : Syntax.Oracles} (hO : P2Oracle A O) :
    DirectiveLeaves A O where
  users _ hs hq := expect_user_defs_refines hO.chars hs hq
  hosts _ hs := expect_host_defs_refines hO.chars.unicode hs
  commands _ hs := expect_command_defs_refines hO hs
  settings _ hs := expect_nonterminal_refines
    (settingsModifier_vec_refines hO.chars) (desc_vec settingsModifier_description) hs

private theorem sudo_leaves {A : GlobAbs} {O : Syntax.Oracles} (hO : P2Oracle A O) :
    SudoLeaves A O where
  identifier := identifier_refines hO.chars
  users := spec_list_user_refines hO.chars
  userDomain _ _ _ h := user_list_domain_of_tokens
    (fun _ _ _ h => username_token_value_bound h)
    (fun _ _ _ h => meta_username_only_value_bound h) h
  permissions _ hs hq := permissions_refines hO hs hq
  includes _ hs := parse_include_refines A hO.chars hs
  directives := directive_leaves hO

/-- P3 item refinement, for the actual `Parse Sudo` instance of the stable feature set. -/
theorem sudo_refines {A : GlobAbs} {O : Syntax.Oracles} (hO : P2Oracle A O) :
    ParseRefinesOn QuoteRoom sudoParseInst (Analysis.absSudo A) (Syntax.sudo O .release) :=
  sudo_refines_of_parts hO (sudo_leaves hO)

/-- P3 file refinement: actual extraction `ok`, related accepted items and diagnostics,
no returned `Reject`, and the reference final stream. `parse_sudoers` itself discards the
final Rust cursor, so the theorem also states the equation for `parse_sudo_lines`. -/
theorem parse_sudoers_refines {A : GlobAbs} {O : Syntax.Oracles} (hO : P2Oracle A O)
    (src : Slice Char) (room : 1 + 2 * src.val.length ≤ Usize.max) :
    ∃ raw stop items,
      sudoers.parse_sudoers src = ok raw ∧
      sudoers.ast.parse_sudo_lines ⟨src, 0#usize, 1#usize, 1#usize⟩ = ok (raw, stop) ∧
      Syntax.parseSudoers O src.val = .ok items ∧
      (Syntax.parseLines Syntax.Descriptions.release.sudo (Syntax.sudo O .release)).run
        (Syntax.Stream.new src.val) = (.ok items, absStream stop) ∧
      List.Forall₂ (ResultRel (Analysis.absSudo A)) raw.val items ∧
      StreamOK stop ∧ ∀ r ∈ raw.val, r ≠ .Err .Reject :=
  parse_sudoers_refines_of_item (sudo_refines hO) src room

end SudoRsProofs.Parser
