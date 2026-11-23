import SudoersSpec.Analysis.Collect
import SudoersSpec.Examples

/-! Witnesses for the include-free text specification. These are synthetic
accounts and a literal path, with no calls to the filesystem, NSS, PAM or an installed sudo.
They exercise both Defaults passes on the same field and distinguish denial from absence of
an include-free model result. They are not tests of those external systems. -/

namespace SudoersSpec.Analysis.Examples

private def env : Syntax.Oracles :=
  ⟨Syntax.CharOracle.latin1, ⟨fun _ => .err⟩, ⟨fun _ => none⟩, ⟨id, id⟩⟩

private def db : Oracle String String := { SudoersSpec.Examples.named with globMatches := (· == ·) }

private def request (name : String) : Request String String :=
  ⟨name, "studio", "worker", "worker", "/tools/report", ["summary"]⟩

-- The command-specific change comes *first* in the text but is applied *after* the generic change.
private def source := "Defaults!/tools/report passwd_tries=2\nDefaults passwd_tries=5\nreader studio = (worker) /tools/report summary\n"

private def observation : Option (Authorization Settings.StrSet) → Option (Option Nat)
  | none => none
  | some .forbidden => some none
  | some (.allowed auth _) => some (some auth.allowedAttempts)

-- Executable test of the entire positive path, not a kernel proof of a concrete evaluation.
#guard observation (authorizationOfText env db source.toList (request "reader")) == some (some 2)

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem unlisted_reader_denied : observation (authorizationOfText env db source.toList (request "observer")) =
    some none := by decide

set_option maxRecDepth 8000 in
theorem include_requires_snapshot : observation (authorizationOfText env db "@include /fixture/rules\n".toList
    (request "reader")) = none := by decide

end SudoersSpec.Analysis.Examples
