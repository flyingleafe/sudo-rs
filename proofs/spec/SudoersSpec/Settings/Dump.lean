import SudoersSpec.Settings.Model

/-!
# Rendering of settings, as `Settings::dump_fields`

Mirrors the test-only observer `Settings::dump_fields` and `DumpValue` of
`src/defaults/settings_dsl.rs` (see `proofs/parser/DUMP.md`): `true`/`false`, decimal integers,
enum variant names, quoted strings, `none`/`(some "..")`, and sets as `[..]` of quoted strings in
ascending order. Used by the tests and by differential comparisons with the Rust code.
-/

namespace SudoersSpec.Settings

/-- `dump_quoted`: printable ASCII other than `"` and `\` verbatim, `\"`, `\\`, and `\u{h}`
(lowercase hexadecimal) for every other code point. -/
def dumpQuoted (s : String) : String :=
  let esc (c : Char) : String :=
    if c = '"' then "\\\""
    else if c = '\\' then "\\\\"
    else if 32 ≤ c.toNat ∧ c.toNat ≤ 126 then c.toString
    else "\\u{" ++ String.ofList (Nat.toDigits 16 c.toNat) ++ "}"
  "\"" ++ String.join (s.toList.map esc) ++ "\""

def dumpBool (b : Bool) : String := if b then "true" else "false"

def dumpOpt : Option String → String
  | none => "none"
  | some s => "(some " ++ dumpQuoted s ++ ")"

/-- A set: its elements, sorted, quoted, separated by spaces. -/
def dumpSet (s : StrSet) : String :=
  "[" ++ " ".intercalate ((s.mergeSort fun a b => decide (a ≤ b)).map dumpQuoted) ++ "]"

def Lecture.dump : Lecture → String
  | .always => "always" | .once => "once" | .never => "never"

def Verifypw.dump : Verifypw → String
  | .all => "all" | .always => "always" | .any => "any" | .never => "never"

def dumpTimestampType : TimestampType → String
  | .tty => "tty" | .ppid => "ppid"

/-- `Settings::dump_fields`: every field in declaration order. -/
def Settings.dumpFields (s : Settings) : List (String × String) :=
  [("always_query_group_plugin", dumpBool s.always_query_group_plugin),
   ("always_set_home", dumpBool s.always_set_home),
   ("env_reset", dumpBool s.env_reset),
   ("fqdn", dumpBool s.fqdn),
   ("ignore_dot", dumpBool s.ignore_dot),
   ("lecture", s.lecture.dump),
   ("mailerpath", dumpOpt s.mailerpath),
   ("mail_badpass", dumpBool s.mail_badpass),
   ("match_group_by_gid", dumpBool s.match_group_by_gid),
   ("use_pty", dumpBool s.use_pty),
   ("visiblepw", dumpBool s.visiblepw),
   ("pwfeedback", dumpBool s.pwfeedback),
   ("rootpw", dumpBool s.rootpw),
   ("targetpw", dumpBool s.targetpw),
   ("noexec", dumpBool s.noexec),
   ("noninteractive_auth", dumpBool s.noninteractive_auth),
   ("log_allowed", dumpBool s.log_allowed),
   ("log_denied", dumpBool s.log_denied),
   ("insults", dumpBool s.insults),
   ("setenv", dumpBool s.setenv),
   ("runcwd", dumpOpt s.runcwd),
   ("apparmor_profile", dumpOpt s.apparmor_profile),
   ("umask", toString s.umask),
   ("umask_override", dumpBool s.umask_override),
   ("passwd_tries", toString s.passwd_tries),
   ("secure_path", dumpOpt s.secure_path),
   ("verifypw", s.verifypw.dump),
   ("passwd_timeout", toString s.passwd_timeout),
   ("timestamp_timeout", toString s.timestamp_timeout),
   ("timestamp_type", dumpTimestampType s.timestamp_type),
   ("editor", dumpQuoted s.editor),
   ("env_editor", dumpBool s.env_editor),
   ("env_keep", dumpSet s.env_keep),
   ("env_check", dumpSet s.env_check),
   ("env_delete", dumpSet s.env_delete)]

/-- The rendered value of the field called `name`. -/
def Settings.dumpField (s : Settings) (name : String) : String :=
  match s.dumpFields.find? (·.1 == name) with
  | some (_, v) => v
  | none => ""

/-- A modifier, shown by its effect on the defaults: `name=value` of the field it writes, after
applying it to `Settings.default`; `none` for no modifier. -/
def showEffect : Option SettingsModifier → String
  | none => "none"
  | some m => m.setting.name ++ "=" ++ (m.apply Settings.default).dumpField m.setting.name

end SudoersSpec.Settings
