import SudoersSpec.Settings.Dump

/-!
# Tests of the settings model

* `example … := by decide` / `rfl`: kernel-checked; the values the Rust unit test
  `defaults::test::check` (`src/defaults/mod.rs`) asserts, step by step.
* `#guard` (compiled evaluation): the expected texts were printed by the Rust code at
  `ad41ddd4` (a scratch test, not committed, over `Settings::default().dump_fields()`, `negate`,
  `set`, `check_integer`, `check_text`, `build_list`): every setting's default, negation and kind,
  and every checker on the inputs of the old-against-new tests of `src/defaults/legacy.rs`
  (`INTEGER_INPUTS`, `TEXT_INPUTS`, `LIST_INPUTS` with the three modes). A modifier is shown by
  its effect on the defaults (`showEffect`). A case covers only its input.
-/

namespace SudoersSpec.Settings.Tests

open SudoersSpec.Settings

/-! ## `defaults::test::check` -/

/-- Apply a modifier the test unwraps. -/
def step (s : Settings) : Option SettingsModifier → Settings
  | none => s
  | some m => m.apply s

example : Settings.default.always_query_group_plugin = false := rfl
example : Settings.default.always_set_home = false := rfl
example : Settings.default.env_reset = true := rfl
example : Settings.default.mail_badpass = true := rfl
example : Settings.default.match_group_by_gid = false := rfl
example : Settings.default.use_pty = true := rfl
example : Settings.default.visiblepw = false := rfl
example : Settings.default.env_editor = true := rfl
example : Settings.default.passwd_tries = 3 := rfl
example : Settings.default.secure_path = none := rfl
example : StrSet.Equiv Settings.default.env_check
    ["COLORTERM", "LANG", "LANGUAGE", "LC_*", "LINGUAS", "TERM", "TZ"] := fun _ => Iff.rfl
example : Settings.default.verifypw = .all := rfl

/-- After `!env_check`, `!env_reset`, `!secure_path`, `!verifypw`. -/
def negated : Settings :=
  [negate "env_check", negate "env_reset", negate "secure_path", negate "verifypw"].foldl step
    Settings.default

example : (negate "env_check").isSome ∧ (negate "env_reset").isSome ∧
    (negate "secure_path").isSome ∧ (negate "verifypw").isSome := by decide
example : negated.always_query_group_plugin = false ∧ negated.always_set_home = false ∧
    negated.env_reset = false ∧ negated.mail_badpass = true ∧
    negated.match_group_by_gid = false ∧ negated.use_pty = true ∧ negated.visiblepw = false ∧
    negated.env_editor = true ∧ negated.passwd_tries = 3 ∧ negated.secure_path = none ∧
    negated.env_check = [] ∧ negated.verifypw = .never := by decide

example : set "lecture" = some (.Text .lecture) := by decide
example : (step negated (checkText .lecture "always")).lecture = .always := by decide
example : (step negated (checkText .lecture "once")).lecture = .once := by decide
example : (step negated (checkText .lecture "never")).lecture = .never := by decide
example : (step (step negated (checkText .lecture "never")) (negate "lecture")).lecture =
    .never := by decide

/-- Then `env_reset`, `secure_path=/bin`, `passwd_tries=5`, `verifypw=any`,
`timestamp_timeout=25.25`. -/
def assigned : Settings :=
  [some (.env_reset true), checkText .secure_path "/bin", checkInteger .passwd_tries "5",
    checkText .verifypw "any", checkInteger .timestamp_timeout "25.25"].foldl step
    (step negated (checkText .lecture "never"))

example : set "env_reset" = some (.Flag (.env_reset true)) := by decide
example : set "secure_path" = some (.Text .secure_path) := by decide
example : set "passwd_tries" = some (.Integer .passwd_tries) := by decide
example : set "verifypw" = some (.Text .verifypw) := by decide
example : set "timestamp_timeout" = some (.Integer .timestamp_timeout) := by decide
example : assigned.always_query_group_plugin = false ∧ assigned.always_set_home = false ∧
    assigned.env_reset = true ∧ assigned.mail_badpass = true ∧
    assigned.match_group_by_gid = false ∧ assigned.use_pty = true ∧
    assigned.visiblepw = false ∧ assigned.env_editor = true ∧ assigned.passwd_tries = 5 ∧
    assigned.timestamp_timeout = 25 * 60 + 60 / 4 ∧ assigned.secure_path = some "/bin" ∧
    assigned.env_check = [] ∧ assigned.verifypw = .any := by decide
example : set "notanoption" = none := by decide
example : checkInteger .timestamp_timeout "notanoption" = none := by decide

/-! ## Panics of `fractional_minutes` -/

example : fractionalMinutesRun "1.00000000000000000000" = .panic := by decide
example : fractionalMinutesRun "9999999999999999999.5" = .panic := by decide
example : fractionalMinutesRun "99999999999999999999.5" = .ok none := by decide
example : fractionalMinutesRun "25.25" = .ok (some 1515) := by decide

/-! ## Against the Rust code -/

/-- `INTEGER_INPUTS` of `src/defaults/legacy.rs`. -/
def integerInputs : List String := [
  "", "0", "00", "000", "1", "3", "7", "8", "10", "999", "1000", "1001", "4294967295",
  "4294967296", "18446744073709551615", "18446744073709551616", "99999999999999999999", "-1",
  "-0", "+5", "+0", "0x10", "0o22", "0b1", "1e3", "abc", "A", " 1", "1 ", "022", "0022", "0077",
  "0777", "0778", "0779", "08", "018", "07777", "077777", "0177777", "037777777777",
  "040000000000", "0+7", "0-7", "0 7", "1.5", "25.25", ".5", "5.", "1.", ".", "..", "1.2.3",
  "0.0", "0.5", "1.05", "+1.5", "1.+5", "-1.5", "1.-5", "0.0000000000000001",
  "9999999999.9999999", "99999999999999999", "307445734561825860", "307445734561825861",
  "1.00000000000000000", "a.5", "1.a", "\u00e9", "\u00e9.5", "1.\u00e9", "0\u00e9", "\u00e90",
  "0\u00e9.5", "\u0661", "0.\u0661"]

/-- `TEXT_INPUTS` of `src/defaults/legacy.rs`. -/
def textInputs : List String := [
  "", "always", "once", "never", "all", "any", "tty", "ppid", "sometimes", "kernel", "Always",
  "NEVER", " never", "never ", "None", "none", "/bin", "/usr/bin:/bin", "*", "a b", "\"x\"",
  "\u00e9"]

/-- `LIST_INPUTS` of `src/defaults/legacy.rs` under each mode. -/
def listCases : List (ListMode × List String) :=
  [ListMode.Set, .Add, .Del].flatMap fun m =>
    [[], ["PATH"], ["MOVED"], ["COLORS", "FOO", "BAR=baz"], ["PATH", "PATH"],
      ["LC_*", "XYZZY", "IFS"]].map fun l => (m, l)

def showKind : Option SettingKind → String
  | none => "none"
  | some (.Flag m) => "flag " ++ showEffect (some m)
  | some (.Integer _) => "integer"
  | some (.Text _) => "text"
  | some (.List _) => "list"

/-- The Rust `dump_quoted` of every text input (from the `editor` results). -/
def quotedTextInputs : List String := [
  "\"\"", "\"always\"", "\"once\"", "\"never\"", "\"all\"", "\"any\"", "\"tty\"", "\"ppid\"",
  "\"sometimes\"", "\"kernel\"", "\"Always\"", "\"NEVER\"", "\" never\"", "\"never \"",
  "\"None\"", "\"none\"", "\"/bin\"", "\"/usr/bin:/bin\"", "\"*\"", "\"a b\"", "\"\\\"x\\\"\"",
  "\"\\u{e9}\""]

/-- The values of `passwd_timeout` and of `timestamp_timeout` (identical) on every integer
input, `none` for a rejected one. -/
def timeoutValues : List String := [
  "none", "0", "0", "0", "60", "180", "420", "480", "600", "59940", "60000", "60060",
  "257698037700", "257698037760", "none", "none", "none", "none", "none", "300", "0", "none",
  "none", "none", "none", "none", "none", "none", "none", "1320", "1320", "4620", "46620", "46680",
  "46740", "480", "1080", "466620", "4666620", "10666620", "2266666666620", "2400000000000",
  "none", "none", "none", "90", "1515", "none", "none", "none", "none", "none", "none", "0", "30",
  "63", "90", "63", "none", "none", "0", "599999999999", "5999999999999999940",
  "18446744073709551600", "none", "60", "none", "none", "none", "none", "none", "none", "none",
  "none", "none", "none"]

def prefixed (name : String) (v : String) : String :=
  if v = "none" then v else name ++ "=" ++ v

#guard Settings.default.dumpFields == [
    ("always_query_group_plugin", "false"),
    ("always_set_home", "false"),
    ("env_reset", "true"),
    ("fqdn", "false"),
    ("ignore_dot", "true"),
    ("lecture", "never"),
    ("mailerpath", "none"),
    ("mail_badpass", "true"),
    ("match_group_by_gid", "false"),
    ("use_pty", "true"),
    ("visiblepw", "false"),
    ("pwfeedback", "true"),
    ("rootpw", "false"),
    ("targetpw", "false"),
    ("noexec", "false"),
    ("noninteractive_auth", "false"),
    ("log_allowed", "true"),
    ("log_denied", "true"),
    ("insults", "false"),
    ("setenv", "false"),
    ("runcwd", "none"),
    ("apparmor_profile", "none"),
    ("umask", "18"),
    ("umask_override", "false"),
    ("passwd_tries", "3"),
    ("secure_path", "none"),
    ("verifypw", "all"),
    ("passwd_timeout", "300"),
    ("timestamp_timeout", "900"),
    ("timestamp_type", "tty"),
    ("editor", "\"/usr/bin/editor:/usr/bin/nano:/usr/bin/vi\""),
    ("env_editor", "true"),
    ("env_keep", "[\"COLORS\" \"DISPLAY\" \"HOSTNAME\" \"KRB5CCNAME\" \"LS_COLORS\" \"PATH\" \"PS1\" \"PS2\" \"XAUTHORITY\" \"XAUTHORIZATION\" \"XDG_CURRENT_DESKTOP\"]"),
    ("env_check", "[\"COLORTERM\" \"LANG\" \"LANGUAGE\" \"LC_*\" \"LINGUAS\" \"TERM\" \"TZ\"]"),
    ("env_delete", "[\"*=()*\" \"BASHOPTS\" \"BASH_ENV\" \"CDPATH\" \"ENV\" \"FPATH\" \"GLOBIGNORE\" \"HOSTALIASES\" \"IFS\" \"JAVA_TOOL_OPTIONS\" \"LD_*\" \"LOCALDOMAIN\" \"NLSPATH\" \"NULLCMD\" \"PATH_LOCALE\" \"PERL5DB\" \"PERL5LIB\" \"PERL5OPT\" \"PERLIO_DEBUG\" \"PERLLIB\" \"PS4\" \"PYTHONHOME\" \"PYTHONINSPECT\" \"PYTHONPATH\" \"PYTHONUSERBASE\" \"READNULLCMD\" \"RES_OPTIONS\" \"RUBYLIB\" \"RUBYOPT\" \"SHELLOPTS\" \"TERMCAP\" \"TERMINFO\" \"TERMINFO_DIRS\" \"TERMPATH\" \"TMPPREFIX\" \"ZDOTDIR\" \"_RLD*\"]")]

#guard (Setting.all.map fun s => showEffect (negate s.name)) == [
    "always_query_group_plugin=false", "always_set_home=false", "env_reset=false", "fqdn=false",
    "ignore_dot=false", "lecture=never", "mailerpath=none", "mail_badpass=false",
    "match_group_by_gid=false", "use_pty=false", "visiblepw=false", "pwfeedback=false",
    "rootpw=false", "targetpw=false", "noexec=false", "noninteractive_auth=false",
    "log_allowed=false", "log_denied=false", "insults=false", "setenv=false", "runcwd=none",
    "apparmor_profile=none", "umask=511", "umask_override=false", "none", "secure_path=none",
    "verifypw=never", "passwd_timeout=0", "timestamp_timeout=0", "none", "none", "env_editor=false",
    "env_keep=[]", "env_check=[]", "env_delete=[]"]

#guard (Setting.all.map fun s => showKind (set s.name)) == [
    "flag always_query_group_plugin=true", "flag always_set_home=true", "flag env_reset=true",
    "flag fqdn=true", "flag ignore_dot=true", "text", "text", "flag mail_badpass=true",
    "flag match_group_by_gid=true", "flag use_pty=true", "flag visiblepw=true",
    "flag pwfeedback=true", "flag rootpw=true", "flag targetpw=true", "flag noexec=true",
    "flag noninteractive_auth=true", "flag log_allowed=true", "flag log_denied=true",
    "flag insults=true", "flag setenv=true", "text", "text", "integer", "flag umask_override=true",
    "integer", "text", "text", "integer", "integer", "text", "text", "flag env_editor=true", "list",
    "list", "list"]

#guard (["", "notanoption", "Use_pty", "use_pty ", "!use_pty"].map fun n =>
    (showKind (set n), showEffect (negate n))) == [
    ("none", "none"), ("none", "none"), ("none", "none"), ("none", "none"), ("none", "none")]

#guard (textInputs.map fun t => showEffect (checkText .lecture t)) == [
    "none", "lecture=always", "lecture=once", "lecture=never", "none", "none", "none", "none",
    "none", "none", "none", "none", "none", "none", "none", "none", "none", "none", "none", "none",
    "none", "none"]

#guard (textInputs.map fun t => showEffect (checkText .verifypw t)) == [
    "none", "verifypw=always", "none", "verifypw=never", "verifypw=all", "verifypw=any", "none",
    "none", "none", "none", "none", "none", "none", "none", "none", "none", "none", "none", "none",
    "none", "none", "none"]

#guard (textInputs.map fun t => showEffect (checkText .timestamp_type t)) == [
    "none", "none", "none", "none", "none", "none", "timestamp_type=tty", "timestamp_type=ppid",
    "none", "none", "none", "none", "none", "none", "none", "none", "none", "none", "none", "none",
    "none", "none"]

#guard (textInputs.map fun t => showEffect (checkText .editor t)) ==
    quotedTextInputs.map ("editor=" ++ ·)

#guard [TextSetting.mailerpath, .runcwd, .apparmor_profile, .secure_path].all fun id =>
    let name := (match id with
      | .mailerpath => "mailerpath" | .runcwd => "runcwd"
      | .apparmor_profile => "apparmor_profile" | _ => "secure_path")
    (textInputs.map fun t => showEffect (checkText id t)) ==
      quotedTextInputs.map fun q => name ++ "=(some " ++ q ++ ")"

#guard (integerInputs.map fun t => showEffect (checkInteger .umask t)) == [
    "none", "none", "umask=0", "umask=0", "none", "none", "none", "none", "none", "none", "none",
    "none", "none", "none", "none", "none", "none", "none", "none", "none", "none", "none", "none",
    "none", "none", "none", "none", "none", "none", "umask=18", "umask=18", "umask=63", "umask=511",
    "none", "none", "none", "none", "umask=4095", "umask=32767", "umask=65535", "umask=4294967295",
    "none", "umask=7", "none", "none", "none", "none", "none", "none", "none", "none", "none",
    "none", "none", "none", "none", "none", "none", "none", "none", "none", "none", "none", "none",
    "none", "none", "none", "none", "none", "none", "none", "none", "none", "none", "none", "none"]

#guard (integerInputs.map fun t => showEffect (checkInteger .passwd_tries t)) == [
    "none", "passwd_tries=0", "passwd_tries=0", "passwd_tries=0", "passwd_tries=1",
    "passwd_tries=3", "passwd_tries=7", "passwd_tries=8", "passwd_tries=10", "passwd_tries=999",
    "passwd_tries=1000", "none", "none", "none", "none", "none", "none", "none", "none",
    "passwd_tries=5", "passwd_tries=0", "none", "none", "none", "none", "none", "none", "none",
    "none", "passwd_tries=22", "passwd_tries=22", "passwd_tries=77", "passwd_tries=777",
    "passwd_tries=778", "passwd_tries=779", "passwd_tries=8", "passwd_tries=18", "none", "none",
    "none", "none", "none", "none", "none", "none", "none", "none", "none", "none", "none", "none",
    "none", "none", "none", "none", "none", "none", "none", "none", "none", "none", "none", "none",
    "none", "none", "none", "none", "none", "none", "none", "none", "none", "none", "none", "none",
    "none"]

#guard (integerInputs.map fun t => showEffect (checkInteger .passwd_timeout t)) ==
    timeoutValues.map (prefixed "passwd_timeout")

#guard (integerInputs.map fun t => showEffect (checkInteger .timestamp_timeout t)) ==
    timeoutValues.map (prefixed "timestamp_timeout")

-- none of the integer inputs panics, and the panic-free value is the Rust one
#guard [IntegerSetting.umask, .passwd_tries, .passwd_timeout, .timestamp_timeout].all fun id =>
    integerInputs.all fun t => checkIntegerRun id t == .ok (checkInteger id t)

#guard (listCases.map fun (m, l) => showEffect (some (buildList .env_keep m l))) ==
  ["env_keep=[]",
   "env_keep=[\"PATH\"]",
   "env_keep=[\"MOVED\"]",
   "env_keep=[\"BAR=baz\" \"COLORS\" \"FOO\"]",
   "env_keep=[\"PATH\"]",
   "env_keep=[\"IFS\" \"LC_*\" \"XYZZY\"]",
   "env_keep=[\"COLORS\" \"DISPLAY\" \"HOSTNAME\" \"KRB5CCNAME\" \"LS_COLORS\" \"PATH\" \"PS1\" \"PS2\" \"XAUTHORITY\" \"XAUTHORIZATION\" \"XDG_CURRENT_DESKTOP\"]",
   "env_keep=[\"COLORS\" \"DISPLAY\" \"HOSTNAME\" \"KRB5CCNAME\" \"LS_COLORS\" \"PATH\" \"PS1\" \"PS2\" \"XAUTHORITY\" \"XAUTHORIZATION\" \"XDG_CURRENT_DESKTOP\"]",
   "env_keep=[\"COLORS\" \"DISPLAY\" \"HOSTNAME\" \"KRB5CCNAME\" \"LS_COLORS\" \"MOVED\" \"PATH\" \"PS1\" \"PS2\" \"XAUTHORITY\" \"XAUTHORIZATION\" \"XDG_CURRENT_DESKTOP\"]",
   "env_keep=[\"BAR=baz\" \"COLORS\" \"DISPLAY\" \"FOO\" \"HOSTNAME\" \"KRB5CCNAME\" \"LS_COLORS\" \"PATH\" \"PS1\" \"PS2\" \"XAUTHORITY\" \"XAUTHORIZATION\" \"XDG_CURRENT_DESKTOP\"]",
   "env_keep=[\"COLORS\" \"DISPLAY\" \"HOSTNAME\" \"KRB5CCNAME\" \"LS_COLORS\" \"PATH\" \"PS1\" \"PS2\" \"XAUTHORITY\" \"XAUTHORIZATION\" \"XDG_CURRENT_DESKTOP\"]",
   "env_keep=[\"COLORS\" \"DISPLAY\" \"HOSTNAME\" \"IFS\" \"KRB5CCNAME\" \"LC_*\" \"LS_COLORS\" \"PATH\" \"PS1\" \"PS2\" \"XAUTHORITY\" \"XAUTHORIZATION\" \"XDG_CURRENT_DESKTOP\" \"XYZZY\"]",
   "env_keep=[\"COLORS\" \"DISPLAY\" \"HOSTNAME\" \"KRB5CCNAME\" \"LS_COLORS\" \"PATH\" \"PS1\" \"PS2\" \"XAUTHORITY\" \"XAUTHORIZATION\" \"XDG_CURRENT_DESKTOP\"]",
   "env_keep=[\"COLORS\" \"DISPLAY\" \"HOSTNAME\" \"KRB5CCNAME\" \"LS_COLORS\" \"PS1\" \"PS2\" \"XAUTHORITY\" \"XAUTHORIZATION\" \"XDG_CURRENT_DESKTOP\"]",
   "env_keep=[\"COLORS\" \"DISPLAY\" \"HOSTNAME\" \"KRB5CCNAME\" \"LS_COLORS\" \"PATH\" \"PS1\" \"PS2\" \"XAUTHORITY\" \"XAUTHORIZATION\" \"XDG_CURRENT_DESKTOP\"]",
   "env_keep=[\"DISPLAY\" \"HOSTNAME\" \"KRB5CCNAME\" \"LS_COLORS\" \"PATH\" \"PS1\" \"PS2\" \"XAUTHORITY\" \"XAUTHORIZATION\" \"XDG_CURRENT_DESKTOP\"]",
   "env_keep=[\"COLORS\" \"DISPLAY\" \"HOSTNAME\" \"KRB5CCNAME\" \"LS_COLORS\" \"PS1\" \"PS2\" \"XAUTHORITY\" \"XAUTHORIZATION\" \"XDG_CURRENT_DESKTOP\"]",
   "env_keep=[\"COLORS\" \"DISPLAY\" \"HOSTNAME\" \"KRB5CCNAME\" \"LS_COLORS\" \"PATH\" \"PS1\" \"PS2\" \"XAUTHORITY\" \"XAUTHORIZATION\" \"XDG_CURRENT_DESKTOP\"]"]

#guard (listCases.map fun (m, l) => showEffect (some (buildList .env_check m l))) ==
  ["env_check=[]",
   "env_check=[\"PATH\"]",
   "env_check=[\"MOVED\"]",
   "env_check=[\"BAR=baz\" \"COLORS\" \"FOO\"]",
   "env_check=[\"PATH\"]",
   "env_check=[\"IFS\" \"LC_*\" \"XYZZY\"]",
   "env_check=[\"COLORTERM\" \"LANG\" \"LANGUAGE\" \"LC_*\" \"LINGUAS\" \"TERM\" \"TZ\"]",
   "env_check=[\"COLORTERM\" \"LANG\" \"LANGUAGE\" \"LC_*\" \"LINGUAS\" \"PATH\" \"TERM\" \"TZ\"]",
   "env_check=[\"COLORTERM\" \"LANG\" \"LANGUAGE\" \"LC_*\" \"LINGUAS\" \"MOVED\" \"TERM\" \"TZ\"]",
   "env_check=[\"BAR=baz\" \"COLORS\" \"COLORTERM\" \"FOO\" \"LANG\" \"LANGUAGE\" \"LC_*\" \"LINGUAS\" \"TERM\" \"TZ\"]",
   "env_check=[\"COLORTERM\" \"LANG\" \"LANGUAGE\" \"LC_*\" \"LINGUAS\" \"PATH\" \"TERM\" \"TZ\"]",
   "env_check=[\"COLORTERM\" \"IFS\" \"LANG\" \"LANGUAGE\" \"LC_*\" \"LINGUAS\" \"TERM\" \"TZ\" \"XYZZY\"]",
   "env_check=[\"COLORTERM\" \"LANG\" \"LANGUAGE\" \"LC_*\" \"LINGUAS\" \"TERM\" \"TZ\"]",
   "env_check=[\"COLORTERM\" \"LANG\" \"LANGUAGE\" \"LC_*\" \"LINGUAS\" \"TERM\" \"TZ\"]",
   "env_check=[\"COLORTERM\" \"LANG\" \"LANGUAGE\" \"LC_*\" \"LINGUAS\" \"TERM\" \"TZ\"]",
   "env_check=[\"COLORTERM\" \"LANG\" \"LANGUAGE\" \"LC_*\" \"LINGUAS\" \"TERM\" \"TZ\"]",
   "env_check=[\"COLORTERM\" \"LANG\" \"LANGUAGE\" \"LC_*\" \"LINGUAS\" \"TERM\" \"TZ\"]",
   "env_check=[\"COLORTERM\" \"LANG\" \"LANGUAGE\" \"LINGUAS\" \"TERM\" \"TZ\"]"]

/-- The rendering of the `env_delete` default with the given names added and removed. -/
def envDelete (added removed : List String) : String :=
  "env_delete=" ++ dumpSet
    ((Settings.default.env_delete ++ added).filter fun x => !removed.contains x)

#guard (listCases.map fun (m, l) => showEffect (some (buildList .env_delete m l))) ==
  ["env_delete=[]",
   "env_delete=[\"PATH\"]",
   "env_delete=[\"MOVED\"]",
   "env_delete=[\"BAR=baz\" \"COLORS\" \"FOO\"]",
   "env_delete=[\"PATH\"]",
   "env_delete=[\"IFS\" \"LC_*\" \"XYZZY\"]",
   "env_delete=[\"*=()*\" \"BASHOPTS\" \"BASH_ENV\" \"CDPATH\" \"ENV\" \"FPATH\" \"GLOBIGNORE\" \"HOSTALIASES\" \"IFS\" \"JAVA_TOOL_OPTIONS\" \"LD_*\" \"LOCALDOMAIN\" \"NLSPATH\" \"NULLCMD\" \"PATH_LOCALE\" \"PERL5DB\" \"PERL5LIB\" \"PERL5OPT\" \"PERLIO_DEBUG\" \"PERLLIB\" \"PS4\" \"PYTHONHOME\" \"PYTHONINSPECT\" \"PYTHONPATH\" \"PYTHONUSERBASE\" \"READNULLCMD\" \"RES_OPTIONS\" \"RUBYLIB\" \"RUBYOPT\" \"SHELLOPTS\" \"TERMCAP\" \"TERMINFO\" \"TERMINFO_DIRS\" \"TERMPATH\" \"TMPPREFIX\" \"ZDOTDIR\" \"_RLD*\"]",
   "env_delete=[\"*=()*\" \"BASHOPTS\" \"BASH_ENV\" \"CDPATH\" \"ENV\" \"FPATH\" \"GLOBIGNORE\" \"HOSTALIASES\" \"IFS\" \"JAVA_TOOL_OPTIONS\" \"LD_*\" \"LOCALDOMAIN\" \"NLSPATH\" \"NULLCMD\" \"PATH\" \"PATH_LOCALE\" \"PERL5DB\" \"PERL5LIB\" \"PERL5OPT\" \"PERLIO_DEBUG\" \"PERLLIB\" \"PS4\" \"PYTHONHOME\" \"PYTHONINSPECT\" \"PYTHONPATH\" \"PYTHONUSERBASE\" \"READNULLCMD\" \"RES_OPTIONS\" \"RUBYLIB\" \"RUBYOPT\" \"SHELLOPTS\" \"TERMCAP\" \"TERMINFO\" \"TERMINFO_DIRS\" \"TERMPATH\" \"TMPPREFIX\" \"ZDOTDIR\" \"_RLD*\"]",
   "env_delete=[\"*=()*\" \"BASHOPTS\" \"BASH_ENV\" \"CDPATH\" \"ENV\" \"FPATH\" \"GLOBIGNORE\" \"HOSTALIASES\" \"IFS\" \"JAVA_TOOL_OPTIONS\" \"LD_*\" \"LOCALDOMAIN\" \"MOVED\" \"NLSPATH\" \"NULLCMD\" \"PATH_LOCALE\" \"PERL5DB\" \"PERL5LIB\" \"PERL5OPT\" \"PERLIO_DEBUG\" \"PERLLIB\" \"PS4\" \"PYTHONHOME\" \"PYTHONINSPECT\" \"PYTHONPATH\" \"PYTHONUSERBASE\" \"READNULLCMD\" \"RES_OPTIONS\" \"RUBYLIB\" \"RUBYOPT\" \"SHELLOPTS\" \"TERMCAP\" \"TERMINFO\" \"TERMINFO_DIRS\" \"TERMPATH\" \"TMPPREFIX\" \"ZDOTDIR\" \"_RLD*\"]",
   "env_delete=[\"*=()*\" \"BAR=baz\" \"BASHOPTS\" \"BASH_ENV\" \"CDPATH\" \"COLORS\" \"ENV\" \"FOO\" \"FPATH\" \"GLOBIGNORE\" \"HOSTALIASES\" \"IFS\" \"JAVA_TOOL_OPTIONS\" \"LD_*\" \"LOCALDOMAIN\" \"NLSPATH\" \"NULLCMD\" \"PATH_LOCALE\" \"PERL5DB\" \"PERL5LIB\" \"PERL5OPT\" \"PERLIO_DEBUG\" \"PERLLIB\" \"PS4\" \"PYTHONHOME\" \"PYTHONINSPECT\" \"PYTHONPATH\" \"PYTHONUSERBASE\" \"READNULLCMD\" \"RES_OPTIONS\" \"RUBYLIB\" \"RUBYOPT\" \"SHELLOPTS\" \"TERMCAP\" \"TERMINFO\" \"TERMINFO_DIRS\" \"TERMPATH\" \"TMPPREFIX\" \"ZDOTDIR\" \"_RLD*\"]",
   "env_delete=[\"*=()*\" \"BASHOPTS\" \"BASH_ENV\" \"CDPATH\" \"ENV\" \"FPATH\" \"GLOBIGNORE\" \"HOSTALIASES\" \"IFS\" \"JAVA_TOOL_OPTIONS\" \"LD_*\" \"LOCALDOMAIN\" \"NLSPATH\" \"NULLCMD\" \"PATH\" \"PATH_LOCALE\" \"PERL5DB\" \"PERL5LIB\" \"PERL5OPT\" \"PERLIO_DEBUG\" \"PERLLIB\" \"PS4\" \"PYTHONHOME\" \"PYTHONINSPECT\" \"PYTHONPATH\" \"PYTHONUSERBASE\" \"READNULLCMD\" \"RES_OPTIONS\" \"RUBYLIB\" \"RUBYOPT\" \"SHELLOPTS\" \"TERMCAP\" \"TERMINFO\" \"TERMINFO_DIRS\" \"TERMPATH\" \"TMPPREFIX\" \"ZDOTDIR\" \"_RLD*\"]",
   "env_delete=[\"*=()*\" \"BASHOPTS\" \"BASH_ENV\" \"CDPATH\" \"ENV\" \"FPATH\" \"GLOBIGNORE\" \"HOSTALIASES\" \"IFS\" \"JAVA_TOOL_OPTIONS\" \"LC_*\" \"LD_*\" \"LOCALDOMAIN\" \"NLSPATH\" \"NULLCMD\" \"PATH_LOCALE\" \"PERL5DB\" \"PERL5LIB\" \"PERL5OPT\" \"PERLIO_DEBUG\" \"PERLLIB\" \"PS4\" \"PYTHONHOME\" \"PYTHONINSPECT\" \"PYTHONPATH\" \"PYTHONUSERBASE\" \"READNULLCMD\" \"RES_OPTIONS\" \"RUBYLIB\" \"RUBYOPT\" \"SHELLOPTS\" \"TERMCAP\" \"TERMINFO\" \"TERMINFO_DIRS\" \"TERMPATH\" \"TMPPREFIX\" \"XYZZY\" \"ZDOTDIR\" \"_RLD*\"]",
   envDelete [] [], envDelete [] [], envDelete [] [], envDelete [] [], envDelete [] [],
   envDelete [] ["IFS"]]

end SudoersSpec.Settings.Tests
