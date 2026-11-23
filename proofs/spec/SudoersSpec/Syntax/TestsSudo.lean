import SudoersSpec.Syntax.Sudo
import SudoersSpec.Syntax.TestsGrammar
import SudoersSpec.Settings.Dump

/-!
# Tests of the Defaults settings parser, `parse_include`, `Sudo`, and `parse_lines::<Sudo>`

As in `TestsGrammar.lean`: kernel-checked examples, and `#guard` tests (compiled evaluation)
whose expected strings are the output of the legacy Rust code at `70fdb56b` (a `cfg(test)`
build, so descriptions are `"elem"`). A settings modifier is rendered by its effect on
`Settings::default()`: the fields whose dump changed (`mod{field=value;...}`). The rows of
PLAN.md section 3.3 and the findings F-P3 and F-P4 are among the `lines` cases.
-/

namespace SudoersSpec.Syntax.TestsSudo

open SudoersSpec SudoersSpec.Syntax Parser
open SudoersSpec.Syntax.TestsGrammar

/-! ## Rendering -/

/-- A modifier by the fields of `Settings::default()` it changes. -/
def modR (m : Settings.SettingsModifier) : String :=
  let before := Settings.Settings.default.dumpFields
  let after := (m.apply Settings.Settings.default).dumpFields
  let diffs := (before.zip after).filter (fun (x, y) => x.2 != y.2) |>.map
    (fun (_, y) => y.1 ++ "=" ++ y.2)
  "mod{" ++ ";".intercalate diffs ++ "}"

def perm (p : PermissionSpec) : String :=
  s!"perm({speclist userspec p.users},{lst hostscmds p.permissions})"

def scope : ConfigScope → String
  | .generic => "generic"
  | .host h => s!"host({speclist host h})"
  | .user u => s!"user({speclist userspec u})"
  | .runAs u => s!"runas({speclist userspec u})"
  | .command c => s!"command({speclist q c})"

def directive : Directive → String
  | .userAlias v => s!"useralias({lst (defn userspec) v})"
  | .hostAlias v => s!"hostalias({lst (defn host) v})"
  | .cmndAlias v => s!"cmndalias({lst (defn command) v})"
  | .runasAlias v => s!"runasalias({lst (defn userspec) v})"
  | .defaults m sc => "defaults([" ++ ",".intercalate (m.map modR) ++ "]," ++ scope sc ++ ")"

def sudoR : Sudo → String
  | .spec p => s!"spec({perm p})"
  | .decl d => s!"decl({directive d})"
  | .include p sp => s!"include({q p},{span sp})"
  | .includeDir p sp => s!"includedir({q p},{span sp})"
  | .lineComment => "comment"

/-- One production on one input, rendered. -/
def run (prod input : String) : String :=
  match prod with
  | "settings" => go (parseVec settingsModifierMany D.settingsModifier (settingsModifier O D))
      (fun v => "[" ++ ",".intercalate (v.map modR) ++ "]") input
  | "include" => go (parseInclude O D) sudoR input
  | "sudo" => go (sudo O D) sudoR input
  | "lines" =>
    match parseSudoersWith D O input.toList with
    | .error _ => "PANIC"
    | .ok _ => go (parseLines D.sudo (sudo O D))
        (fun items => "[" ++ "; ".intercalate (items.map (parsed sudoR)) ++ "]") input
  | _ => "UNKNOWN"

/-! ## Kernel-checked examples -/

/-- Prefix acceptance (F-P1): the rule is kept, the rest of the line is garbage, and the
newline left behind is a comment line. -/
example : parseSudoersWith D K "alice ALL = ALL !/usr/bin/su\n".toList =
    .ok [.ok (.spec ⟨[.allow (.only (.user (.name "alice")))], [([.allow .all],
      [(none, ⟨[], .allow .all⟩)])]⟩),
      .error (.fatal ⟨(1, 17), (1, 17)⟩ .garbageAtEndOfLine), .ok .lineComment] := by decide
/-- F-P4: a `#` user id that does not fit in `u32` makes the line a comment. -/
example : parseSudoersWith D K "#99999999999 ALL = ALL\n".toList = .ok [.ok .lineComment] := by
  decide
/-- F-P3: a quoted text that is not a user (`"@x"`) is rejected after consuming, and
`expect_nonterminal` reports it as `expected elem` with a span over the consumed part. -/
example : (runOn (sudo K D) "\"@x\" ALL = ALL").1 =
    .error (.fatal ⟨(1, 1), (1, 4)⟩ (.expected "elem")) := by decide
/-- Include directives and their spans. -/
example : parseSudoersWith D K "@include /etc/x\n".toList =
    .ok [.ok (.include "/etc/x" ⟨(1, 2), (1, 16)⟩)] := by decide
example : (runOn (parseInclude K D) "include /etc/x").1 =
    .error (.fatal ⟨(1, 9), (1, 15)⟩ .useQuotesAroundFilenames) := by decide
/-- `Defaults` scopes: a scope character directly after `Defaults`. -/
example : (runOn (sudo K D) "Defaults:alice !env_reset").1 =
    .ok (.decl (.defaults [.env_reset false] (.user [.allow (.only (.user (.name "alice")))]))) := by
  decide
/-- `Defaults@`: the stream goes back to the start of the line and 9 characters forward. -/
example : (runOn (sudo K D) "Defaults@h1,h2 use_pty").1 =
    .ok (.decl (.defaults [.use_pty true] (.host [.allow (.only "h1"), .allow (.only "h2")]))) := by
  decide
/-- Any name that starts with `Defaults` starts a `Defaults` line. -/
example : (runOn (sudo K D) "Defaultsfoo !use_pty").1 =
    .ok (.decl (.defaults [.use_pty false] .generic)) := by decide
example : (runOn (sudo K D) "User_Alias, foo ALIAS=x").1 =
    .error (.fatal ⟨(1, 1), (1, 24)⟩ .ambiguousSyntax) := by decide
/-- Settings: kinds, negation, checkers. -/
example : (runOn (settingsModifier K D) "!passwd_tries").1 =
    .error (.fatal ⟨(1, 2), (1, 14)⟩ (.cannotBeUsedInBooleanContext "passwd_tries")) := by decide
example : (runOn (settingsModifier K D) "passwd_tries+=5").1 =
    .error (.fatal ⟨(1, 1), (1, 15)⟩ (.notAListParameter "passwd_tries")) := by decide
example : (runOn (settingsModifier K D) "env_reset=1").1 =
    .error (.fatal ⟨(1, 11), (1, 11)⟩ (.cannotAssignToBoolean "env_reset")) := by decide
example : (runOn (settingsModifier K D) "passwd_tries").1 =
    .error (.fatal ⟨(1, 1), (1, 13)⟩ (.notABooleanSetting "passwd_tries")) := by decide
example : (runOn (settingsModifier K D) "lecture=sometimes").1 =
    .error (.fatal ⟨(1, 9), (1, 18)⟩ (.invalidValue "sometimes" "lecture")) := by decide
example : (runOn (settingsModifier K D) "foo").1 =
    .error (.fatal ⟨(1, 1), (1, 4)⟩ (.unknownSetting "foo")) := by decide
example : (runOn (settingsModifier K D) "env_keep=\"\"").1 =
    .error (.fatal ⟨(1, 12), (1, 12)⟩ .emptyStringNotAllowed) := by decide
example : (runOn (settingsModifier K D) "env_keep=A=B").1 =
    .error (.fatal ⟨(1, 12), (1, 12)⟩ .doubleQuotesRequired) := by decide
example : (runOn (settingsModifier K D) "env_keep -= \"PATH X=y\"").1 =
    .ok (.env_keep (.Del, ["PATH", "X=y"])) := by decide
example : (runOn (settingsModifier K D) "umask=077").1 = .ok (.umask 63) := by decide
/-- `LeadingWhitespace::parse` at the end of the input (it ends `parse_lines` silently). -/
example : (runOn leadingWhitespace " \t").1 =
    .error (.fatal ⟨(1, 3), (1, 3)⟩ .superfluousWhitespace) := by decide
/-- The panic of `Command::construct` turns into the panic of the whole parse. The parser never
reaches it with the Rust character classes (see `Syntax/README.md`); this oracle makes `/` a
whitespace character. -/
example : parseSudoersWith D
    { K with char := { CharOracle.latin1 with isWhitespace := fun c => c == ' ' || c == '/' } }
    "a ALL = /\n".toList = .error "called `Option::unwrap()` on a `None` value" := by decide

/-! ## Comparison with the legacy Rust code (`#guard` tests) -/

#guard run "settings" "env_reset" ==
  "ok [mod{}] @1:10 rest=\"\""
#guard run "settings" "!env_reset" ==
  "ok [mod{env_reset=false}] @1:11 rest=\"\""
#guard run "settings" "!!env_reset" ==
  "fatal 1:2-1:2 \"expected elem\" @1:2 rest=\"!env_reset\""
#guard run "settings" "env_reset, !use_pty" ==
  "ok [mod{},mod{use_pty=false}] @1:20 rest=\"\""
#guard run "settings" "foo" ==
  "fatal 1:1-1:4 \"unknown setting: 'foo'\" @1:4 rest=\"\""
#guard run "settings" "!foo" ==
  "fatal 1:2-1:5 \"unknown setting: 'foo'\" @1:5 rest=\"\""
#guard run "settings" "!passwd_tries" ==
  "fatal 1:2-1:14 \"'passwd_tries' cannot be used in a boolean context\" @1:14 rest=\"\""
#guard run "settings" "!editor" ==
  "fatal 1:2-1:8 \"'editor' cannot be used in a boolean context\" @1:8 rest=\"\""
#guard run "settings" "!timestamp_type" ==
  "fatal 1:2-1:16 \"'timestamp_type' cannot be used in a boolean context\" @1:16 rest=\"\""
#guard run "settings" "!lecture" ==
  "ok [mod{}] @1:9 rest=\"\""
#guard run "settings" "!secure_path" ==
  "ok [mod{}] @1:13 rest=\"\""
#guard run "settings" "!env_keep" ==
  "ok [mod{env_keep=[]}] @1:10 rest=\"\""
#guard run "settings" "!umask" ==
  "ok [mod{umask=511}] @1:7 rest=\"\""
#guard run "settings" "!passwd_timeout" ==
  "ok [mod{passwd_timeout=0}] @1:16 rest=\"\""
#guard run "settings" "!verifypw" ==
  "ok [mod{verifypw=never}] @1:10 rest=\"\""
#guard run "settings" "passwd_tries=5" ==
  "ok [mod{passwd_tries=5}] @1:15 rest=\"\""
#guard run "settings" "passwd_tries = 5" ==
  "ok [mod{passwd_tries=5}] @1:17 rest=\"\""
#guard run "settings" "passwd_tries=1000" ==
  "ok [mod{passwd_tries=1000}] @1:18 rest=\"\""
#guard run "settings" "passwd_tries=1001" ==
  "fatal 1:14-1:18 \"'1001' is not a valid value for passwd_tries\" @1:18 rest=\"\""
#guard run "settings" "passwd_tries=a" ==
  "fatal 1:14-1:15 \"'a' is not a valid value for passwd_tries\" @1:15 rest=\"\""
#guard run "settings" "passwd_tries" ==
  "fatal 1:1-1:13 \"'passwd_tries' is not a boolean setting\" @1:13 rest=\"\""
#guard run "settings" "passwd_tries+=5" ==
  "fatal 1:1-1:15 \"passwd_tries is not a list parameter\" @1:15 rest=\"5\""
#guard run "settings" "passwd_tries-=5" ==
  "fatal 1:1-1:15 \"passwd_tries is not a list parameter\" @1:15 rest=\"5\""
#guard run "settings" "env_reset=1" ==
  "fatal 1:11-1:11 \"can't assign to boolean setting 'env_reset'\" @1:11 rest=\"1\""
#guard run "settings" "env_reset+=x" ==
  "fatal 1:1-1:12 \"env_reset is not a list parameter\" @1:12 rest=\"x\""
#guard run "settings" "umask=0077" ==
  "ok [mod{umask=63}] @1:11 rest=\"\""
#guard run "settings" "umask=077" ==
  "ok [mod{umask=63}] @1:10 rest=\"\""
#guard run "settings" "umask=0" ==
  "fatal 1:7-1:8 \"'0' is not a valid value for umask\" @1:8 rest=\"\""
#guard run "settings" "umask=00" ==
  "ok [mod{umask=0}] @1:9 rest=\"\""
#guard run "settings" "umask=0778" ==
  "fatal 1:7-1:11 \"'0778' is not a valid value for umask\" @1:11 rest=\"\""
#guard run "settings" "umask=77" ==
  "fatal 1:7-1:9 \"'77' is not a valid value for umask\" @1:9 rest=\"\""
#guard run "settings" "umask=037777777777" ==
  "ok [mod{umask=4294967295}] @1:19 rest=\"\""
#guard run "settings" "umask=040000000000" ==
  "fatal 1:7-1:19 \"'040000000000' is not a valid value for umask\" @1:19 rest=\"\""
#guard run "settings" "timestamp_timeout=5" ==
  "ok [mod{timestamp_timeout=300}] @1:20 rest=\"\""
#guard run "settings" "timestamp_timeout=2.5" ==
  "ok [mod{timestamp_timeout=150}] @1:22 rest=\"\""
#guard run "settings" "timestamp_timeout=.5" ==
  "fatal 1:19-1:21 \"'.5' is not a valid value for timestamp_timeout\" @1:21 rest=\"\""
#guard run "settings" "timestamp_timeout=5." ==
  "fatal 1:19-1:21 \"'5.' is not a valid value for timestamp_timeout\" @1:21 rest=\"\""
#guard run "settings" "timestamp_timeout=1.2.3" ==
  "fatal 1:19-1:24 \"'1.2.3' is not a valid value for timestamp_timeout\" @1:24 rest=\"\""
#guard run "settings" "timestamp_timeout=0.01" ==
  "ok [mod{timestamp_timeout=0}] @1:23 rest=\"\""
#guard run "settings" "timestamp_timeout=999999999999999999" ==
  "fatal 1:19-1:37 \"'999999999999999999' is not a valid value for timestamp_timeout\" @1:37 rest=\"\""
#guard run "settings" "timestamp_timeout=99999999999999999" ==
  "ok [mod{timestamp_timeout=5999999999999999940}] @1:36 rest=\"\""
#guard run "settings" "passwd_timeout=1.333" ==
  "ok [mod{passwd_timeout=79}] @1:21 rest=\"\""
#guard run "settings" "timestamp_timeout=1e" ==
  "fatal 1:19-1:21 \"'1e' is not a valid value for timestamp_timeout\" @1:21 rest=\"\""
#guard run "settings" "lecture=always" ==
  "ok [mod{lecture=always}] @1:15 rest=\"\""
#guard run "settings" "lecture=once" ==
  "ok [mod{lecture=once}] @1:13 rest=\"\""
#guard run "settings" "lecture=sometimes" ==
  "fatal 1:9-1:18 \"'sometimes' is not a valid value for lecture\" @1:18 rest=\"\""
#guard run "settings" "verifypw=any" ==
  "ok [mod{verifypw=any}] @1:13 rest=\"\""
#guard run "settings" "timestamp_type=ppid" ==
  "ok [mod{timestamp_type=ppid}] @1:20 rest=\"\""
#guard run "settings" "timestamp_type=tty" ==
  "ok [mod{}] @1:19 rest=\"\""
#guard run "settings" "timestamp_type=x" ==
  "fatal 1:16-1:17 \"'x' is not a valid value for timestamp_type\" @1:17 rest=\"\""
#guard run "settings" "secure_path=/usr/bin:/bin" ==
  "ok [mod{secure_path=(some \"/usr/bin:/bin\")}] @1:26 rest=\"\""
#guard run "settings" "secure_path=\"/usr/bin /bin\"" ==
  "ok [mod{secure_path=(some \"/usr/bin /bin\")}] @1:28 rest=\"\""
#guard run "settings" "secure_path=" ==
  "fatal 1:13-1:13 \"expected elem\" @1:13 rest=\"\""
#guard run "settings" "secure_path=\"\"" ==
  "fatal 1:14-1:14 \"expected elem\" @1:14 rest=\"\\\"\""
#guard run "settings" "secure_path=\"a\\\"b\"" ==
  "ok [mod{secure_path=(some \"a\\\"b\")}] @1:19 rest=\"\""
#guard run "settings" "secure_path=a,b" ==
  "fatal 1:15-1:16 \"unknown setting: 'b'\" @1:16 rest=\"\""
#guard run "settings" "editor=/usr/bin/vim" ==
  "ok [mod{editor=\"/usr/bin/vim\"}] @1:20 rest=\"\""
#guard run "settings" "editor=\"vi\"" ==
  "ok [mod{editor=\"vi\"}] @1:12 rest=\"\""
#guard run "settings" "runcwd=*" ==
  "ok [mod{runcwd=(some \"*\")}] @1:9 rest=\"\""
#guard run "settings" "apparmor_profile=x" ==
  "ok [mod{apparmor_profile=(some \"x\")}] @1:19 rest=\"\""
#guard run "settings" "mailerpath=/x" ==
  "ok [mod{mailerpath=(some \"/x\")}] @1:14 rest=\"\""
#guard run "settings" "env_keep=\"FOO BAR\"" ==
  "ok [mod{env_keep=[\"BAR\" \"FOO\"]}] @1:19 rest=\"\""
#guard run "settings" "env_keep=FOO" ==
  "ok [mod{env_keep=[\"FOO\"]}] @1:13 rest=\"\""
#guard run "settings" "env_keep+=\"FOO\"" ==
  "ok [mod{env_keep=[\"COLORS\" \"DISPLAY\" \"FOO\" \"HOSTNAME\" \"KRB5CCNAME\" \"LS_COLORS\" \"PATH\" \"PS1\" \"PS2\" \"XAUTHORITY\" \"XAUTHORIZATION\" \"XDG_CURRENT_DESKTOP\"]}] @1:16 rest=\"\""
#guard run "settings" "env_keep+=FOO" ==
  "ok [mod{env_keep=[\"COLORS\" \"DISPLAY\" \"FOO\" \"HOSTNAME\" \"KRB5CCNAME\" \"LS_COLORS\" \"PATH\" \"PS1\" \"PS2\" \"XAUTHORITY\" \"XAUTHORIZATION\" \"XDG_CURRENT_DESKTOP\"]}] @1:14 rest=\"\""
#guard run "settings" "env_keep-=PATH" ==
  "ok [mod{env_keep=[\"COLORS\" \"DISPLAY\" \"HOSTNAME\" \"KRB5CCNAME\" \"LS_COLORS\" \"PS1\" \"PS2\" \"XAUTHORITY\" \"XAUTHORIZATION\" \"XDG_CURRENT_DESKTOP\"]}] @1:15 rest=\"\""
#guard run "settings" "env_keep -= \"PATH COLORS\"" ==
  "ok [mod{env_keep=[\"DISPLAY\" \"HOSTNAME\" \"KRB5CCNAME\" \"LS_COLORS\" \"PS1\" \"PS2\" \"XAUTHORITY\" \"XAUTHORIZATION\" \"XDG_CURRENT_DESKTOP\"]}] @1:26 rest=\"\""
#guard run "settings" "env_keep=\"\"" ==
  "fatal 1:12-1:12 \"empty string not allowed\" @1:12 rest=\"\""
#guard run "settings" "env_keep=A=B" ==
  "fatal 1:12-1:12 \"double quotes are required for VAR=value pairs\" @1:12 rest=\"B\""
#guard run "settings" "env_keep=\"A=B C\"" ==
  "ok [mod{env_keep=[\"A=B\" \"C\"]}] @1:17 rest=\"\""
#guard run "settings" "env_keep=\"A=b c\"" ==
  "ok [mod{env_keep=[\"A=b\" \"c\"]}] @1:17 rest=\"\""
#guard run "settings" "env_check=\"LC_*\"" ==
  "ok [mod{env_check=[\"LC_*\"]}] @1:17 rest=\"\""
#guard run "settings" "env_delete+=\"X\"" ==
  "ok [mod{env_delete=[\"*=()*\" \"BASHOPTS\" \"BASH_ENV\" \"CDPATH\" \"ENV\" \"FPATH\" \"GLOBIGNORE\" \"HOSTALIASES\" \"IFS\" \"JAVA_TOOL_OPTIONS\" \"LD_*\" \"LOCALDOMAIN\" \"NLSPATH\" \"NULLCMD\" \"PATH_LOCALE\" \"PERL5DB\" \"PERL5LIB\" \"PERL5OPT\" \"PERLIO_DEBUG\" \"PERLLIB\" \"PS4\" \"PYTHONHOME\" \"PYTHONINSPECT\" \"PYTHONPATH\" \"PYTHONUSERBASE\" \"READNULLCMD\" \"RES_OPTIONS\" \"RUBYLIB\" \"RUBYOPT\" \"SHELLOPTS\" \"TERMCAP\" \"TERMINFO\" \"TERMINFO_DIRS\" \"TERMPATH\" \"TMPPREFIX\" \"X\" \"ZDOTDIR\" \"_RLD*\"]}] @1:16 rest=\"\""
#guard run "settings" "env_keep=\"FOO" ==
  "fatal 1:14-1:14 \"expecting '\\\"' but found 'EOF'\" @1:14 rest=\"\""
#guard run "settings" "env_keep" ==
  "fatal 1:1-1:9 \"'env_keep' is not a boolean setting\" @1:9 rest=\"\""
#guard run "settings" "env_keep +=  \"A\"" ==
  "ok [mod{env_keep=[\"A\" \"COLORS\" \"DISPLAY\" \"HOSTNAME\" \"KRB5CCNAME\" \"LS_COLORS\" \"PATH\" \"PS1\" \"PS2\" \"XAUTHORITY\" \"XAUTHORIZATION\" \"XDG_CURRENT_DESKTOP\"]}] @1:17 rest=\"\""
#guard run "settings" "env_keep=\"A,B\"" ==
  "fatal 1:12-1:12 \"expecting '\\\"' but found ','\" @1:12 rest=\",B\\\"\""
#guard run "settings" "secure_path=/a, env_reset" ==
  "ok [mod{secure_path=(some \"/a\")},mod{}] @1:26 rest=\"\""
#guard run "settings" "secure_path=/a env_reset" ==
  "ok [mod{secure_path=(some \"/a\")}] @1:16 rest=\"env_reset\""
#guard run "settings" "use_pty," ==
  "fatal 1:9-1:9 \"expected elem\" @1:9 rest=\"\""
#guard run "settings" "Ü" ==
  "reject @1:1 rest=\"\\u{dc}\""
#guard run "settings" "" ==
  "reject @1:1 rest=\"\""

/-- The variable-list limit: 127 names pass, the 128th is fatal. -/
def vars (n : Nat) : String :=
  "env_keep=\"" ++ " ".intercalate ((List.range n).map fun i => s!"V{i}") ++ "\""
#guard run "settings" (vars 128) ==
  "fatal 1:540-1:540 \"environment variable list too long\" @1:540 rest=\"\\\"\""
#guard (run "settings" (vars 127)).endsWith "\"V97\" \"V98\" \"V99\"]}] @1:536 rest=\"\""

#guard run "include" "include /etc/x\n" ==
  "ok include(\"/etc/x\",1:1-1:15) @1:15 rest=\"\\u{a}\""
#guard run "include" "include /etc/x" ==
  "fatal 1:9-1:15 \"use quotes around filenames or escape whitespace\" @1:15 rest=\"\""
#guard run "include" "include /etc/x \n" ==
  "ok include(\"/etc/x\",1:1-1:16) @1:16 rest=\"\\u{a}\""
#guard run "include" "include /etc/x #c\n" ==
  "fatal 1:9-1:16 \"use quotes around filenames or escape whitespace\" @1:16 rest=\"#c\\u{a}\""
#guard run "include" "include \"/etc/a b\"" ==
  "ok include(\"/etc/a b\",1:1-1:19) @1:19 rest=\"\""
#guard run "include" "include \"/etc/a b\"x" ==
  "ok include(\"/etc/a b\",1:1-1:19) @1:19 rest=\"x\""
#guard run "include" "includedir /etc/sudoers.d\n" ==
  "ok includedir(\"/etc/sudoers.d\",1:1-1:26) @1:26 rest=\"\\u{a}\""
#guard run "include" "foo /x\n" ==
  "fatal 1:1-1:5 \"unknown directive\" @1:5 rest=\"/x\\u{a}\""
#guard run "include" " include /x\n" ==
  "fatal 1:1-1:2 \"unknown directive\" @1:2 rest=\"include /x\\u{a}\""
#guard run "include" "include\n" ==
  "fatal 1:8-1:8 \"expected elem\" @1:8 rest=\"\\u{a}\""
#guard run "include" "include \"\"" ==
  "fatal 1:10-1:10 \"expected elem\" @1:10 rest=\"\\\"\""
#guard run "include" "socket /x\n" ==
  "fatal 1:1-1:8 \"unknown directive\" @1:8 rest=\"/x\\u{a}\""
#guard run "include" "Include /x\n" ==
  "fatal 1:1-1:9 \"unknown directive\" @1:9 rest=\"/x\\u{a}\""

#guard run "sudo" "alice ALL = ALL" ==
  "ok spec(perm([allow(only(user(name:\"alice\")))],[([allow(ALL)],[(none,cs([],allow(ALL)))])])) @1:16 rest=\"\""
#guard run "sudo" "@include /etc/x\n" ==
  "ok include(\"/etc/x\",1:2-1:16) @1:16 rest=\"\\u{a}\""
#guard run "sudo" "#include /etc/x\n" ==
  "ok include(\"/etc/x\",1:2-1:16) @1:16 rest=\"\\u{a}\""
#guard run "sudo" "#includedir /etc/d\n" ==
  "ok includedir(\"/etc/d\",1:2-1:19) @1:19 rest=\"\\u{a}\""
#guard run "sudo" "# comment" ==
  "ok comment @1:10 rest=\"\""
#guard run "sudo" "#" ==
  "ok comment @1:2 rest=\"\""
#guard run "sudo" "#123 ALL = ALL" ==
  "ok spec(perm([allow(only(user(id:123)))],[([allow(ALL)],[(none,cs([],allow(ALL)))])])) @1:15 rest=\"\""
#guard run "sudo" "#123, bob ALL = ALL" ==
  "ok spec(perm([allow(only(user(id:123))),allow(only(user(name:\"bob\")))],[([allow(ALL)],[(none,cs([],allow(ALL)))])])) @1:20 rest=\"\""
#guard run "sudo" "#4294967296 ALL = ALL" ==
  "ok comment @1:22 rest=\"\""
#guard run "sudo" "#x" ==
  "ok comment @1:3 rest=\"\""
#guard run "sudo" "\"alice\" ALL = ALL" ==
  "ok spec(perm([allow(only(user(name:\"alice\")))],[([allow(ALL)],[(none,cs([],allow(ALL)))])])) @1:18 rest=\"\""
#guard run "sudo" "\"@x\" ALL = ALL" ==
  "fatal 1:1-1:4 \"expected elem\" @1:4 rest=\"\\\" ALL = ALL\""
#guard run "sudo" "User_Alias A = alice" ==
  "ok decl(useralias([def(\"A\",[allow(only(user(name:\"alice\")))])])) @1:21 rest=\"\""
#guard run "sudo" "User_Alias, foo ALIAS=x" ==
  "fatal 1:1-1:24 \"ambiguous syntax\" @1:24 rest=\"\""
#guard run "sudo" "foo, User_Alias A = alice" ==
  "fatal 1:21-1:21 \"expected elem\" @1:21 rest=\"alice\""
#guard run "sudo" "Host_Alias H = h1, h2" ==
  "ok decl(hostalias([def(\"H\",[allow(only(\"h1\")),allow(only(\"h2\"))])])) @1:22 rest=\"\""
#guard run "sudo" "Cmnd_Alias C = /bin/ls" ==
  "ok decl(cmndalias([def(\"C\",[allow(only(cmd(\"/bin/ls\",prefix[])))])])) @1:23 rest=\"\""
#guard run "sudo" "Cmd_Alias C = /bin/ls" ==
  "ok decl(cmndalias([def(\"C\",[allow(only(cmd(\"/bin/ls\",prefix[])))])])) @1:22 rest=\"\""
#guard run "sudo" "Runas_Alias R = root" ==
  "ok decl(runasalias([def(\"R\",[allow(only(user(name:\"root\")))])])) @1:21 rest=\"\""
#guard run "sudo" "Defaults env_reset" ==
  "ok decl(defaults([mod{}],generic)) @1:19 rest=\"\""
#guard run "sudo" "Defaults:alice env_reset" ==
  "ok decl(defaults([mod{}],user([allow(only(user(name:\"alice\")))]))) @1:25 rest=\"\""
#guard run "sudo" "Defaults :alice env_reset" ==
  "fatal 1:10-1:10 \"expected elem\" @1:10 rest=\":alice env_reset\""
#guard run "sudo" "Defaults!/bin/ls env_reset" ==
  "ok decl(defaults([mod{}],command([allow(only(\"/bin/ls\"))]))) @1:27 rest=\"\""
#guard run "sudo" "Defaults>root env_reset" ==
  "ok decl(defaults([mod{}],runas([allow(only(user(name:\"root\")))]))) @1:24 rest=\"\""
#guard run "sudo" "Defaults@host env_reset" ==
  "ok decl(defaults([mod{}],host([allow(only(\"host\"))]))) @1:24 rest=\"\""
#guard run "sudo" "Defaults@h1,h2 env_reset" ==
  "ok decl(defaults([mod{}],host([allow(only(\"h1\")),allow(only(\"h2\"))]))) @1:25 rest=\"\""
#guard run "sudo" "Defaultsfoo env_reset" ==
  "ok decl(defaults([mod{}],generic)) @1:22 rest=\"\""
#guard run "sudo" "Defaults_x env_reset" ==
  "ok decl(defaults([mod{}],generic)) @1:21 rest=\"\""
#guard run "sudo" "Defaults" ==
  "fatal 1:9-1:9 \"expected elem\" @1:9 rest=\"\""
#guard run "sudo" "Defaults " ==
  "fatal 1:10-1:10 \"expected elem\" @1:10 rest=\"\""
#guard run "sudo" "Defaults,foo env_reset" ==
  "fatal 1:1-1:23 \"ambiguous syntax\" @1:23 rest=\"\""
#guard run "sudo" "foo,Defaults env_reset" ==
  "fatal 1:23-1:23 \"expecting '=' but found 'EOF'\" @1:23 rest=\"\""
#guard run "sudo" "Defaults\\:x env_reset" ==
  "ok decl(defaults([mod{}],generic)) @1:22 rest=\"\""
#guard run "sudo" "!alice ALL = ALL" ==
  "ok spec(perm([forbid(only(user(name:\"alice\")))],[([allow(ALL)],[(none,cs([],allow(ALL)))])])) @1:17 rest=\"\""
#guard run "sudo" "ALL ALL = ALL" ==
  "ok spec(perm([allow(ALL)],[([allow(ALL)],[(none,cs([],allow(ALL)))])])) @1:14 rest=\"\""
#guard run "sudo" "alice" ==
  "fatal 1:6-1:6 \"expected elem\" @1:6 rest=\"\""
#guard run "sudo" "alice ALL" ==
  "fatal 1:10-1:10 \"expecting '=' but found 'EOF'\" @1:10 rest=\"\""
#guard run "sudo" ")" ==
  "ok comment @1:1 rest=\")\""
#guard run "sudo" "Defaults@ env_reset" ==
  "fatal 1:20-1:20 \"expected elem\" @1:20 rest=\"\""
#guard run "sudo" "Defaults:alice,bob !env_reset" ==
  "ok decl(defaults([mod{env_reset=false}],user([allow(only(user(name:\"alice\"))),allow(only(user(name:\"bob\")))]))) @1:30 rest=\"\""
#guard run "sudo" "User_Alias A = alice : B = bob" ==
  "ok decl(useralias([def(\"A\",[allow(only(user(name:\"alice\")))]),def(\"B\",[allow(only(user(name:\"bob\")))])])) @1:31 rest=\"\""
#guard run "sudo" "Runas_Alias NOTROOT = ALL !root" ==
  "ok decl(runasalias([def(\"NOTROOT\",[allow(ALL)])])) @1:27 rest=\"!root\""
#guard run "sudo" "Cmnd_Alias SAFE = ALL !/usr/bin/su" ==
  "fatal 1:19-1:35 \"fully qualified path needed\" @1:35 rest=\"\""
#guard run "sudo" "alice,bob ALL=ALL" ==
  "ok spec(perm([allow(only(user(name:\"alice\"))),allow(only(user(name:\"bob\")))],[([allow(ALL)],[(none,cs([],allow(ALL)))])])) @1:18 rest=\"\""
#guard run "sudo" "Defaults secure_path=\"/usr/bin\", timestamp_timeout=0, noexec" ==
  "ok decl(defaults([mod{secure_path=(some \"/usr/bin\")},mod{timestamp_timeout=0},mod{noexec=true}],generic)) @1:61 rest=\"\""
#guard run "sudo" "Defaults secure_path=\"/usr/bin\" timestamp_timeout=0" ==
  "ok decl(defaults([mod{secure_path=(some \"/usr/bin\")}],generic)) @1:33 rest=\"timestamp_timeout=0\""
#guard run "sudo" "Defaults logfile=\"/var/log/sudo.log\"" ==
  "fatal 1:10-1:17 \"unknown setting: 'logfile'\" @1:17 rest=\"=\\\"/var/log/sudo.log\\\"\""
#guard run "sudo" "\\\nDefaults@x env_reset" ==
  "fatal 2:9-2:9 \"expected elem\" @2:9 rest=\"@x env_reset\""
#guard run "sudo" "Defaults@host,bob env_reset" ==
  "ok decl(defaults([mod{}],host([allow(only(\"host\")),allow(only(\"bob\"))]))) @1:28 rest=\"\""

#guard run "lines" "alice ALL = /bin/a, sha224:x \\\nbob ALL = (ALL) ALL\n" ==
  "ok [fatal 1:21-1:27 \"digest specifications are not supported\"; ok comment; ok spec(perm([allow(only(user(name:\"bob\")))],[([allow(ALL)],[(some(runas([allow(ALL)];[])),cs([],allow(ALL)))])]))] @3:1 rest=\"\""
#guard run "lines" "alice ALL = /bin/a, /bin/b \\\nbob ALL = (ALL) ALL\n" ==
  "ok [ok spec(perm([allow(only(user(name:\"alice\")))],[([allow(ALL)],[(none,cs([],allow(only(cmd(\"/bin/a\",prefix[]))))),(none,cs([],allow(only(cmd(\"/bin/b\",exact[\"bob\",\"ALL\",\"=\",\"(ALL)\",\"ALL\"])))))])]))] @3:1 rest=\"\""
#guard run "lines" "alice ALL = ALL" ==
  "ok [ok spec(perm([allow(only(user(name:\"alice\")))],[([allow(ALL)],[(none,cs([],allow(ALL)))])])); fatal 1:16-1:16 \"missing line terminator at end of file\"] @1:16 rest=\"\""
#guard run "lines" "alice ALL = ALL ) junk\nbob ALL = ALL\n" ==
  "ok [ok spec(perm([allow(only(user(name:\"alice\")))],[([allow(ALL)],[(none,cs([],allow(ALL)))])])); fatal 1:17-1:17 \"garbage at end of line\"; ok comment; ok spec(perm([allow(only(user(name:\"bob\")))],[([allow(ALL)],[(none,cs([],allow(ALL)))])]))] @3:1 rest=\"\""
#guard run "lines" "alice ALL = ALL, !/usr/bin/su\n" ==
  "ok [ok spec(perm([allow(only(user(name:\"alice\")))],[([allow(ALL)],[(none,cs([],allow(ALL))),(none,cs([],forbid(only(cmd(\"/usr/bin/su\",prefix[])))))])]))] @2:1 rest=\"\""
#guard run "lines" "alice ALL = ALL !/usr/bin/su\n" ==
  "ok [ok spec(perm([allow(only(user(name:\"alice\")))],[([allow(ALL)],[(none,cs([],allow(ALL)))])])); fatal 1:17-1:17 \"garbage at end of line\"; ok comment] @2:1 rest=\"\""
#guard run "lines" "alice ALL = ALL, !sha224:x\n" ==
  "ok [fatal 1:19-1:25 \"digest specifications are not supported\"; ok comment] @2:1 rest=\"\""
#guard run "lines" "Runas_Alias NOTROOT = ALL !root\nalice ALL = (NOTROOT) /usr/bin/id\n" ==
  "ok [ok decl(runasalias([def(\"NOTROOT\",[allow(ALL)])])); fatal 1:27-1:27 \"garbage at end of line\"; ok comment; ok spec(perm([allow(only(user(name:\"alice\")))],[([allow(ALL)],[(some(runas([allow(alias:\"NOTROOT\")];[])),cs([],allow(only(cmd(\"/usr/bin/id\",prefix[])))))])]))] @3:1 rest=\"\""
#guard run "lines" "Cmnd_Alias SAFE = ALL !/usr/bin/su\nalice ALL = SAFE\n" ==
  "ok [fatal 1:19-1:35 \"fully qualified path needed\"; ok spec(perm([allow(only(user(name:\"alice\")))],[([allow(ALL)],[(none,cs([],allow(alias:\"SAFE\")))])]))] @3:1 rest=\"\""
#guard run "lines" "alice ALL = ALL\nalice ALL !/usr/bin/su\n" ==
  "ok [ok spec(perm([allow(only(user(name:\"alice\")))],[([allow(ALL)],[(none,cs([],allow(ALL)))])])); fatal 2:11-2:11 \"expecting '=' but found '!'\"; ok comment] @3:1 rest=\"\""
#guard run "lines" "Cmnd_Alias SHELLS /usr/bin/su, /usr/bin/bash\nalice ALL = ALL, !SHELLS\n" ==
  "ok [fatal 1:19-1:19 \"expecting '=' but found '/'\"; ok comment; ok spec(perm([allow(only(user(name:\"alice\")))],[([allow(ALL)],[(none,cs([],allow(ALL))),(none,cs([],forbid(alias:\"SHELLS\")))])]))] @3:1 rest=\"\""
#guard run "lines" "alice ALL = INTERCEPT: ALL\n" ==
  "ok [fatal 1:13-1:22 \"INTERCEPT is not supported by sudo-rs\"; ok comment] @2:1 rest=\"\""
#guard run "lines" "Defaults secure_path=\"/usr/bin\", timestamp_timeout=0, noexec\n" ==
  "ok [ok decl(defaults([mod{secure_path=(some \"/usr/bin\")},mod{timestamp_timeout=0},mod{noexec=true}],generic))] @2:1 rest=\"\""
#guard run "lines" "Defaults secure_path=\"/usr/bin\", timestamp_timeout=0, noexec, logfile=\"/var/log/sudo.log\"\n" ==
  "ok [fatal 1:63-1:70 \"unknown setting: 'logfile'\"; ok comment] @2:1 rest=\"\""
#guard run "lines" "Defaults secure_path=\"/usr/bin\" timestamp_timeout=0\n" ==
  "ok [ok decl(defaults([mod{secure_path=(some \"/usr/bin\")}],generic)); fatal 1:33-1:33 \"garbage at end of line\"; ok comment] @2:1 rest=\"\""
#guard run "lines" "\"@x\" ALL = ALL\nbob ALL = ALL\n" ==
  "ok [fatal 1:1-1:4 \"expected elem\"; ok comment; ok spec(perm([allow(only(user(name:\"bob\")))],[([allow(ALL)],[(none,cs([],allow(ALL)))])]))] @3:1 rest=\"\""
#guard run "lines" "#99999999999 ALL = ALL\nbob ALL=ALL\n" ==
  "ok [ok comment; ok spec(perm([allow(only(user(name:\"bob\")))],[([allow(ALL)],[(none,cs([],allow(ALL)))])]))] @3:1 rest=\"\""
#guard run "lines" "# comment\n#include /etc/x\n@includedir /etc/d\n" ==
  "ok [ok comment; ok include(\"/etc/x\",2:2-2:16); ok includedir(\"/etc/d\",3:2-3:19)] @4:1 rest=\"\""
#guard run "lines" "\n\n  \n\t\n" ==
  "ok [ok comment; ok comment; ok comment; ok comment] @5:1 rest=\"\""
#guard run "lines" "alice ALL = ALL # comment\n" ==
  "ok [ok spec(perm([allow(only(user(name:\"alice\")))],[([allow(ALL)],[(none,cs([],allow(ALL)))])]))] @2:1 rest=\"\""
#guard run "lines" "alice ALL = ALL\\\n, /bin/ls\n" ==
  "ok [ok spec(perm([allow(only(user(name:\"alice\")))],[([allow(ALL)],[(none,cs([],allow(ALL))),(none,cs([],allow(only(cmd(\"/bin/ls\",prefix[])))))])]))] @3:1 rest=\"\""
#guard run "lines" "alice ALL = \\ \n" ==
  "ok [fatal 1:14-1:14 \"expecting '=' but found ' '\"; ok comment] @2:1 rest=\"\""
#guard run "lines" "@include /x y\nbob ALL = ALL\n" ==
  "ok [fatal 1:10-1:13 \"use quotes around filenames or escape whitespace\"; ok comment; ok spec(perm([allow(only(user(name:\"bob\")))],[([allow(ALL)],[(none,cs([],allow(ALL)))])]))] @3:1 rest=\"\""
#guard run "lines" "Defaults:alice !env_reset\nDefaults env_keep += \"FOO\"\n" ==
  "ok [ok decl(defaults([mod{env_reset=false}],user([allow(only(user(name:\"alice\")))]))); ok decl(defaults([mod{env_keep=[\"COLORS\" \"DISPLAY\" \"FOO\" \"HOSTNAME\" \"KRB5CCNAME\" \"LS_COLORS\" \"PATH\" \"PS1\" \"PS2\" \"XAUTHORITY\" \"XAUTHORIZATION\" \"XDG_CURRENT_DESKTOP\"]}],generic))] @3:1 rest=\"\""
#guard run "lines" "User_Alias ADMINS = alice, %wheel\nADMINS ALL = (ALL:ALL) NOPASSWD: ALL\n" ==
  "ok [ok decl(useralias([def(\"ADMINS\",[allow(only(user(name:\"alice\"))),allow(only(group(name:\"wheel\")))])])); ok spec(perm([allow(alias:\"ADMINS\")],[([allow(ALL)],[(some(runas([allow(ALL)];[allow(ALL)])),cs([nopasswd],allow(ALL)))])]))] @3:1 rest=\"\""
#guard run "lines" "%wheel ALL=(ALL) ALL\n%:x ALL = ALL\n+net ALL = ALL\n" ==
  "ok [ok spec(perm([allow(only(group(name:\"wheel\")))],[([allow(ALL)],[(some(runas([allow(ALL)];[])),cs([],allow(ALL)))])])); ok spec(perm([allow(only(nonunix(name:\"x\")))],[([allow(ALL)],[(none,cs([],allow(ALL)))])])); fatal 3:2-3:2 \"netgroups are not supported yet\"; ok comment] @4:1 rest=\"\""
#guard run "lines" "alice ALL = (root) CWD=/tmp NOPASSWD: /bin/ls, (bob) ALL : h2 = /bin/sh\n" ==
  "ok [ok spec(perm([allow(only(user(name:\"alice\")))],[([allow(ALL)],[(some(runas([allow(only(user(name:\"root\")))];[])),cs([cwd(path(\"/tmp\")),nopasswd],allow(only(cmd(\"/bin/ls\",prefix[]))))),(some(runas([allow(only(user(name:\"bob\")))];[])),cs([],allow(ALL)))]),([allow(only(\"h2\"))],[(none,cs([],allow(only(cmd(\"/bin/sh\",prefix[])))))])]))] @2:1 rest=\"\""
#guard run "lines" "alice ALL = /bin/ls\r\n" ==
  "ok [ok spec(perm([allow(only(user(name:\"alice\")))],[([allow(ALL)],[(none,cs([],allow(only(cmd(\"/bin/ls\",prefix[])))))])])); fatal 1:20-1:20 \"garbage at end of line\"; ok comment] @2:1 rest=\"\""
#guard run "lines" "alice\tALL\t=\tALL\n" ==
  "ok [ok spec(perm([allow(only(user(name:\"alice\")))],[([allow(ALL)],[(none,cs([],allow(ALL)))])]))] @2:1 rest=\"\""
#guard run "lines" "@include\n" ==
  "ok [fatal 1:9-1:9 \"expected elem\"] @2:1 rest=\"\""
#guard run "lines" "Defaults !lecture, lecture=always, !env_keep\n" ==
  "ok [ok decl(defaults([mod{},mod{lecture=always},mod{env_keep=[]}],generic))] @2:1 rest=\"\""

end SudoersSpec.Syntax.TestsSudo
