import Differential.Rng
import Differential.Quote

/-!
# Corpus generator for the sudoers parser (stage P0)

Grammar-directed texts that cover every construct of the legacy sudo-rs parser, and mutations
of them for error recovery. Every case is a pure function of `(seed, category, index)`; the
corpus is printed one case per line as `<category>:<index> <quoted text>` (quoting rule:
`Differential.Quote`, `proofs/parser/DUMP.md`).

Conventions (`DUMP.md`, "Corpus conventions"):

* command paths start with `/sudoers-nx/`, which must not exist on the host, so that
  `SimpleCommand::construct` never canonicalizes them; the category `fixture` uses paths under
  `/tmp/sudo-rs-parser-dump-fixture`, a directory the harnesses create with a known layout;
* include targets are either the fixture's empty file `include` and empty directory `incdir`,
  or paths under `/sudoers-nx/`.

Mutation of a text deletes, inserts, replaces, duplicates or swaps a character or a token,
truncates the text, or splices two lines; characters are drawn with a bias towards the
structural characters `,:=!()"\#@%+` and newline.
-/

namespace Differential.ParserCorpus

open Gen

def nx : String := "/sudoers-nx"
def fixture : String := "/tmp/sudo-rs-parser-dump-fixture"

instance : Inhabited (Gen String) := ⟨pure ""⟩

/-- A generator chosen by weight. -/
def oneOf [Inhabited α] (l : List (Nat × Gen α)) : Gen α := do
  let total := l.foldl (· + ·.1) 0
  let mut r ← below total
  for (w, g) in l do
    if r < w then return ← g
    r := r - w
  return default

def str (n : Nat) (s : String) : String := String.join (List.replicate n s)

/-! ## Whitespace and separators -/

def sp : Gen String := oneOf [(10, pure " "), (2, pure "\t"), (2, pure "  "), (1, pure " \t ")]
def osp : Gen String := oneOf [(6, pure ""), (5, sp)]

def joinWith (sepG : Gen String) : List String → Gen String
  | [] => pure ""
  | x :: xs => do
    let mut out := x
    for y in xs do out := out ++ (← sepG) ++ y
    return out

def sepBy (c : String) : Gen String := do return (← osp) ++ c ++ (← osp)

def listG (lo hi : Nat) (g : Gen String) (c : String := ",") : Gen String := do
  joinWith (sepBy c) (← listOf lo hi g)

/-- Zero or more `!` (each optionally followed by whitespace) before an item. -/
def neg (g : Gen String) : Gen String := do
  let n ← weighted [(10, 0), (3, 1), (1, 2), (1, 3)]
  let mut out := ""
  for _ in [0:n] do out := out ++ "!" ++ (← oneOf [(3, pure ""), (1, sp)])
  return out ++ (← g)

/-- Every generator below takes `wild`: `false` draws only forms the legacy parser accepts,
`true` adds rejected and borderline forms (one draw in three). -/
def pickW (wild : Bool) (ok bad : List String) : Gen String :=
  if wild then oneOf [(2, pick ok), (1, pick bad)] else pick ok

def oneOfW [Inhabited α] (wild : Bool) (ok bad : List (Nat × Gen α)) : Gen α :=
  oneOf (if wild then ok ++ bad else ok)

/-! ## Users, groups, hosts -/

def plainNames : List String :=
  ["root", "alice", "bob", "carol", "dave", "eve", "www-data", "svc.backup", "a_b", "u1", "x",
   "user-01", "alice@corp", "svc$", "a.b-c_d", "Alice", "0day", "a@b@c"]
def oddNames : List String :=
  ["a$b", "$x", "aLICE", "ALL2x", "-x", ".x", "_x", "sha224", "sudoedit", "Defaults_x",
   "User_Alias2", "include", "a\\xb", "a\\#b", "\\ alice", "alice\\ "]
def escNames : List String :=
  ["al\\ ice", "al\\,ice", "a\\:b", "a\\=b", "a\\!b", "a\\(b\\)", "a\\\\b", "a\\\"b"]
def userName (wild : Bool) : Gen String :=
  oneOf [(10, pickW wild plainNames oddNames), (1, pick escNames)]
def groupName (wild : Bool) : Gen String :=
  pickW wild ["wheel", "staff", "users", "adm", "sudo", "root", "Admins", "domain\\ users"]
    ["g@x", "a\\xb", "1g", "-g"]
def idStr (wild : Bool) : Gen String :=
  pickW wild ["0", "1", "1000", "65534", "4294967295", "007"]
    ["4294967296", "99999999999", "12x", "", "-1", "0x10"]
def userAliases : List String := ["ADMINS", "UA", "U_1", "OPS"]
def runasAliases : List String := ["RA", "OPS_USERS", "DBA"]
def hostAliases : List String := ["SERVERS", "HA", "H_2"]
def cmndAliases : List String := ["SHELLS", "CA", "CMNDS", "C2"]
def reserved : List String := ["ALL", "CHROOT", "CWD", "NOTAFTER", "NOTBEFORE", "ROLE", "TIMEOUT", "TYPE"]
def badAliasNames : List String := ["lower", "1ABC", "A-B", "_A", "Ab", "A.B"]

def quotedUserBody (wild : Bool) : Gen String :=
  pickW wild ["alice", "al ice", "%wheel", "%:Domain Users", "#1000", "Domain Users", "a:b",
      "a=b", "ADMINS", "%#10", "a,b"]
    ["@x", "a\\\"b", "", "+ng", "ALL", "alice bob", "%:#5", "a\\b", "%", "#x"]

def userSpec (wild : Bool) : Gen String := oneOfW wild [
  (10, userName wild),
  (2, do return "#" ++ (← idStr wild)),
  (3, do return "%" ++ (← groupName wild)),
  (1, do return "%#" ++ (← idStr wild)),
  (1, do return "%:" ++ (← groupName wild)),
  (1, do return "%:#" ++ (← idStr wild)),
  (2, do return "\"" ++ (← quotedUserBody wild) ++ "\""),
  (2, pure "ALL"),
  (2, pick userAliases)] [
  (1, do return "+" ++ (← pick ["ng", "netgroup1"])),
  (1, pick (reserved ++ badAliasNames)),
  (1, pick ["%", "%:", "#", "\"", "!"])]

def userList (wild : Bool) : Gen String := listG 1 4 (neg (userSpec wild))

def hostName (wild : Bool) : Gen String :=
  pickW wild ["h1", "h2", "web-01", "db.example.com", "localhost", "host_x", "h1x", "a.1.2.3",
      "1.2.3.4.5", "1234.1.1.1"]
    ["10.0.0.1", "192.168.1.1", "10.0.0.0/8", "256.1.1.1", "1.2.3.4", "1.2.3", "::1",
      "*.example.com", "0.0.0.0", "h\\1", "héllo"]
def hostSpec (wild : Bool) : Gen String := oneOfW wild
  [(10, hostName wild), (3, pure "ALL"), (2, pick hostAliases)]
  [(1, pick (reserved ++ badAliasNames))]
def hostList (wild : Bool) : Gen String := listG 1 3 (neg (hostSpec wild))

def runasUser (wild : Bool) : Gen String := oneOfW wild [
  (6, pick ["root", "alice", "www-data", "postgres"]),
  (2, pure "ALL"), (2, pick runasAliases), (1, do return "#" ++ (← idStr wild)),
  (1, do return "%" ++ (← groupName wild)), (1, do return "%:" ++ (← groupName wild)),
  (1, do return "\"" ++ (← quotedUserBody wild) ++ "\"")]
  [(1, pure "+ng"), (1, pick badAliasNames)]
def runasGroup (wild : Bool) : Gen String := oneOfW wild
  [(6, groupName wild), (2, pure "ALL"), (1, pick runasAliases), (1, do return "#" ++ (← idStr wild))]
  [(1, do return "%" ++ (← groupName wild))]

def runas (wild : Bool) : Gen String := do
  let users ← oneOfW wild [(6, listG 1 3 (neg (runasUser wild))), (2, pure "")]
    [(1, do return (← listG 1 2 (neg (runasUser wild))) ++ ",")]
  let groups ← oneOfW wild [(5, pure none), (3, do return some (← listG 1 2 (neg (runasGroup wild))))]
    [(1, pure (some ""))]
  let inner := match groups with
    | none => users
    | some g => users ++ (if users.isEmpty then "" else " ") ++ ":" ++ (if g.isEmpty then "" else " " ++ g)
  return "(" ++ (← osp) ++ inner ++ (← osp) ++ ")"

/-! ## Tags and options -/

def supportedTags : List String := ["PASSWD", "NOPASSWD", "SETENV", "NOSETENV", "EXEC", "NOEXEC"]
def ignoredTags : List String :=
  ["LOG_INPUT", "NOLOG_INPUT", "LOG_OUTPUT", "NOLOG_OUTPUT", "MAIL", "NOMAIL", "FOLLOW"]
def noopTags : List String := ["NOFOLLOW", "NOINTERCEPT"]
def otherTags : List String := ["INTERCEPT", "FOO", "NOPASS", "passwd"]

def chdirPath (wild : Bool) : Gen String :=
  pickW wild ["/tmp", "*", "~", "~alice/x", "/var/tmp/x", "/a\\ b"]
    ["/a b", "/x*", "relative", "\"/q\"", "~/", "/a\\xb"]

/-- Options (`CWD=`, `APPARMOR_PROFILE=`, ...): C sudo requires them before the tags. -/
def option (wild : Bool) : Gen String := oneOfW wild [
  (2, do return "CWD" ++ (← osp) ++ "=" ++ (← osp) ++ (← chdirPath wild)),
  (1, do return "APPARMOR_PROFILE=" ++ (← pick ["unconfined", "my_profile"]))] [
  (1, do return "CHROOT=" ++ (← chdirPath wild)),
  (1, do return "APPARMOR_PROFILE=" ++ (← pick ["a b", "\"x\""])),
  (1, do return (← pick ["ROLE", "TYPE"]) ++ "=" ++ (← pick ["sysadm_r", "unconfined_t"])),
  (1, do return (← pick ["TIMEOUT", "NOTBEFORE", "NOTAFTER"]) ++ "=" ++
      (← pick ["1h", "20250101000000Z", "5"])),
  (1, do return (← pick ["FOO", "NOPASSWD", "SETENV"]) ++ "=" ++ (← pick ["bar", "1"]))]

def tag (wild : Bool) : Gen String := oneOfW wild [
  (8, do return (← pick supportedTags) ++ (← osp) ++ ":"),
  (3, do return (← pick ignoredTags) ++ (← osp) ++ ":"),
  (1, do return (← pick noopTags) ++ ":")] [
  (1, do return (← pick otherTags) ++ ":"),
  (2, option wild)]

/-- Options, then tags, each followed by whitespace. -/
def tags (wild : Bool) : Gen String := do
  let os ← if wild then listOf 0 1 (option true)
    else oneOf [(5, pure []), (1, do return [← option false])]
  let ts ← listOf 0 3 (tag wild)
  let mut out := ""
  for t in os ++ ts do out := out ++ t ++ (← sp)
  return out

/-! ## Commands -/

def nxPaths : List String := ["bin/ls", "bin/cat", "usr/bin/id", "sbin/reboot", "bin/vi",
  "usr/local/bin/tool", "bin/sh"]

def cmdPath (wild : Bool) : Gen String := oneOfW wild [
  (10, do return nx ++ "/" ++ (← pick nxPaths)),
  (2, do return nx ++ "/" ++ (← pickW wild ["bin/*", "b?n/ls", "[a-c]/x", "**/x", "bin/**",
      "[!x]y", "a]b"] ["***", "a**", "**b", "[", "[]", "[!]", "x[a-", "bin/[[:alpha:]]"])),
  (2, do return nx ++ "/" ++ (← pick ["bin/", "usr/bin/", "/", "bin//", "a/./b", "a/../b", "bin/.."])),
  (2, do return "sudoedit " ++ nx ++ "/etc/" ++ (← pickW wild ["motd", "a"] ["*"])),
  (1, pure "list"),
  (1, do return nx ++ "/" ++ (← pick ["a\\ b", "a\\,b", "a\\:b", "a\\=b", "a\\#b", "a\\\\b",
      "a=b", "a!b", "a\"b", "a(b)"]))] [
  (1, pure "sudoedit"),
  (1, do return (← pick ["sha224", "sha256", "sha384", "sha512"]) ++ ":" ++
      (← pick ["d14a028c2a3a2bc9476102bb288234c415a2b01f828ea62ac5b3e42f",
               "ZmFrZQ==", "x"]) ++ " " ++ nx ++ "/bin/ls"),
  (1, do return "^" ++ nx ++ (← pick ["/bin/.*$", "/x$", "/(a|b)"])),
  (1, pick ["ls", "bin/ls", "./ls", "~/x", "sudoeditx", "listx", "shx"]),
  (1, do return nx ++ "/" ++ (← pick ["a#b", "a\\xb", "a\\"]))]

def argWord (wild : Bool) : Gen String :=
  pickW wild ["-l", "-a", "x", "/etc/passwd", "a=b", "--", "\\,", "a\\:b", "a\\ b", "-",
      "a\\\\", "''"]
    ["\"x\"", "*x", "x?", "[a]", "#x", "a\\xb"]

def args (wild : Bool) : Gen String := oneOfW wild [
  (6, pure ""),
  (3, do return " " ++ (← joinWith sp (← listOf 1 3 (argWord wild)))),
  (2, pure " \"\""),
  (2, do return " " ++ (← joinWith sp (← listOf 1 2 (argWord wild))) ++ " *"),
  (1, pure " *")] [
  (1, do return " " ++ (← pick ["^a.*$", "^$", "a$", "\"\" x", "x \"\""])),
  (1, do return (← sp) ++ (← pick ["-l", "x"]) ++ (← sp))]

def command (wild : Bool) : Gen String := oneOfW wild [
  (10, do
    let p ← cmdPath wild
    if p == "list" || p.startsWith "sudoedit " then return p else return p ++ (← args wild)),
  (3, pure "ALL"), (2, pick cmndAliases)]
  [(1, pick (reserved ++ badAliasNames)), (1, do return "list" ++ (← args true))]

def cmndSpec (wild : Bool) : Gen String := do
  let r ← oneOf [(3, do return (← runas wild) ++ (← sp)), (5, pure "")]
  return r ++ (← tags wild) ++ (← neg (command wild))

def cmndSpecList (wild : Bool) : Gen String := listG 1 4 (cmndSpec wild)

/-! ## Lines -/

def hostGroup (wild : Bool) : Gen String := do
  return (← hostList wild) ++ (← osp) ++ "=" ++ (← osp) ++ (← cmndSpecList wild)

def ruleWith (users hosts cmds : Gen String) (wild : Bool) : Gen String := do
  let first := (← hosts) ++ (← osp) ++ "=" ++ (← osp) ++ (← cmds)
  let more ← oneOf [(6, pure []), (1, listOf 1 2 (hostGroup wild))]
  let groups ← joinWith (sepBy ":") (first :: more)
  return (← users) ++ (← sp) ++ groups

def rule (wild : Bool) : Gen String :=
  ruleWith (userList wild) (hostList wild) (cmndSpecList wild) wild

def aliasDefs (wild : Bool) (kind : String) (names : List String) (member : Gen String) :
    Gen String := do
  let name : Gen String := oneOfW wild [(10, pick names)]
    [(1, pick reserved), (1, pick badAliasNames), (1, pick ["", "A B"])]
  let one : Gen String := do
    return (← name) ++ (← osp) ++ "=" ++ (← osp) ++ (← listG 1 4 (neg member))
  return kind ++ (← sp) ++ (← listG 1 3 one ":")

def aliasLine (wild : Bool) : Gen String := oneOf [
  (2, aliasDefs wild "User_Alias" userAliases (userSpec wild)),
  (2, aliasDefs wild "Runas_Alias" runasAliases (runasUser wild)),
  (2, aliasDefs wild "Host_Alias" hostAliases (hostSpec wild)),
  (2, aliasDefs wild "Cmnd_Alias" cmndAliases (command wild)),
  (1, aliasDefs wild "Cmd_Alias" cmndAliases (command wild))]

/-! ## Defaults -/

def flagNames : List String := ["always_query_group_plugin", "always_set_home", "env_reset",
  "fqdn", "ignore_dot", "mail_badpass", "match_group_by_gid", "use_pty", "visiblepw",
  "pwfeedback", "rootpw", "targetpw", "noexec", "noninteractive_auth", "log_allowed",
  "log_denied", "insults", "setenv", "umask_override", "env_editor"]
def intNames : List String := ["umask", "passwd_tries", "passwd_timeout", "timestamp_timeout"]
def textNames : List String := ["lecture", "mailerpath", "runcwd", "apparmor_profile",
  "secure_path", "verifypw", "timestamp_type", "editor"]
def listNames : List String := ["env_keep", "env_check", "env_delete"]
/-- Names C sudo knows and sudo-rs does not, and names neither knows. -/
def otherNames : List String := ["logfile", "requiretty", "syslog", "lecture_file", "passprompt",
  "badpass_message", "mail_always", "nosuchsetting", "Env_keep", "env-keep"]

/-- A valid value for each integer and text setting. -/
def goodValue (name : String) : Gen String :=
  match name with
  | "umask" => pick ["077", "0022", "0777", "0"]
  | "passwd_tries" => pick ["0", "5", "1000"]
  | "passwd_timeout" | "timestamp_timeout" => pick ["0", "15", "1.5", "2.25", "0.5"]
  | "lecture" => pick ["always", "once", "never"]
  | "verifypw" => pick ["all", "always", "any", "never"]
  | "timestamp_type" => pick ["tty", "ppid"]
  | _ => pick ["/usr/bin:/bin", "\"/usr/bin:/bin\"", "\"a b\"", "a\\ b", "\"a\\\"b\"",
      "unconfined", "\"/usr/bin/vi:/usr/bin/nano\"", "\"x#y\"", "\"a,b\""]

def badValue : Gen String := pick ["1001", "0o22", "abc", "1e3", "ff", "-1", "999999999999999999",
  "9999999999999999999", "1.", ".5", "\"5\"", "\"\"", "x#y", "a,b", "\\#x", "\"tab\there\"",
  "sometimes", "TTY", "always "]

def listValue (wild : Bool) : Gen String :=
  pickW wild ["\"A B C\"", "\"A=1 B\"", "A", "\"LC_*\"", "\"A=x y\"", "PATH", "\"*=()*\""]
    ["A=1", "\"\"", "\"A,B\"", "\"A\\=B\"", "\"A#B\"", "\"A\" B", "\"A\\xB\"", "\" A \"",
      "\"A=\\\"x y\\\"\""]

def setting (wild : Bool) : Gen String := oneOfW wild [
  (6, pick flagNames),
  (4, do return "!" ++ (← osp) ++ (← pick (flagNames ++ listNames ++
      ["lecture", "mailerpath", "runcwd", "apparmor_profile", "secure_path", "verifypw", "umask",
       "passwd_timeout", "timestamp_timeout"]))),
  (8, do
    let n ← pick (intNames ++ textNames)
    return n ++ (← osp) ++ "=" ++ (← osp) ++ (← goodValue n)),
  (4, do return (← pick listNames) ++ (← osp) ++ (← pick ["=", "+=", "-="]) ++ (← osp) ++
      (← listValue wild))] [
  (4, do return (← pick (intNames ++ textNames)) ++ (← osp) ++ "=" ++ (← osp) ++ (← badValue)),
  (1, do return "!" ++ (← pick ["passwd_tries", "timestamp_type", "editor"])),
  (1, do return (← pick (flagNames ++ textNames)) ++ (← pick ["+=", "-="]) ++ "\"A\""),
  (1, do return (← pick flagNames) ++ "=" ++ (← pick ["true", "1"])),
  (1, pick (intNames ++ textNames ++ listNames)),
  (3, do return (← pick otherNames) ++ (← pick ["", "=x", "=\"/var/log/sudo.log\""]))]

/-- A command path without arguments (`Defaults!`). -/
def simpleCmdPath : Gen String := do
  let p ← cmdPath false
  return if p.startsWith "sudoedit " then "sudoedit" else p

def defaultsScope (wild : Bool) : Gen String := oneOfW wild [
  (6, pure ""),
  (2, do return "@" ++ (← listG 1 2 (neg (hostSpec wild)))),
  (2, do return ":" ++ (← listG 1 2 (neg (userSpec wild)))),
  (2, do return ">" ++ (← listG 1 2 (neg (runasUser wild)))),
  (2, do return "!" ++ (← listG 1 2 (neg (oneOf [(5, simpleCmdPath), (1, pick cmndAliases),
      (1, pure "ALL")]))))] [
  (1, do return "!" ++ (← cmdPath true)),
  (1, do return " " ++ (← pick ["@h1", ":alice", "!" ++ nx ++ "/bin/ls", ">root"])),
  (1, pick ["s", "_x", "@", ":", "!", ">"])]

def defaultsLine (wild : Bool) : Gen String := do
  return "Defaults" ++ (← defaultsScope wild) ++ (← sp) ++ (← listG 1 4 (setting wild))

/-! ## Includes and comments -/

def includePath (wild : Bool) : Gen String := oneOfW wild [
  (4, pure (fixture ++ "/include")),
  (1, pure ("\"" ++ fixture ++ "/include\""))] [
  (2, pure (nx ++ "/sudoers.d/x")),
  (1, pure "relative/file"),
  (2, do return "\"" ++ (← pick [nx ++ "/with space", nx ++ "/a\\\"b", nx ++ "/back\\slash", ""]) ++ "\""),
  (1, pure (nx ++ "/with\\ space")),
  (1, pure (nx ++ "/%h")),
  (1, do return nx ++ "/x" ++ (← sp)),
  (1, pure "")]
def includeDirPath (wild : Bool) : Gen String := oneOfW wild [
  (4, pure (fixture ++ "/incdir")),
  (1, pure ("\"" ++ fixture ++ "/incdir\""))] [
  (2, pure (nx ++ "/sudoers.d")),
  (1, pure (fixture ++ "/incdir/"))]

def includeLine (wild : Bool) : Gen String := oneOfW wild [
  (4, do return "@include" ++ (← sp) ++ (← includePath wild)),
  (3, do return "#include" ++ (← sp) ++ (← includePath wild)),
  (3, do return "@includedir" ++ (← sp) ++ (← includeDirPath wild)),
  (2, do return "#includedir" ++ (← sp) ++ (← includeDirPath wild))] [
  (1, do return (← pick ["@include", "#include", "@includedir"])),
  (1, do return (← pick ["@includ", "@foo", "@", "@ include", "#includes", "@Include", "@socket"]) ++
      " " ++ fixture ++ "/include")]

def commentLine (wild : Bool) : Gen String := oneOf [
  (4, do return "#" ++ (← pickW wild ["", " comment", "# double", " Defaults env_reset",
      " alice ALL=ALL", " trailing \\", " é ü", "!x", "#1"] ["1x", "12 ALL = ALL", "4294967296x"])),
  (2, do return (← sp) ++ "# indented"),
  (1, pure "")]

/-- A line of any kind, without its terminator. -/
def anyLine (wild : Bool) : Gen String := oneOf [(8, rule wild), (3, aliasLine wild),
  (3, defaultsLine wild), (1, includeLine wild), (2, commentLine wild)]

/-- A line with a trailing comment now and then. -/
def withComment (g : Gen String) : Gen String := do
  let l ← g
  if ← chance 1 8 then return l ++ (← sp) ++ "# c" else return l

def lines (lo hi : Nat) (g : Gen String) : Gen String := do
  let ls ← listOf lo hi (withComment g)
  return String.join (ls.map (· ++ "\n"))

/-- Mostly valid lines, one in five wild. -/
def mostlyValidLine : Gen String := oneOf [(4, anyLine false), (1, anyLine true)]

/-! ## Categories -/

def catBlank : Gen String := do
  let ls ← listOf 1 5 (oneOf [(2, commentLine false), (1, commentLine true), (2, pure ""), (2, sp),
    (2, rule false)])
  return String.join (ls.map (· ++ "\n"))

/-- A category that is wild in one construct: one line in four is entirely valid. -/
def focus (g : Bool → Gen String) : Gen String :=
  lines 1 3 (oneOf [(3, g true), (1, g false)])

def catUser : Gen String := focus fun w => ruleWith (userList w) (pure "ALL") (pure "ALL") false
def catHost : Gen String := focus fun w => ruleWith (pure "alice") (hostList w) (pure "ALL") false
def catRunas : Gen String := focus fun w => do
  return "alice ALL = " ++ (← runas w) ++ (← osp) ++ (← oneOf [(3, pure "ALL"), (1, cmdPath false),
    (1, do return (← tags false) ++ "ALL")])
def catTag : Gen String := focus fun w => do
  return "alice ALL = " ++ (← oneOf [(1, do return (← runas false) ++ " "), (2, pure "")]) ++
    (← tags w) ++ (← tag w) ++ (← sp) ++ (← command false)
def catCommand : Gen String :=
  focus fun w => ruleWith (pure "alice") (pure "ALL") (cmndSpecList w) false
def catAlias : Gen String := focus aliasLine
def catDefaults : Gen String := focus defaultsLine
def catInclude : Gen String := lines 1 2 (oneOf [(3, includeLine true), (2, includeLine false),
  (1, rule false)])
/-- Valid rules only. -/
def catRule : Gen String := lines 1 4 (rule false)
/-- Valid lines of every kind. -/
def catValid : Gen String := lines 2 8 (anyLine false)
def catMixed : Gen String := lines 3 10 mostlyValidLine

/-- Line continuations (`\` newline) at random points of valid lines, and stray escapes. -/
def catContinuation : Gen String := do
  let ls ← listOf 1 3 (anyLine false)
  let mut out := ""
  for l in ls do
    let cs := l.toList
    let k ← listOf 1 3 (below (cs.length + 1))
    let mut res := ""
    let mut i := 0
    for c in cs do
      if k.contains i then
        res := res ++ (← oneOf [(6, pure "\\\n"), (2, pure " \\\n"), (2, pure "\\\n "),
          (1, pure "\\ \n"), (1, pure "\\\n\\\n"), (1, pure "\\\t\n")])
      res := res.push c
      i := i + 1
    if k.contains cs.length then res := res ++ (← pick ["\\\n", " \\\n", "\\"])
    out := out ++ res ++ "\n"
  if ← chance 1 6 then out := out ++ "\\"
  return out

def wsVariants : List String :=
  [" ", "\t", "  ", "\t\t", "\u000b", "\u000c", "\r", "\u00a0", "\u2028", "\u3000", "\u0085",
   "\u200b", "\ufeff"]

/-- Whitespace variety: every space of a generated line may become another kind of
whitespace (ASCII or not); leading and trailing whitespace; CRLF line ends. -/
def catWhitespace : Gen String := do
  let ls ← listOf 1 3 (anyLine false)
  let mut out := ""
  for l in ls do
    let mut res := ← oneOf [(3, pure ""), (1, sp), (1, pick wsVariants)]
    for c in l.toList do
      if c == ' ' && (← chance 1 3) then res := res ++ (← pick wsVariants)
      else res := res.push c
    res := res ++ (← oneOf [(4, pure ""), (1, sp), (1, pick wsVariants)])
    out := out ++ res ++ (← oneOf [(6, pure "\n"), (1, pure "\r\n")])
  return out

/-- Non-ASCII characters: multi-byte letters, non-ASCII uppercase and digits, control
characters, in every kind of token. -/
def unicodeSamples : List String :=
  ["é", "ü", "ß", "日本", "Σ", "É", "Ⅻ", "ǅ", "𐐀", "٣", "²", "\u0301", "\u200d", "\u0001",
   "\u007f", "\u0085", "\u00a0", "\u2028", "🙂", "\ufeff", "ı", "İ", "ﬀ", "Ω", "ℌ"]

def catUnicode : Gen String := oneOf [
  (3, lines 1 2 (do return (← pick unicodeSamples) ++ (← pick ["", "alice", "x"]) ++ " ALL = ALL")),
  (2, lines 1 2 (do return "alice ALL = " ++ nx ++ "/bin/" ++ (← pick unicodeSamples) ++
      (← pick ["", " arg", " " ++ (← pick unicodeSamples)]))),
  (2, lines 1 2 (do return (← pick ["User_Alias ", "Cmnd_Alias ", "Host_Alias "]) ++
      (← pick unicodeSamples) ++ (← pick ["", "A"]) ++ " = x")),
  (1, lines 1 2 (do return "alice ALL = " ++ (← pick unicodeSamples) ++ (← pick ["", "ALL", "X"]))),
  (2, lines 1 2 (do return "Defaults " ++ (← pick ["secure_path=", "env_keep=\"", "editor=\"",
      "lecture="]) ++ (← pick unicodeSamples) ++ (← pick ["", "\""]))),
  (1, lines 1 2 (do return "\"" ++ (← pick unicodeSamples) ++ "x\" ALL = ALL")),
  (1, lines 1 2 (do return "@include " ++ nx ++ "/" ++ (← pick unicodeSamples))),
  (1, lines 1 2 (do return "# " ++ (← pick unicodeSamples))),
  (2, do
    let l ← anyLine false
    let cs := l.toList
    let i ← below (cs.length + 1)
    return String.ofList (cs.take i) ++ (← pick unicodeSamples) ++ String.ofList (cs.drop i) ++ "\n")]

/-- Missing final newline after every kind of line, and other file ends. -/
def catEof : Gen String := do
  let body ← lines 0 2 (anyLine false)
  let last ← oneOf [(6, anyLine false), (1, pure ""), (1, sp), (1, pure "\\"), (1, pure "# c"),
    (1, do return (← anyLine false) ++ " \\"), (1, do return (← anyLine false) ++ "\\")]
  return body ++ last

/-- `n` characters: ASCII filler, or filler with one multi-byte character at the end, so that
byte and character lengths differ around the limit. -/
def filler (first rest : String) (n : Nat) (multi : Option String) : String :=
  match multi with
  | none => first ++ str (n - 1) rest
  | some m => first ++ str (n - 2) rest ++ m

/-- Tokens around each `MAX_LEN` of `tokens.rs` (lengths in characters; the limit is checked in
bytes, so the multi-byte variants straddle it). -/
def catMaxLen : Gen String := do
  let (limit, mk) ← pick [
    (255, fun (s : String) => s ++ " ALL = ALL"),
    (255, fun s => "alice " ++ s ++ " = ALL"),
    (10, fun s => "#" ++ s ++ " ALL = ALL"),
    (10, fun s => "%#" ++ s ++ " ALL = ALL"),
    (18, fun s => "Defaults passwd_tries=" ++ s),
    (18, fun s => "Defaults timestamp_timeout=" ++ s),
    (255, fun s => "alice ALL = " ++ s),
    (255, fun s => "User_Alias " ++ s ++ " = alice"),
    (1024, fun s => "alice ALL = " ++ s),
    (1024, fun s => "Defaults!" ++ s ++ " noexec"),
    (255, fun s => "Defaults " ++ s),
    (255, fun s => "Defaults env_keep=\"" ++ s ++ "\""),
    (1024, fun s => "Defaults secure_path=" ++ s),
    (1024, fun s => "Defaults secure_path=\"" ++ s ++ "\""),
    (1024, fun s => "@include " ++ s),
    (1024, fun s => "@include \"" ++ s ++ "\""),
    (1024, fun s => "alice ALL = CWD=" ++ s ++ " ALL"),
    (1024, fun s => "\"" ++ s ++ "\" ALL = ALL")]
  let n ← pick [limit - 2, limit - 1, limit, limit + 1, limit + 2]
  let multi ← oneOf [(3, pure none), (1, pure (some "é")), (1, pure (some "日")), (1, pure (some "𐐀"))]
  let probe := mk "PROBE"
  let tok :=
    if probe.startsWith "#" || probe.startsWith "%#" || probe.startsWith "Defaults passwd" ||
        probe.startsWith "Defaults timestamp" then
      filler "1" "1" n none
    else if probe.startsWith "alice ALL = PROBE" && limit == 255 then filler "A" "A" n none
    else if probe.startsWith "User_Alias" then filler "A" "B" n none
    else if limit == 1024 && (probe.startsWith "alice ALL = PROBE" || probe.startsWith "Defaults!") then
      filler (nx ++ "/") "a" (n - nx.length) multi
    else if probe.startsWith "@include" || probe.startsWith "alice ALL = CWD" then
      filler (nx ++ "/") "b" (n - nx.length) multi
    else if probe.startsWith "Defaults PROBE" then filler "a" "b" n none
    else filler "a" "b" n multi
  return mk tok ++ "\n"

/-- Lists around each limit (`Many::LIMIT` = 127, the 127 bounds on tags and on quoted
environment variable lists). -/
def catListLimit : Gen String := do
  let n ← pick [1, 126, 127, 128, 129]
  let items (f : Nat → String) : List String := (List.range n).map f
  let comma := ", "
  let line ← pick [
    comma.intercalate (items (s!"u{·}")) ++ " ALL = ALL",
    "alice " ++ comma.intercalate (items (s!"h{·}")) ++ " = ALL",
    "alice ALL = (" ++ comma.intercalate (items (s!"r{·}")) ++ ") ALL",
    "alice ALL = (root : " ++ comma.intercalate (items (s!"g{·}")) ++ ") ALL",
    "alice ALL = " ++ comma.intercalate (items (s!"{nx}/c{·}")),
    "alice " ++ " : ".intercalate (items (s!"h{·} = ALL")),
    "alice ALL = " ++ String.join (items fun _ => "NOPASSWD: ") ++ "ALL",
    "alice ALL = " ++ String.join (items fun _ => "LOG_INPUT: ") ++ "ALL",
    "User_Alias " ++ " : ".intercalate (items (s!"U{·} = alice")),
    "User_Alias U = " ++ comma.intercalate (items (s!"u{·}")),
    "Defaults " ++ comma.intercalate (items fun i => if i % 2 == 0 then "env_reset" else "!use_pty"),
    "Defaults env_keep=\"" ++ " ".intercalate (items (s!"V{·}")) ++ "\"",
    "Defaults:" ++ comma.intercalate (items (s!"u{·}")) ++ " env_reset"]
  return line ++ "\n"

/-- Command paths in the fixture directory (symbolic links, `..`, `.`, trailing slashes). -/
def catFixture : Gen String := do
  let p ← pick ["bin/tool", "link/tool", "bin/alias", "link/alias", "sub/../bin/tool", "bin/",
    "link/", "bin/..", "bin/.", "missing", "link/../bin/tool", "bin//tool", "bin/tool/", "link",
    "sub/", "bin/*", "link/*", ""]
  let path := fixture ++ "/" ++ p
  let line ← pick ["alice ALL = " ++ path, "alice ALL = " ++ path ++ " -x",
    "Cmnd_Alias C = " ++ path, "Defaults!" ++ path ++ " noexec", "alice ALL = !" ++ path]
  return line ++ "\n"

/-- The inputs of `PLAN.md` section 3.3 and of findings F-P1 to F-P6, verbatim. -/
def knownTexts : List String := [
  "alice ALL = /bin/a, sha224:x \\\nbob ALL = (ALL) ALL\n",
  "alice ALL = /bin/a, /bin/b \\\nbob ALL = (ALL) ALL\n",
  "alice ALL = ALL",
  "alice ALL = ALL ) junk\nbob ALL = ALL\n",
  "alice ALL = ALL, !/usr/bin/su\n",
  "alice ALL = ALL !/usr/bin/su\n",
  "alice ALL = ALL, !sha224:x\n",
  "Runas_Alias NOTROOT = ALL !root\nalice ALL = (NOTROOT) /usr/bin/id\n",
  "Cmnd_Alias SAFE = ALL !/usr/bin/su\nalice ALL = SAFE\n",
  "alice ALL = ALL\nalice ALL !/usr/bin/su\n",
  "Cmnd_Alias SHELLS /usr/bin/su, /usr/bin/bash\nalice ALL = ALL, !SHELLS\n",
  "alice ALL = INTERCEPT: ALL\n",
  "Defaults secure_path=\"/usr/bin\", timestamp_timeout=0, noexec\n",
  "Defaults secure_path=\"/usr/bin\", timestamp_timeout=0, noexec, logfile=\"/var/log/sudo.log\"\n",
  "Defaults secure_path=\"/usr/bin\" timestamp_timeout=0\n",
  "User_Alias U = alice !bob\nU ALL = ALL\n",
  "\"@x\" ALL = ALL\n",
  "alice, \"@x\" ALL = ALL\n",
  "alice ALL = (\"@x\") ALL\n",
  "#4294967296 ALL = ALL\n",
  "#12345678901 ALL = ALL\n",
  "#1 ALL = ALL\n",
  "#x ALL = ALL\n",
  "Defaults env_reset, nosuchsetting, !use_pty\n"]

/-! ## Mutations -/

def structural : List Char := [',', ':', '=', '!', '(', ')', '"', '\\', '#', '@', '%', '+', '\n']
def otherChars : List Char := ['a', 'Z', '0', ' ', '\t', '/', '*', '.', '-', '_', '$', 'é', '\r']

def randChar : Gen Char :=
  oneOf [(7, pick structural), (3, pick otherChars)]

/-- A position, biased towards structural characters. -/
def position (cs : List Char) : Gen Nat := do
  let marks := (List.range cs.length).filter fun i => structural.contains cs[i]!
  if !marks.isEmpty && (← chance 6 10) then pick marks else below (cs.length + 1)

/-- Maximal runs of word characters, and single other characters. -/
def tokenize (cs : List Char) : List (List Char) := Id.run do
  let word (c : Char) := c.isAlphanum || "_.-/$".toList.contains c
  let mut out : Array (List Char) := #[]
  let mut cur : List Char := []
  for c in cs do
    if word c then cur := cur ++ [c]
    else
      if !cur.isEmpty then out := out.push cur
      cur := []
      out := out.push [c]
  if !cur.isEmpty then out := out.push cur
  return out.toList

def mutOps : List String := ["delete-char", "insert-char", "replace-char", "duplicate-char",
  "swap-char", "delete-token", "duplicate-token", "swap-token", "truncate", "splice-lines"]

def mutate (op : String) (t other : String) : Gen String := do
  let cs := t.toList
  let n := cs.length
  match op with
  | "delete-char" => do
    let i ← position cs
    return String.ofList (cs.eraseIdx i)
  | "insert-char" => do
    let i ← position cs
    return String.ofList (cs.take i ++ [← randChar] ++ cs.drop i)
  | "replace-char" => do
    let i ← position cs
    return String.ofList (cs.set i (← randChar))
  | "duplicate-char" => do
    let i ← position cs
    return String.ofList (cs.take (i + 1) ++ cs.drop i)
  | "swap-char" => do
    let i ← below (max n 1)
    if i + 1 < n then return String.ofList (cs.take i ++ [cs[i+1]!, cs[i]!] ++ cs.drop (i + 2))
    else return t
  | "delete-token" => do
    let ts := tokenize cs
    let i ← below (max ts.length 1)
    return String.ofList (ts.eraseIdx i).flatten
  | "duplicate-token" => do
    let ts := tokenize cs
    let i ← below (max ts.length 1)
    return String.ofList (ts.take (i + 1) ++ ts.drop i).flatten
  | "swap-token" => do
    let ts := tokenize cs
    let i ← below (max ts.length 1)
    let j ← below (max ts.length 1)
    if i < ts.length && j < ts.length then
      return String.ofList ((ts.set i ts[j]!).set j ts[i]!).flatten
    else return t
  | "truncate" => do return String.ofList (cs.take (← below (n + 1)))
  | _ => do
    -- splice: a prefix of one line of `t` with a suffix of one line of `other`
    let la := t.splitOn "\n"
    let lb := other.splitOn "\n"
    let i ← below la.length
    let j ← below lb.length
    let a := la[i]!.toList
    let b := lb[j]!.toList
    let line := String.ofList (a.take (← below (a.length + 1)) ++ b.drop (← below (b.length + 1)))
    return "\n".intercalate (la.set i line)

/-! ## The corpus -/

/-- Grammar categories: name and generator. -/
def grammarCats : List (String × Gen String) := [
  ("blank", catBlank), ("user", catUser), ("host", catHost), ("runas", catRunas),
  ("tag", catTag), ("command", catCommand), ("alias", catAlias), ("defaults", catDefaults),
  ("include", catInclude), ("rule", catRule), ("continuation", catContinuation),
  ("whitespace", catWhitespace), ("unicode", catUnicode), ("eof", catEof),
  ("maxlen", catMaxLen), ("listlimit", catListLimit), ("fixture", catFixture),
  ("mixed", catMixed), ("valid", catValid)]

/-- Mutation sources: the grammar categories that generate whole files of valid-looking lines. -/
def mutationSources : List (String × Gen String) :=
  grammarCats.filter fun (n, _) => n != "maxlen" && n != "listlimit"

structure PCase where
  label : String
  text : String
  deriving Inhabited

def PCase.line (c : PCase) : String := c.label ++ " " ++ Quote.quote c.text

/-- Case `i` of grammar category number `ci`. -/
def grammarCase (seed ci i : Nat) : PCase :=
  let (name, g) := grammarCats[ci]!
  { label := s!"{name}:{i}", text := (g.run' (Rng.forCase seed (1000000 * (ci + 1) + i))) }

/-- Case `i` of mutation operator number `oi`: a source text from a random category, mutated
one to three times. -/
def mutationCase (seed oi i : Nat) : PCase :=
  let op := mutOps[oi]!
  let g : Gen (String × String) := do
    let (src, sg) ← pick mutationSources
    let t ← sg
    let other ← (← pick mutationSources).2
    let k ← weighted [(6, 1), (3, 2), (1, 3)]
    let mut out := t
    for _ in [0:k] do out ← mutate op out other
    return (src, out)
  let (src, text) := g.run' (Rng.forCase seed (1000000 * (100 + oi + 1) + i))
  { label := s!"mut.{op}.{src}:{i}", text }

def knownCases : List PCase :=
  (List.range knownTexts.length).map fun i => { label := s!"known:{i}", text := knownTexts[i]! }

/-- The corpus: `n` cases per grammar category and per mutation operator, then the known
inputs. -/
def corpus (seed n : Nat) : Array PCase := Id.run do
  let mut out := #[]
  for ci in [0:grammarCats.length] do
    for i in [0:n] do out := out.push (grammarCase seed ci i)
  for oi in [0:mutOps.length] do
    for i in [0:n] do out := out.push (mutationCase seed oi i)
  for c in knownCases do out := out.push c
  return out

end Differential.ParserCorpus
