import SudoersSpec.Syntax.Ast

/-!
# Tests of the tokens and productions of `tokens.rs` and `ast.rs`

* `example … := by decide`: kernel-checked runs on concrete inputs, including the cases the
  legacy parser cannot reach (opaque messages, the panic of `Command::construct`, the file
  system oracle).
* `#guard` (tests, compiled evaluation): every production on 308 inputs, plus 5 long ones; the
  expected strings are the output of the legacy Rust code at `70fdb56b`, run in a `cfg(test)`
  build of the crate (so every description is `"elem"`, `Descriptions.test`) by a scratch
  test module rendering results in the format below. A case covers only its input.

Test oracles: `CharOracle.latin1`; `canonicalize` maps the paths that resolve on the machine
the expected values were produced on (each to itself) and fails on every other path; glob
compilation follows the error rule of `glob::Pattern::new` (glob 0.3.4); `{:?}` is `q`.
-/

namespace SudoersSpec.Syntax.TestsGrammar

open SudoersSpec SudoersSpec.Syntax Parser

/-! ## Rendering -/

def hexOf (n : Nat) : String := String.ofList (Nat.toDigits 16 n)

/-- A quoted string: printable ASCII but `"` and `\` verbatim, the rest as `\u{h}`. -/
def q (s : String) : String := Id.run do
  let mut out := "\""
  for c in s.toList do
    if c == '"' then out := out ++ "\\\""
    else if c == '\\' then out := out ++ "\\\\"
    else if ' ' ≤ c && c ≤ '~' then out := out.push c
    else out := out ++ "\\u{" ++ hexOf c.toNat ++ "}"
  return out ++ "\""

def lst (f : α → String) (l : List α) : String := "[" ++ ",".intercalate (l.map f) ++ "]"
def pos (p : Nat × Nat) : String := s!"{p.1}:{p.2}"
def span (s : Span) : String := pos s.start ++ "-" ++ pos s.stop
def status : Status → String
  | .fatal sp k => s!"fatal {span sp} {q k.render}"
  | .reject => "reject"
def parsed (f : α → String) : Parsed α → String
  | .ok x => "ok " ++ f x
  | .error e => status e
def ident : Identifier → String
  | .name n => "name:" ++ q n
  | .id n => s!"id:{n}"
def userspec : UserSpecifier → String
  | .user i => s!"user({ident i})"
  | .group i => s!"group({ident i})"
  | .nonunixGroup i => s!"nonunix({ident i})"
def metaR (f : α → String) : Meta α → String
  | .all => "ALL"
  | .alias a => "alias:" ++ q a
  | .only x => s!"only({f x})"
def qual (f : α → String) : Qualified α → String
  | .allow m => s!"allow({f m})"
  | .forbid m => s!"forbid({f m})"
def specR (f : α → String) (s : Spec α) : String := qual (metaR f) s
def speclist (f : α → String) (l : SpecList α) : String := lst (specR f) l
def host (h : Hostname) : String := q h
def chdir : ChDir → String
  | .any => "any"
  | .path p => s!"path({q p})"
def command (c : Command) : String :=
  let a := match c.args with
    | .prefix v => "prefix" ++ lst q v
    | .exact v => "exact" ++ lst q v
  s!"cmd({q c.pattern},{a})"
def modifier : Modifier → String
  | .passwd => "passwd" | .nopasswd => "nopasswd" | .setenv => "setenv"
  | .nosetenv => "nosetenv" | .exec => "exec" | .noexec => "noexec"
  | .cwd c => s!"cwd({chdir c})" | .apparmorProfile p => s!"apparmor({q p})"
  | .ignored s => s!"ignored({span s})" | .noop => "noop"
def cmdspec (c : CommandSpec) : String := s!"cs({lst modifier c.mods},{specR command c.cmd})"
def runas (r : RunAs) : String :=
  s!"runas({speclist userspec r.users};{speclist ident r.groups})"
def opt (f : α → String) : Option α → String
  | none => "none"
  | some x => s!"some({f x})"
def runascmd (x : Option RunAs × CommandSpec) : String := s!"({opt runas x.1},{cmdspec x.2})"
def hostscmds (x : SpecList Hostname × List (Option RunAs × CommandSpec)) : String :=
  s!"({speclist host x.1},{lst runascmd x.2})"
def defn (f : α → String) (d : Def α) : String := s!"def({q d.name},{speclist f d.items})"

/-! ## Test oracles -/

/-- The error rule of `glob::Pattern::new` (glob 0.3.4), with a fuel of the pattern length. -/
def globCheck (cs : Array Char) : Nat → Nat → Option GlobError
  | 0, _ => none
  | fuel + 1, i =>
    let n := cs.size
    if i ≥ n then none else
    match cs[i]! with
    | '?' => globCheck cs fuel (i + 1)
    | '*' =>
      let old := i
      let rec skip (f : Nat) (j : Nat) : Nat := match f with
        | 0 => j
        | f + 1 => if j < n && cs[j]! == '*' then skip f (j + 1) else j
      let i := skip n i
      let count := i - old
      if count > 2 then some ⟨old + 2, "wildcards are either regular `*` or recursive `**`"⟩
      else if count == 2 then
        if i == 2 || cs[i - count - 1]! == '/' then
          if i < n && cs[i]! == '/' then globCheck cs fuel (i + 1)
          else if i == n then none
          else some ⟨i, "recursive wildcards must form a single path component"⟩
        else some ⟨old - 1, "recursive wildcards must form a single path component"⟩
      else globCheck cs fuel i
    | '[' =>
      let findClose (from_ : Nat) : Option Nat := (cs.toList.drop from_).findIdx? (· == ']')
      if i + 4 ≤ n && cs[i + 1]! == '!' then
        match findClose (i + 3) with
        | some j => globCheck cs fuel (i + j + 4)
        | none => some ⟨i, "invalid range pattern"⟩
      else if i + 3 ≤ n && cs[i + 1]! != '!' then
        match findClose (i + 2) with
        | some j => globCheck cs fuel (i + j + 3)
        | none => some ⟨i, "invalid range pattern"⟩
      else some ⟨i, "invalid range pattern"⟩
    | _ => globCheck cs fuel (i + 1)

/-- The paths that resolved when the expected values were produced. -/
def resolving : List String := ["/", "/bin", "/bin/sh", "/tmp", "/usr/bin", "/usr/bin/env"]

def O : Oracles where
  char := CharOracle.latin1
  fs := ⟨fun p => if resolving.contains p then .ok p else .err⟩
  glob := ⟨fun p => globCheck p.toList.toArray (p.length + 1) 0⟩
  fmt := ⟨q, q⟩

def D : Descriptions := .test

def runOn (p : Parser α) (text : String) : Parsed α × Stream := p.run (Stream.ofString text)

def go (p : Parser α) (f : α → String) (input : String) : String :=
  match runOn p input with
  | (r, s) => parsed f r ++ s!" @{pos s.getPos} rest={q (String.ofList s.rest)}"

/-- One production on one input, rendered. -/
def run (prod input : String) : String :=
  match prod with
  | "username" => go (token (usernameToken O)) q input
  | "digits" => go (token digitsU32Token) toString input
  | "numeric" => go (token numericToken) q input
  | "command" => go (token (commandToken O)) command input
  | "metacommand" => go (token (metaToken O.char (commandToken O))) (metaR command) input
  | "simplecommand" => go (token (simpleCommandToken O)) q input
  | "defaultname" => go (token defaultNameToken) q input
  | "envvar" => go (token (envVarToken O.char)) q input
  | "qsp" => go (token (quotedStringParameterToken O.char)) q input
  | "qip" => go (token (quotedIncludePathToken O.char)) q input
  | "includepath" => go (token (includePathToken O.char)) q input
  | "stringparam" => go (token (stringParameterToken O.char)) q input
  | "chdir" => go (token (chDirToken O)) chdir input
  | "unquoted" => go (token (unquotedToken O.char (usernameToken O))) q input
  | "identifier" => go (identifier O D) ident input
  | "metaident" => go (metaIdentifier O D) (metaR ident) input
  | "userspec" => go (userSpecifier O D) userspec input
  | "metauserspec" => go (metaUserSpecifier O D) (metaR userspec) input
  | "userlist" => go (specListUserSpecifier O D) (speclist userspec) input
  | "runas" => go (runAs O D) runas input
  | "metaortag" => go (metaOrTag O D) (metaR modifier) input
  | "commandspec" => go (commandSpec O D) cmdspec input
  | "runascmd" => go (runasCommand O D) runascmd input
  | "permissions" => go (permissions O D) (lst hostscmds) input
  | "defuser" =>
    go (defParser userSpecifierMany D.userSpecifier (metaUserSpecifier O D)) (defn userspec) input
  | "defscmnd" =>
    go (defs D {} D.command (token (metaToken O.char (commandToken O)))) (lst (defn command)) input
  | _ => "UNKNOWN"

/-! ## Kernel-checked examples -/

/-- A simpler oracle for the kernel: nothing resolves, every pattern compiles. -/
def K : Oracles where
  char := CharOracle.latin1
  fs := ⟨fun _ => .err⟩
  glob := ⟨fun _ => none⟩
  fmt := ⟨fun s => "<" ++ s ++ ">", fun s => "[" ++ s ++ "]"⟩

example : runOn (identifier K D) "#123 " = (.ok (.id 123), ⟨[], 1, 6⟩) := by decide
example : runOn (identifier K D) "#4294967296" =
    (.error (.fatal ⟨(1, 2), (1, 12)⟩ .valueTooLarge), ⟨[], 1, 12⟩) := by decide
example : runOn (userSpecifier K D) "%:x" = (.ok (.nonunixGroup (.name "x")), ⟨[], 1, 4⟩) := by
  decide
/-- The quoted user: the text is re-escaped and parsed on a nested stream. -/
example : runOn (userSpecifier K D) "\"al ice\"" = (.ok (.user (.name "al ice")), ⟨[], 1, 9⟩) := by
  decide
/-- F-P3: a quoted text that is not a user rejects after the quote was consumed. -/
example : runOn (userSpecifier K D) "\"@x\"" = (.error .reject, ⟨"\"".toList, 1, 4⟩) := by decide
/-- Inside quotes `%:` is not a non-Unix group: `:` is escaped by `Unquoted<Username>`. -/
example : runOn (userSpecifier K D) "\"%:x\"" = (.ok (.group (.name ":x")), ⟨[], 1, 6⟩) := by
  decide
example : runOn (userSpecifier K D) "+net" =
    (.error (.fatal ⟨(1, 2), (1, 2)⟩ .netgroupsNotSupported), ⟨"net".toList, 1, 2⟩) := by decide
/-- `RunAs`: a fatal error in the user list is discarded (`unwrap_or_default`). -/
example : runOn (runAs K D) "(+x)" =
    (.error (.fatal ⟨(1, 3), (1, 3)⟩ (.expectingSyntax ')' (some 'x'))), ⟨"x)".toList, 1, 3⟩) := by
  decide
example : runOn (runAs K D) "(root:)" =
    (.ok ⟨[.allow (.only (.user (.name "root")))], []⟩, ⟨[], 1, 8⟩) := by decide
example : runOn (metaOrTag K D) "CWD=/tmp" = (.ok (.only (.cwd (.path "/tmp"))), ⟨[], 1, 9⟩) := by
  decide
example : runOn (metaOrTag K D) "NOLOG_INPUT :" =
    (.ok (.only (.ignored ⟨(1, 1), (1, 13)⟩)), ⟨[], 1, 14⟩) := by decide
example : runOn (metaOrTag K D) "ROLE=x" =
    (.error (.fatal ⟨(1, 1), (1, 5)⟩ .selinuxNotSupported), ⟨"=x".toList, 1, 5⟩) := by decide
example : runOn (metaOrTag K D) "FOO=bar" =
    (.error (.fatal ⟨(1, 1), (1, 5)⟩ (.unsupportedModifier "FOO")), ⟨"bar".toList, 1, 5⟩) := by
  decide
example : runOn (commandSpec K D) "NOPASSWD: ALL" = (.ok ⟨[.nopasswd], .allow .all⟩, ⟨[], 1, 14⟩) := by
  decide
example : runOn (commandSpec K D) "PASSWD: /bin/ls *" =
    (.ok ⟨[.passwd], .allow (.only ⟨"/bin/ls", .prefix []⟩)⟩, ⟨[], 1, 18⟩) := by decide
example : runOn (defParser userSpecifierMany D.userSpecifier (metaUserSpecifier K D)) "CWD = x" =
    (.error (.fatal ⟨(1, 1), (1, 5)⟩ (.reservedAliasName "CWD")), ⟨"= x".toList, 1, 5⟩) := by
  decide

/-- `Command::construct`: the argument pattern. -/
example : Command.construct K "/bin/ls a \"\"".toList = .ok ⟨"/bin/ls", .exact ["a"]⟩ := by decide
example : Command.construct K "/bin/ls * *".toList = .error .globInCommandArguments := by decide
example : Command.construct K "list x".toList = .error .listTakesNoArguments := by decide
example : Command.construct K "/bin/ls ^a".toList = .error .regularExpressionsNotSupported := by
  decide
/-- `cmd_iter.next().unwrap()` with no word: the panic marker. -/
example : Command.construct K " \t".toList = .error .unwrapNone := by decide

/-- The file-system oracle: a canonical path replaces the command, `/*` is put back for a
directory, a non-UTF-8 canonical path is an error. -/
def F : Oracles :=
  { K with fs := ⟨fun p => if p == "/bin/sh" then .ok "/usr/bin/bash"
      else if p == "/bin" then .ok "/usr/bin" else if p == "/weird" then .okNonUtf8 else .err⟩ }
example : SimpleCommand.construct F "/bin/sh".toList = .ok "/usr/bin/bash" := by decide
example : SimpleCommand.construct F "/bin/".toList = .ok "/usr/bin/*" := by decide
example : SimpleCommand.construct F "/weird".toList = .error .nonUtf8Filesystem := by decide
example : SimpleCommand.construct F "sudoedit".toList = .ok "sudoedit" := by decide
/-- The glob oracle and the rendering of `glob::PatternError`. -/
example : SimpleCommand.construct { K with glob := ⟨fun _ => some ⟨3, "invalid range pattern"⟩⟩ }
    "/a[".toList =
    .error (.wildcardPatternError "Pattern syntax error near position 3: invalid range pattern") := by
  decide

/-- The opaque `Debug` texts of `SudoString::new` and `SudoPath::try_from`. -/
example : Username.construct K ['a', '\x00'] =
    .error (.sudoStringValidation "Unexpected null character in input: <a\x00>") := by decide
example : ChDir.construct K ['/', '\x00'] =
    .error (.sudoPathValidation "Unexpected null character in input: [/\x00]") := by decide
example : Username.construct K "a$b".toList = .error .embeddedDollarInUsername := by decide
example : Username.construct K "a$".toList = .ok "a$" := by decide

/-! ## Comparison with the legacy Rust code (`#guard` tests) -/

#guard run "username" "alice" ==
  "ok \"alice\" @1:6 rest=\"\""
#guard run "username" "alice bob" ==
  "ok \"alice\" @1:6 rest=\" bob\""
#guard run "username" "a$" ==
  "ok \"a$\" @1:3 rest=\"\""
#guard run "username" "a$b" ==
  "fatal 1:1-1:4 \"embedded $ in username\" @1:4 rest=\"\""
#guard run "username" "$" ==
  "ok \"$\" @1:2 rest=\"\""
#guard run "username" "@a" ==
  "reject @1:1 rest=\"@a\""
#guard run "username" "a@b" ==
  "ok \"a@b\" @1:4 rest=\"\""
#guard run "username" "a\\ b" ==
  "ok \"a b\" @1:5 rest=\"\""
#guard run "username" "a\\,b" ==
  "ok \"a,b\" @1:5 rest=\"\""
#guard run "username" "a\\x" ==
  "fatal 1:3-1:3 \"illegal escape sequence\" @1:3 rest=\"x\""
#guard run "username" "a\\\nb" ==
  "ok \"a\" @2:1 rest=\"b\""
#guard run "username" "\\\na" ==
  "reject @2:1 rest=\"a\""
#guard run "username" "a.b-c_d" ==
  "ok \"a.b-c_d\" @1:8 rest=\"\""
#guard run "username" "Élodie" ==
  "ok \"\\u{c9}lodie\" @1:7 rest=\"\""
#guard run "username" "1abc" ==
  "ok \"1abc\" @1:5 rest=\"\""
#guard run "username" "-x" ==
  "ok \"-x\" @1:3 rest=\"\""
#guard run "username" (String.ofList (List.replicate 256 'a')) ==
  "fatal 1:257-1:257 \"token exceeds maximum length\" @1:257 rest=\"\""

#guard run "digits" "0" ==
  "ok 0 @1:2 rest=\"\""
#guard run "digits" "123" ==
  "ok 123 @1:4 rest=\"\""
#guard run "digits" "4294967295" ==
  "ok 4294967295 @1:11 rest=\"\""
#guard run "digits" "4294967296" ==
  "fatal 1:1-1:11 \"value too large\" @1:11 rest=\"\""
#guard run "digits" "12345678901" ==
  "fatal 1:12-1:12 \"token exceeds maximum length\" @1:12 rest=\"\""
#guard run "digits" "x" ==
  "reject @1:1 rest=\"x\""
#guard run "digits" "007" ==
  "ok 7 @1:4 rest=\"\""

#guard run "numeric" "1f" ==
  "ok \"1f\" @1:3 rest=\"\""
#guard run "numeric" "0.5" ==
  "ok \"0.5\" @1:4 rest=\"\""
#guard run "numeric" "1234567890abcdef12" ==
  "ok \"1234567890abcdef12\" @1:19 rest=\"\""
#guard run "numeric" "1234567890abcdef123" ==
  "fatal 1:20-1:20 \"token exceeds maximum length\" @1:20 rest=\"\""
#guard run "numeric" "g" ==
  "reject @1:1 rest=\"g\""
#guard run "numeric" "." ==
  "ok \".\" @1:2 rest=\"\""

#guard run "command" "/bin/ls" ==
  "ok cmd(\"/bin/ls\",prefix[]) @1:8 rest=\"\""
#guard run "command" "/bin/ls -l" ==
  "ok cmd(\"/bin/ls\",exact[\"-l\"]) @1:11 rest=\"\""
#guard run "command" "/bin/ls *" ==
  "ok cmd(\"/bin/ls\",prefix[]) @1:10 rest=\"\""
#guard run "command" "/bin/ls a *" ==
  "ok cmd(\"/bin/ls\",prefix[\"a\"]) @1:12 rest=\"\""
#guard run "command" "/bin/ls * *" ==
  "fatal 1:1-1:12 \"glob patterns are not allowed in command arguments\" @1:12 rest=\"\""
#guard run "command" "/bin/ls \"\"" ==
  "ok cmd(\"/bin/ls\",exact[]) @1:11 rest=\"\""
#guard run "command" "/bin/ls a \"\"" ==
  "ok cmd(\"/bin/ls\",exact[\"a\"]) @1:13 rest=\"\""
#guard run "command" "/bin/ls ^a" ==
  "fatal 1:1-1:11 \"regular expressions are not supported\" @1:11 rest=\"\""
#guard run "command" "/bin/ls a ^b" ==
  "ok cmd(\"/bin/ls\",exact[\"a\",\"^b\"]) @1:13 rest=\"\""
#guard run "command" "/bin/ls a*" ==
  "fatal 1:1-1:11 \"glob patterns are not allowed in command arguments\" @1:11 rest=\"\""
#guard run "command" "/bin/ls a?" ==
  "fatal 1:1-1:11 \"glob patterns are not allowed in command arguments\" @1:11 rest=\"\""
#guard run "command" "/bin/ls [a]" ==
  "fatal 1:1-1:12 \"glob patterns are not allowed in command arguments\" @1:12 rest=\"\""
#guard run "command" "list" ==
  "ok cmd(\"list\",prefix[]) @1:5 rest=\"\""
#guard run "command" "list x" ==
  "fatal 1:1-1:7 \"list does not take arguments\" @1:7 rest=\"\""
#guard run "command" "list *" ==
  "ok cmd(\"list\",prefix[]) @1:7 rest=\"\""
#guard run "command" "list \"\"" ==
  "fatal 1:1-1:8 \"list does not take arguments\" @1:8 rest=\"\""
#guard run "command" "sudoedit /etc/x" ==
  "ok cmd(\"sudoedit\",exact[\"/etc/x\"]) @1:16 rest=\"\""
#guard run "command" "sha224:abc" ==
  "fatal 1:1-1:7 \"digest specifications are not supported\" @1:7 rest=\":abc\""
#guard run "command" "ls" ==
  "fatal 1:1-1:3 \"fully qualified path needed\" @1:3 rest=\"\""
#guard run "command" "/bin/" ==
  "ok cmd(\"/bin/*\",prefix[]) @1:6 rest=\"\""
#guard run "command" "/" ==
  "ok cmd(\"/*\",prefix[]) @1:2 rest=\"\""
#guard run "command" "/bin/a***" ==
  "fatal 1:1-1:10 \"wildcard pattern error Pattern syntax error near position 8: wildcards are either regular `*` or recursive `**`\" @1:10 rest=\"\""
#guard run "command" "/bin/**x" ==
  "fatal 1:1-1:9 \"wildcard pattern error Pattern syntax error near position 7: recursive wildcards must form a single path component\" @1:9 rest=\"\""
#guard run "command" "/bin/[" ==
  "fatal 1:1-1:7 \"wildcard pattern error Pattern syntax error near position 5: invalid range pattern\" @1:7 rest=\"\""
#guard run "command" "/bin/[!x]" ==
  "ok cmd(\"/bin/[!x]\",prefix[]) @1:10 rest=\"\""
#guard run "command" "/bin/a\\,b" ==
  "ok cmd(\"/bin/a,b\",prefix[]) @1:10 rest=\"\""
#guard run "command" "/bin/a\\ b c" ==
  "ok cmd(\"/bin/a\",exact[\"b\",\"c\"]) @1:12 rest=\"\""
#guard run "command" "/bin/ls\t-l" ==
  "ok cmd(\"/bin/ls\",exact[\"-l\"]) @1:11 rest=\"\""
#guard run "command" "/bin/ls  -l  " ==
  "ok cmd(\"/bin/ls\",exact[\"-l\"]) @1:14 rest=\"\""
#guard run "command" "/bin/a=b" ==
  "ok cmd(\"/bin/a=b\",prefix[]) @1:9 rest=\"\""
#guard run "command" "/bin/a\\=b" ==
  "ok cmd(\"/bin/a=b\",prefix[]) @1:10 rest=\"\""
#guard run "command" "/nonexistent/dir/" ==
  "ok cmd(\"/nonexistent/dir/*\",prefix[]) @1:18 rest=\"\""
#guard run "command" "/tmp" ==
  "ok cmd(\"/tmp\",prefix[]) @1:5 rest=\"\""
#guard run "command" "/tmp/" ==
  "ok cmd(\"/tmp/*\",prefix[]) @1:6 rest=\"\""
#guard run "command" "/bin/sh" ==
  "ok cmd(\"/bin/sh\",prefix[]) @1:8 rest=\"\""
#guard run "command" "/usr/bin/env x" ==
  "ok cmd(\"/usr/bin/env\",exact[\"x\"]) @1:15 rest=\"\""
#guard run "command" "/bin/ls #x" ==
  "ok cmd(\"/bin/ls\",prefix[]) @1:9 rest=\"#x\""
#guard run "command" "s" ==
  "fatal 1:1-1:2 \"fully qualified path needed\" @1:2 rest=\"\""
#guard run "command" "l" ==
  "fatal 1:1-1:2 \"fully qualified path needed\" @1:2 rest=\"\""
#guard run "command" "sudoeditor" ==
  "fatal 1:1-1:11 \"fully qualified path needed\" @1:11 rest=\"\""

#guard run "metacommand" "ALL" ==
  "ok ALL @1:4 rest=\"\""
#guard run "metacommand" "ALIAS_1" ==
  "ok alias:\"ALIAS_1\" @1:8 rest=\"\""
#guard run "metacommand" "/bin/ls" ==
  "ok only(cmd(\"/bin/ls\",prefix[])) @1:8 rest=\"\""
#guard run "metacommand" "ALL " ==
  "ok ALL @1:5 rest=\"\""
#guard run "metacommand" "SHELLS x" ==
  "fatal 1:1-1:9 \"fully qualified path needed\" @1:9 rest=\"\""
#guard run "metacommand" "Sx" ==
  "fatal 1:1-1:3 \"fully qualified path needed\" @1:3 rest=\"\""

#guard run "simplecommand" "/bin/ls" ==
  "ok \"/bin/ls\" @1:8 rest=\"\""
#guard run "simplecommand" "/bin/ls -l" ==
  "ok \"/bin/ls\" @1:8 rest=\" -l\""
#guard run "simplecommand" "list" ==
  "ok \"list\" @1:5 rest=\"\""
#guard run "simplecommand" "sha1" ==
  "fatal 1:1-1:5 \"digest specifications are not supported\" @1:5 rest=\"\""
#guard run "simplecommand" "/a**/b" ==
  "fatal 1:1-1:7 \"wildcard pattern error Pattern syntax error near position 1: recursive wildcards must form a single path component\" @1:7 rest=\"\""
#guard run "simplecommand" "/a/**/b" ==
  "ok \"/a/**/b\" @1:8 rest=\"\""
#guard run "simplecommand" "/a/**" ==
  "ok \"/a/**\" @1:6 rest=\"\""
#guard run "simplecommand" "/a/***" ==
  "fatal 1:1-1:7 \"wildcard pattern error Pattern syntax error near position 5: wildcards are either regular `*` or recursive `**`\" @1:7 rest=\"\""
#guard run "simplecommand" "sudoedit" ==
  "ok \"sudoedit\" @1:9 rest=\"\""

#guard run "defaultname" "env_reset" ==
  "ok \"env_reset\" @1:10 rest=\"\""
#guard run "defaultname" "env-reset" ==
  "ok \"env\" @1:4 rest=\"-reset\""
#guard run "defaultname" "Env_1" ==
  "ok \"Env_1\" @1:6 rest=\"\""
#guard run "defaultname" "_" ==
  "ok \"_\" @1:2 rest=\"\""

#guard run "envvar" "PATH" ==
  "ok \"PATH\" @1:5 rest=\"\""
#guard run "envvar" "LC_*" ==
  "ok \"LC_*\" @1:5 rest=\"\""
#guard run "envvar" "A=B" ==
  "ok \"A\" @1:2 rest=\"=B\""
#guard run "envvar" "A\\=B" ==
  "ok \"A=B\" @1:5 rest=\"\""
#guard run "envvar" "A\\#B" ==
  "ok \"A#B\" @1:5 rest=\"\""
#guard run "envvar" "A\"B" ==
  "ok \"A\" @1:2 rest=\"\\\"B\""
#guard run "envvar" "A,B" ==
  "ok \"A\" @1:2 rest=\",B\""
#guard run "envvar" "A B" ==
  "ok \"A\" @1:2 rest=\" B\""
#guard run "envvar" "\\x" ==
  "fatal 1:2-1:2 \"illegal escape sequence\" @1:2 rest=\"x\""
#guard run "envvar" "Ü" ==
  "ok \"\\u{dc}\" @1:2 rest=\"\""

#guard run "qsp" "hello world" ==
  "ok \"hello world\" @1:12 rest=\"\""
#guard run "qsp" "a\\\"b" ==
  "ok \"a\\\"b\" @1:5 rest=\"\""
#guard run "qsp" "a\\\\b" ==
  "ok \"a\\\\b\" @1:5 rest=\"\""
#guard run "qsp" "a\"b" ==
  "ok \"a\" @1:2 rest=\"\\\"b\""
#guard run "qsp" "a\\nb" ==
  "fatal 1:3-1:3 \"illegal escape sequence\" @1:3 rest=\"nb\""
#guard run "qsp" "a\\x" ==
  "fatal 1:3-1:3 \"illegal escape sequence\" @1:3 rest=\"x\""
#guard run "qsp" "a\tb" ==
  "ok \"a\" @1:2 rest=\"\\u{9}b\""
#guard run "qsp" "" ==
  "reject @1:1 rest=\"\""

#guard run "qip" "/etc/a b" ==
  "ok \"/etc/a b\" @1:9 rest=\"\""
#guard run "qip" "/etc/a\\b" ==
  "ok \"/etc/a\\\\b\" @1:9 rest=\"\""
#guard run "qip" "/etc/a\\\"b" ==
  "ok \"/etc/a\\\"b\" @1:10 rest=\"\""
#guard run "qip" "a\"b" ==
  "ok \"a\" @1:2 rest=\"\\\"b\""
#guard run "qip" "\\\nx" ==
  "ok \"\\u{a}x\" @2:2 rest=\"\""

#guard run "includepath" "/etc/sudoers.d" ==
  "ok \"/etc/sudoers.d\" @1:15 rest=\"\""
#guard run "includepath" "/etc/a\\ b" ==
  "ok \"/etc/a b\" @1:10 rest=\"\""
#guard run "includepath" "/etc/a b" ==
  "ok \"/etc/a\" @1:7 rest=\" b\""
#guard run "includepath" "/etc/a\\\"b" ==
  "ok \"/etc/a\\\"b\" @1:10 rest=\"\""
#guard run "includepath" "/etc/a#b" ==
  "ok \"/etc/a#b\" @1:9 rest=\"\""
#guard run "includepath" "/etc/a\\x" ==
  "fatal 1:8-1:8 \"illegal escape sequence\" @1:8 rest=\"x\""

#guard run "stringparam" "/usr/bin" ==
  "ok \"/usr/bin\" @1:9 rest=\"\""
#guard run "stringparam" "a b" ==
  "ok \"a\" @1:2 rest=\" b\""
#guard run "stringparam" "a,b" ==
  "ok \"a\" @1:2 rest=\",b\""
#guard run "stringparam" "a#b" ==
  "ok \"a\" @1:2 rest=\"#b\""
#guard run "stringparam" "a\\,b" ==
  "ok \"a,b\" @1:5 rest=\"\""
#guard run "stringparam" "a\\ b" ==
  "ok \"a b\" @1:5 rest=\"\""
#guard run "stringparam" "a\"b" ==
  "ok \"a\" @1:2 rest=\"\\\"b\""
#guard run "stringparam" "a=b" ==
  "ok \"a=b\" @1:4 rest=\"\""

#guard run "chdir" "/tmp" ==
  "ok path(\"/tmp\") @1:5 rest=\"\""
#guard run "chdir" "*" ==
  "ok any @1:2 rest=\"\""
#guard run "chdir" "~" ==
  "ok path(\"~\") @1:2 rest=\"\""
#guard run "chdir" "~alice/x" ==
  "ok path(\"~alice/x\") @1:9 rest=\"\""
#guard run "chdir" "/a*" ==
  "fatal 1:1-1:4 \"path cannot contain '*'\" @1:4 rest=\"\""
#guard run "chdir" "**" ==
  "fatal 1:1-1:3 \"path cannot contain '*'\" @1:3 rest=\"\""
#guard run "chdir" "/a\\ b" ==
  "ok path(\"/a b\") @1:6 rest=\"\""
#guard run "chdir" "x" ==
  "reject @1:1 rest=\"x\""
#guard run "chdir" "/a b" ==
  "ok path(\"/a\") @1:3 rest=\" b\""
#guard run "chdir" "*x" ==
  "fatal 1:1-1:3 \"path cannot contain '*'\" @1:3 rest=\"\""

#guard run "unquoted" "alice" ==
  "ok \"alice\" @1:6 rest=\"\""
#guard run "unquoted" "a b" ==
  "ok \"a\\\\ b\" @1:4 rest=\"\""
#guard run "unquoted" "a,b" ==
  "ok \"a\\\\,b\" @1:4 rest=\"\""
#guard run "unquoted" "a\\b" ==
  "ok \"a\\\\\\\\b\" @1:4 rest=\"\""
#guard run "unquoted" "a\"b" ==
  "ok \"a\" @1:2 rest=\"\\\"b\""
#guard run "unquoted" "a(b)" ==
  "ok \"a\\\\(b\\\\)\" @1:5 rest=\"\""
#guard run "unquoted" "" ==
  "reject @1:1 rest=\"\""

#guard run "identifier" "alice" ==
  "ok name:\"alice\" @1:6 rest=\"\""
#guard run "identifier" "#0" ==
  "ok id:0 @1:3 rest=\"\""
#guard run "identifier" "#123" ==
  "ok id:123 @1:5 rest=\"\""
#guard run "identifier" "#4294967296" ==
  "fatal 1:2-1:12 \"value too large\" @1:12 rest=\"\""
#guard run "identifier" "#" ==
  "fatal 1:2-1:2 \"expected elem\" @1:2 rest=\"\""
#guard run "identifier" "#x" ==
  "fatal 1:2-1:2 \"expected elem\" @1:2 rest=\"x\""
#guard run "identifier" "# 1" ==
  "fatal 1:2-1:2 \"expected elem\" @1:2 rest=\" 1\""
#guard run "identifier" "%x" ==
  "reject @1:1 rest=\"%x\""
#guard run "identifier" "" ==
  "reject @1:1 rest=\"\""
#guard run "identifier" "\\\nalice" ==
  "reject @2:1 rest=\"alice\""
#guard run "identifier" "#12 " ==
  "ok id:12 @1:5 rest=\"\""
#guard run "identifier" "alice " ==
  "ok name:\"alice\" @1:7 rest=\"\""

#guard run "metaident" "ALL" ==
  "ok ALL @1:4 rest=\"\""
#guard run "metaident" "ADMINS" ==
  "ok alias:\"ADMINS\" @1:7 rest=\"\""
#guard run "metaident" "alice" ==
  "ok only(name:\"alice\") @1:6 rest=\"\""
#guard run "metaident" "#5" ==
  "ok only(id:5) @1:3 rest=\"\""
#guard run "metaident" "#" ==
  "fatal 1:2-1:2 \"expected elem\" @1:2 rest=\"\""
#guard run "metaident" "Bob" ==
  "ok only(name:\"Bob\") @1:4 rest=\"\""
#guard run "metaident" "\\\n#5" ==
  "ok only(id:5) @2:3 rest=\"\""

#guard run "userspec" "alice" ==
  "ok user(name:\"alice\") @1:6 rest=\"\""
#guard run "userspec" "%wheel" ==
  "ok group(name:\"wheel\") @1:7 rest=\"\""
#guard run "userspec" "%:nonunix" ==
  "ok nonunix(name:\"nonunix\") @1:10 rest=\"\""
#guard run "userspec" "%#10" ==
  "ok group(id:10) @1:5 rest=\"\""
#guard run "userspec" "%" ==
  "fatal 1:2-1:2 \"expected elem\" @1:2 rest=\"\""
#guard run "userspec" "%:" ==
  "fatal 1:3-1:3 \"expected elem\" @1:3 rest=\"\""
#guard run "userspec" "+net" ==
  "fatal 1:2-1:2 \"netgroups are not supported yet\" @1:2 rest=\"net\""
#guard run "userspec" "\"alice\"" ==
  "ok user(name:\"alice\") @1:8 rest=\"\""
#guard run "userspec" "\"al ice\"" ==
  "ok user(name:\"al ice\") @1:9 rest=\"\""
#guard run "userspec" "\"a,b\"" ==
  "ok user(name:\"a,b\") @1:6 rest=\"\""
#guard run "userspec" "\"%wheel\"" ==
  "ok group(name:\"wheel\") @1:9 rest=\"\""
#guard run "userspec" "\"@x\"" ==
  "reject @1:4 rest=\"\\\"\""
#guard run "userspec" "\"a+b\"" ==
  "ok user(name:\"a\") @1:6 rest=\"\""
#guard run "userspec" "\"alice" ==
  "fatal 1:7-1:7 \"expecting '\\\"' but found 'EOF'\" @1:7 rest=\"\""
#guard run "userspec" "\"\" x" ==
  "fatal 1:2-1:2 \"expected elem\" @1:2 rest=\"\\\" x\""
#guard run "userspec" "\"#12\"" ==
  "ok user(id:12) @1:6 rest=\"\""
#guard run "userspec" "\"a\\b\"" ==
  "ok user(name:\"a\\\\b\") @1:6 rest=\"\""
#guard run "userspec" "@x" ==
  "reject @1:1 rest=\"@x\""
#guard run "userspec" "#5" ==
  "ok user(id:5) @1:3 rest=\"\""
#guard run "userspec" "\"%:x y\"" ==
  "ok group(name:\":x y\") @1:8 rest=\"\""

#guard run "metauserspec" "ALL" ==
  "ok ALL @1:4 rest=\"\""
#guard run "metauserspec" "ADMINS" ==
  "ok alias:\"ADMINS\" @1:7 rest=\"\""
#guard run "metauserspec" "alice" ==
  "ok only(user(name:\"alice\")) @1:6 rest=\"\""
#guard run "metauserspec" "%wheel" ==
  "ok only(group(name:\"wheel\")) @1:7 rest=\"\""
#guard run "metauserspec" "\"ALL\"" ==
  "ok only(user(name:\"ALL\")) @1:6 rest=\"\""
#guard run "metauserspec" "\"bob\"" ==
  "ok only(user(name:\"bob\")) @1:6 rest=\"\""
#guard run "metauserspec" "#7" ==
  "ok only(user(id:7)) @1:3 rest=\"\""
#guard run "metauserspec" "+x" ==
  "fatal 1:2-1:2 \"netgroups are not supported yet\" @1:2 rest=\"x\""
#guard run "metauserspec" "\\\n%x" ==
  "ok only(group(name:\"x\")) @2:3 rest=\"\""

#guard run "userlist" "alice, bob" ==
  "ok [allow(only(user(name:\"alice\"))),allow(only(user(name:\"bob\")))] @1:11 rest=\"\""
#guard run "userlist" "alice,%wheel,!bob" ==
  "ok [allow(only(user(name:\"alice\"))),allow(only(group(name:\"wheel\"))),forbid(only(user(name:\"bob\")))] @1:18 rest=\"\""
#guard run "userlist" "!!alice" ==
  "ok [allow(only(user(name:\"alice\")))] @1:8 rest=\"\""
#guard run "userlist" "," ==
  "reject @1:1 rest=\",\""
#guard run "userlist" "alice," ==
  "fatal 1:7-1:7 \"expected elem\" @1:7 rest=\"\""
#guard run "userlist" "ALL, !root" ==
  "ok [allow(ALL),forbid(only(user(name:\"root\")))] @1:11 rest=\"\""
#guard run "userlist" (",".intercalate (List.replicate 127 "a")) ==
  "ok [" ++ ",".intercalate (List.replicate 127 "allow(only(user(name:\"a\")))") ++
    "] @1:254 rest=\"\""
#guard run "userlist" (",".intercalate (List.replicate 128 "a")) ==
  "fatal 1:255-1:255 \"too many items in list\" @1:255 rest=\"a\""

#guard run "runas" "(root)" ==
  "ok runas([allow(only(user(name:\"root\")))];[]) @1:7 rest=\"\""
#guard run "runas" "(root:wheel)" ==
  "ok runas([allow(only(user(name:\"root\")))];[allow(only(name:\"wheel\"))]) @1:13 rest=\"\""
#guard run "runas" "(:wheel)" ==
  "ok runas([];[allow(only(name:\"wheel\"))]) @1:9 rest=\"\""
#guard run "runas" "()" ==
  "ok runas([];[]) @1:3 rest=\"\""
#guard run "runas" "(root,bob : wheel, staff)" ==
  "ok runas([allow(only(user(name:\"root\"))),allow(only(user(name:\"bob\")))];[allow(only(name:\"wheel\")),allow(only(name:\"staff\"))]) @1:26 rest=\"\""
#guard run "runas" "(ALL:ALL)" ==
  "ok runas([allow(ALL)];[allow(ALL)]) @1:10 rest=\"\""
#guard run "runas" "(root" ==
  "fatal 1:6-1:6 \"expecting ')' but found 'EOF'\" @1:6 rest=\"\""
#guard run "runas" "(root:" ==
  "fatal 1:7-1:7 \"expecting ')' but found 'EOF'\" @1:7 rest=\"\""
#guard run "runas" "(root:)" ==
  "ok runas([allow(only(user(name:\"root\")))];[]) @1:8 rest=\"\""
#guard run "runas" "(+x)" ==
  "fatal 1:3-1:3 \"expecting ')' but found 'x'\" @1:3 rest=\"x)\""
#guard run "runas" "(+x:wheel)" ==
  "fatal 1:3-1:3 \"expecting ')' but found 'x'\" @1:3 rest=\"x:wheel)\""
#guard run "runas" "(,)" ==
  "fatal 1:2-1:2 \"expecting ')' but found ','\" @1:2 rest=\",)\""
#guard run "runas" "( root )" ==
  "ok runas([allow(only(user(name:\"root\")))];[]) @1:9 rest=\"\""
#guard run "runas" "(root:#5)" ==
  "ok runas([allow(only(user(name:\"root\")))];[allow(only(id:5))]) @1:10 rest=\"\""
#guard run "runas" "(%x)" ==
  "ok runas([allow(only(group(name:\"x\")))];[]) @1:5 rest=\"\""
#guard run "runas" "(!root)" ==
  "ok runas([forbid(only(user(name:\"root\")))];[]) @1:8 rest=\"\""
#guard run "runas" "x" ==
  "reject @1:1 rest=\"x\""
#guard run "runas" "(root:+x)" ==
  "fatal 1:7-1:7 \"expecting ')' but found '+'\" @1:7 rest=\"+x)\""
#guard run "runas" "(root:,)" ==
  "fatal 1:7-1:7 \"expecting ')' but found ','\" @1:7 rest=\",)\""
#guard run "runas" "(root) " ==
  "ok runas([allow(only(user(name:\"root\")))];[]) @1:8 rest=\"\""
#guard run "runas" "(root:wheel" ==
  "fatal 1:12-1:12 \"expecting ')' but found 'EOF'\" @1:12 rest=\"\""

#guard run "metaortag" "NOPASSWD:" ==
  "ok only(nopasswd) @1:10 rest=\"\""
#guard run "metaortag" "NOPASSWD :" ==
  "ok only(nopasswd) @1:11 rest=\"\""
#guard run "metaortag" "NOPASSWD" ==
  "fatal 1:9-1:9 \"expecting ':' but found 'EOF'\" @1:9 rest=\"\""
#guard run "metaortag" "PASSWD:" ==
  "ok only(passwd) @1:8 rest=\"\""
#guard run "metaortag" "EXEC:" ==
  "ok only(exec) @1:6 rest=\"\""
#guard run "metaortag" "NOEXEC:" ==
  "ok only(noexec) @1:8 rest=\"\""
#guard run "metaortag" "SETENV:" ==
  "ok only(setenv) @1:8 rest=\"\""
#guard run "metaortag" "NOSETENV:" ==
  "ok only(nosetenv) @1:10 rest=\"\""
#guard run "metaortag" "CWD=/tmp" ==
  "ok only(cwd(path(\"/tmp\"))) @1:9 rest=\"\""
#guard run "metaortag" "CWD=*" ==
  "ok only(cwd(any)) @1:6 rest=\"\""
#guard run "metaortag" "CWD = /tmp" ==
  "ok only(cwd(path(\"/tmp\"))) @1:11 rest=\"\""
#guard run "metaortag" "CWD=x" ==
  "fatal 1:5-1:5 \"expected elem\" @1:5 rest=\"x\""
#guard run "metaortag" "CWD=/a*" ==
  "fatal 1:5-1:8 \"path cannot contain '*'\" @1:8 rest=\"\""
#guard run "metaortag" "INTERCEPT:" ==
  "fatal 1:1-1:10 \"INTERCEPT is not supported by sudo-rs\" @1:10 rest=\":\""
#guard run "metaortag" "CHROOT=/x" ==
  "fatal 1:1-1:7 \"CHROOT is not supported by sudo-rs\" @1:7 rest=\"=/x\""
#guard run "metaortag" "TIMEOUT=1" ==
  "fatal 1:1-1:8 \"TIMEOUT is not supported by sudo-rs\" @1:8 rest=\"=1\""
#guard run "metaortag" "NOTBEFORE=1" ==
  "fatal 1:1-1:10 \"NOTBEFORE is not supported by sudo-rs\" @1:10 rest=\"=1\""
#guard run "metaortag" "NOTAFTER=1" ==
  "fatal 1:1-1:9 \"NOTAFTER is not supported by sudo-rs\" @1:9 rest=\"=1\""
#guard run "metaortag" "ROLE=x" ==
  "fatal 1:1-1:5 \"SELinux role based access control is not yet supported by sudo-rs\" @1:5 rest=\"=x\""
#guard run "metaortag" "TYPE=x" ==
  "fatal 1:1-1:5 \"SELinux role based access control is not yet supported by sudo-rs\" @1:5 rest=\"=x\""
#guard run "metaortag" "LOG_INPUT:" ==
  "ok only(ignored(1:1-1:10)) @1:11 rest=\"\""
#guard run "metaortag" "NOLOG_INPUT :" ==
  "ok only(ignored(1:1-1:13)) @1:14 rest=\"\""
#guard run "metaortag" "LOG_OUTPUT:" ==
  "ok only(ignored(1:1-1:11)) @1:12 rest=\"\""
#guard run "metaortag" "NOLOG_OUTPUT:" ==
  "ok only(ignored(1:1-1:13)) @1:14 rest=\"\""
#guard run "metaortag" "MAIL:" ==
  "ok only(ignored(1:1-1:5)) @1:6 rest=\"\""
#guard run "metaortag" "NOMAIL:" ==
  "ok only(ignored(1:1-1:7)) @1:8 rest=\"\""
#guard run "metaortag" "FOLLOW:" ==
  "ok only(ignored(1:1-1:7)) @1:8 rest=\"\""
#guard run "metaortag" "NOFOLLOW:" ==
  "ok only(noop) @1:10 rest=\"\""
#guard run "metaortag" "NOINTERCEPT:" ==
  "ok only(noop) @1:13 rest=\"\""
#guard run "metaortag" "APPARMOR_PROFILE=foo" ==
  "ok only(apparmor(\"foo\")) @1:21 rest=\"\""
#guard run "metaortag" "APPARMOR_PROFILE=a,b" ==
  "ok only(apparmor(\"a\")) @1:19 rest=\",b\""
#guard run "metaortag" "APPARMOR_PROFILE=\"x\"" ==
  "fatal 1:18-1:18 \"expected elem\" @1:18 rest=\"\\\"x\\\"\""
#guard run "metaortag" "ALL" ==
  "ok ALL @1:4 rest=\"\""
#guard run "metaortag" "FOO" ==
  "ok alias:\"FOO\" @1:4 rest=\"\""
#guard run "metaortag" "FOO=bar" ==
  "fatal 1:1-1:5 \"unsupported modifier 'FOO'\" @1:5 rest=\"bar\""
#guard run "metaortag" "FOO =bar" ==
  "fatal 1:1-1:6 \"unsupported modifier 'FOO'\" @1:6 rest=\"bar\""
#guard run "metaortag" "nopasswd:" ==
  "reject @1:1 rest=\"nopasswd:\""
#guard run "metaortag" "" ==
  "reject @1:1 rest=\"\""
#guard run "metaortag" "MAIL" ==
  "fatal 1:5-1:5 \"expecting ':' but found 'EOF'\" @1:5 rest=\"\""

#guard run "commandspec" "/bin/ls" ==
  "ok cs([],allow(only(cmd(\"/bin/ls\",prefix[])))) @1:8 rest=\"\""
#guard run "commandspec" "NOPASSWD: /bin/ls" ==
  "ok cs([nopasswd],allow(only(cmd(\"/bin/ls\",prefix[])))) @1:18 rest=\"\""
#guard run "commandspec" "NOPASSWD:/bin/ls" ==
  "ok cs([nopasswd],allow(only(cmd(\"/bin/ls\",prefix[])))) @1:17 rest=\"\""
#guard run "commandspec" "NOPASSWD: ALL" ==
  "ok cs([nopasswd],allow(ALL)) @1:14 rest=\"\""
#guard run "commandspec" "PASSWD: NOEXEC: /bin/ls a" ==
  "ok cs([passwd,noexec],allow(only(cmd(\"/bin/ls\",exact[\"a\"])))) @1:26 rest=\"\""
#guard run "commandspec" "SHELLS" ==
  "ok cs([],allow(alias:\"SHELLS\")) @1:7 rest=\"\""
#guard run "commandspec" "NOPASSWD: SHELLS" ==
  "ok cs([nopasswd],allow(alias:\"SHELLS\")) @1:17 rest=\"\""
#guard run "commandspec" "NOPASSWD:" ==
  "fatal 1:10-1:10 \"expected elem\" @1:10 rest=\"\""
#guard run "commandspec" "NOPASSWD: !/bin/ls" ==
  "ok cs([nopasswd],forbid(only(cmd(\"/bin/ls\",prefix[])))) @1:19 rest=\"\""
#guard run "commandspec" "!/bin/ls" ==
  "ok cs([],forbid(only(cmd(\"/bin/ls\",prefix[])))) @1:9 rest=\"\""
#guard run "commandspec" "!!ALL" ==
  "ok cs([],allow(ALL)) @1:6 rest=\"\""
#guard run "commandspec" "CWD=/tmp /bin/ls" ==
  "ok cs([cwd(path(\"/tmp\"))],allow(only(cmd(\"/bin/ls\",prefix[])))) @1:17 rest=\"\""
#guard run "commandspec" "MAIL: NOMAIL: ALL" ==
  "ok cs([ignored(1:1-1:5),ignored(1:7-1:13)],allow(ALL)) @1:18 rest=\"\""
#guard run "commandspec" "NOPASSWD: x" ==
  "fatal 1:11-1:11 \"expected elem\" @1:11 rest=\"x\""
#guard run "commandspec" "ls" ==
  "fatal 1:1-1:3 \"fully qualified path needed\" @1:3 rest=\"\""
#guard run "commandspec" "NOPASSWD:\\\n /bin/ls" ==
  "ok cs([nopasswd],allow(only(cmd(\"/bin/ls\",prefix[])))) @2:9 rest=\"\""
#guard run "commandspec" "sha224:abc" ==
  "fatal 1:1-1:7 \"digest specifications are not supported\" @1:7 rest=\":abc\""

/-- The tag limit: 127 tags pass, the 128th is fatal. -/
def tags (n : Nat) : String := " ".intercalate (List.replicate n "EXEC:") ++ " /bin/ls"
#guard run "commandspec" (tags 127) ==
  "ok cs([" ++ ",".intercalate (List.replicate 127 "exec") ++
    "],allow(only(cmd(\"/bin/ls\",prefix[])))) @1:770 rest=\"\""
#guard run "commandspec" (tags 128) ==
  "fatal 1:769-1:769 \"too many tags for command specifier\" @1:769 rest=\"/bin/ls\""

#guard run "runascmd" "/bin/ls" ==
  "ok (none,cs([],allow(only(cmd(\"/bin/ls\",prefix[]))))) @1:8 rest=\"\""
#guard run "runascmd" "(root) /bin/ls" ==
  "ok (some(runas([allow(only(user(name:\"root\")))];[])),cs([],allow(only(cmd(\"/bin/ls\",prefix[]))))) @1:15 rest=\"\""
#guard run "runascmd" "(root) NOPASSWD: ALL" ==
  "ok (some(runas([allow(only(user(name:\"root\")))];[])),cs([nopasswd],allow(ALL))) @1:21 rest=\"\""
#guard run "runascmd" "(root)" ==
  "fatal 1:7-1:7 \"expected elem\" @1:7 rest=\"\""
#guard run "runascmd" "(root) x" ==
  "fatal 1:8-1:8 \"expected elem\" @1:8 rest=\"x\""
#guard run "runascmd" "ALL" ==
  "ok (none,cs([],allow(ALL))) @1:4 rest=\"\""
#guard run "runascmd" "x" ==
  "fatal 1:1-1:1 \"expected elem\" @1:1 rest=\"x\""

#guard run "permissions" "ALL = ALL" ==
  "ok [([allow(ALL)],[(none,cs([],allow(ALL)))])] @1:10 rest=\"\""
#guard run "permissions" "ALL=(ALL:ALL) ALL" ==
  "ok [([allow(ALL)],[(some(runas([allow(ALL)];[allow(ALL)])),cs([],allow(ALL)))])] @1:18 rest=\"\""
#guard run "permissions" "host1, !host2 = /bin/ls, (root) /bin/sh : host3 = ALL" ==
  "ok [([allow(only(\"host1\")),forbid(only(\"host2\"))],[(none,cs([],allow(only(cmd(\"/bin/ls\",prefix[]))))),(some(runas([allow(only(user(name:\"root\")))];[])),cs([],allow(only(cmd(\"/bin/sh\",prefix[])))))]),([allow(only(\"host3\"))],[(none,cs([],allow(ALL)))])] @1:54 rest=\"\""
#guard run "permissions" "ALL = /bin/a, sha224:x" ==
  "fatal 1:15-1:21 \"digest specifications are not supported\" @1:21 rest=\":x\""
#guard run "permissions" "ALL = ALL ) junk" ==
  "ok [([allow(ALL)],[(none,cs([],allow(ALL)))])] @1:11 rest=\") junk\""
#guard run "permissions" "ALL = ALL !/usr/bin/su" ==
  "ok [([allow(ALL)],[(none,cs([],allow(ALL)))])] @1:11 rest=\"!/usr/bin/su\""
#guard run "permissions" "ALL = ALL, !/usr/bin/su" ==
  "ok [([allow(ALL)],[(none,cs([],allow(ALL))),(none,cs([],forbid(only(cmd(\"/usr/bin/su\",prefix[])))))])] @1:24 rest=\"\""
#guard run "permissions" "ALL" ==
  "fatal 1:4-1:4 \"expecting '=' but found 'EOF'\" @1:4 rest=\"\""
#guard run "permissions" "ALL =" ==
  "fatal 1:6-1:6 \"expected elem\" @1:6 rest=\"\""
#guard run "permissions" "= ALL" ==
  "reject @1:1 rest=\"= ALL\""
#guard run "permissions" "ALL = ALL :" ==
  "fatal 1:12-1:12 \"expected elem\" @1:12 rest=\"\""
#guard run "permissions" "ALL = ALL, " ==
  "fatal 1:12-1:12 \"expected elem\" @1:12 rest=\"\""
#guard run "permissions" "ALL = (root) /bin/ls, /bin/sh, (bob) ALL" ==
  "ok [([allow(ALL)],[(some(runas([allow(only(user(name:\"root\")))];[])),cs([],allow(only(cmd(\"/bin/ls\",prefix[]))))),(none,cs([],allow(only(cmd(\"/bin/sh\",prefix[]))))),(some(runas([allow(only(user(name:\"bob\")))];[])),cs([],allow(ALL)))])] @1:41 rest=\"\""

#guard run "defuser" "ADMINS = alice, bob" ==
  "ok def(\"ADMINS\",[allow(only(user(name:\"alice\"))),allow(only(user(name:\"bob\")))]) @1:20 rest=\"\""
#guard run "defuser" "ADMINS=%wheel" ==
  "ok def(\"ADMINS\",[allow(only(group(name:\"wheel\")))]) @1:14 rest=\"\""
#guard run "defuser" "ALL = x" ==
  "fatal 1:1-1:5 \"reserved word ALL used as an alias name\" @1:5 rest=\"= x\""
#guard run "defuser" "CWD = x" ==
  "fatal 1:1-1:5 \"reserved word CWD used as an alias name\" @1:5 rest=\"= x\""
#guard run "defuser" "ROLE=x" ==
  "fatal 1:1-1:5 \"reserved word ROLE used as an alias name\" @1:5 rest=\"=x\""
#guard run "defuser" "A = " ==
  "fatal 1:5-1:5 \"expected elem\" @1:5 rest=\"\""
#guard run "defuser" "A x" ==
  "fatal 1:3-1:3 \"expecting '=' but found 'x'\" @1:3 rest=\"x\""
#guard run "defuser" "a = b" ==
  "reject @1:1 rest=\"a = b\""
#guard run "defuser" "A = !alice, ALL" ==
  "ok def(\"A\",[forbid(only(user(name:\"alice\"))),allow(ALL)]) @1:16 rest=\"\""

#guard run "defscmnd" "SHELLS = /bin/sh, /bin/bash : EDITORS = /usr/bin/vi" ==
  "ok [def(\"SHELLS\",[allow(only(cmd(\"/bin/sh\",prefix[]))),allow(only(cmd(\"/bin/bash\",prefix[])))]),def(\"EDITORS\",[allow(only(cmd(\"/usr/bin/vi\",prefix[])))])] @1:52 rest=\"\""
#guard run "defscmnd" "SAFE = ALL !/usr/bin/su" ==
  "fatal 1:8-1:24 \"fully qualified path needed\" @1:24 rest=\"\""
#guard run "defscmnd" "A = /bin/a :" ==
  "fatal 1:13-1:13 \"expected elem\" @1:13 rest=\"\""
#guard run "defscmnd" "A = /bin/a : B" ==
  "fatal 1:15-1:15 \"expecting '=' but found 'EOF'\" @1:15 rest=\"\""
#guard run "defscmnd" "X=" ==
  "fatal 1:3-1:3 \"expected elem\" @1:3 rest=\"\""
#guard run "defscmnd" "NOTBEFORE = /x" ==
  "fatal 1:1-1:11 \"reserved word NOTBEFORE used as an alias name\" @1:11 rest=\"= /x\""

end SudoersSpec.Syntax.TestsGrammar
