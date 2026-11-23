import SudoersSpec.Syntax.Ast

/-!
# Tests of the reference parser core

Two kinds of evidence, both checked by `lake build`:

* `example … := by decide`: kernel-checked equations on concrete inputs. They reproduce the unit
  tests of `basic_parser.rs` and `char_stream.rs` and the cases listed in the task (line
  continuation in tokens, length limit, `!` folding, `Meta<Hostname>` classification, IPv4-like
  names, positions, missing final newline, garbage at end of line).
* `#guard` (tests, compiled evaluation): 113 cases whose expected text was produced by the legacy
  Rust code at `70fdb56b` (`char_stream.rs`, `basic_parser.rs`, and the items `Hostname`,
  `AliasName`, `Meta<T>`, `Qualified<T>` copied verbatim into a scratch harness, with the
  release descriptions and the test tokens below) on the same inputs. A case covers only its
  input.

The test tokens mirror the test token of `basic_parser.rs` (`impl Token for String`) and add
tokens with escapes and a small `MAX_LEN`. `O` is `CharOracle.latin1`; all inputs stay in
Latin-1 except `€` (U+20AC), which only the oracle-free `smallToken` sees.
-/

namespace SudoersSpec.Syntax.Tests

open SudoersSpec.Syntax
open Parser

/-! ## Fixtures -/

/-- The character oracle of the tests. -/
def O : CharOracle := CharOracle.latin1

/-- The test token of `basic_parser.rs`: `impl Token for String` with `c.is_ascii_alphanumeric()`. -/
def stringToken : TokenSpec String where
  construct s := .ok (String.ofList s)
  accept := isAsciiAlphanumeric

/-- A token with escapes that accepts a space (as `Command` does): `\` newline reads as `' '`. -/
def contToken : TokenSpec String where
  construct s := .ok (String.ofList s)
  accept c := isAsciiAlphanumeric c || c == ' '
  allowEscape := true
  escaped c := c == '\\' || c == ','

/-- A token with escapes that does not accept a space (as `Username`): `\` newline rejects. -/
def userToken : TokenSpec String where
  construct s := .ok (String.ofList s)
  accept := isAsciiAlphanumeric
  allowEscape := true
  escaped c := c == '\\' || c == ' '

/-- A token with escapes that accepts the backslash itself. -/
def backToken : TokenSpec String where
  construct s := .ok (String.ofList s)
  accept c := isAsciiAlphanumeric c || c == '\\'
  allowEscape := true
  escaped c := c == ','

/-- A token with `MAX_LEN = 3`. -/
def smallToken : TokenSpec String where
  maxLen := 3
  construct s := .ok (String.ofList s)
  accept c := c != ' ' && c != '\n'

def runOn (p : Parser α) (text : String) : Parsed α × Stream :=
  p.run (Stream.ofString text)

def linesOf (text : String) : Parsed (List (Parsed String)) :=
  (runOn (parseLines "elem" (token stringToken)) text).1

/-! ## `char_stream.rs` `test_iter` and positions -/

example : (Stream.ofString "12\n3\n").peek = some '1' := by decide
example :
    let s := Stream.ofString "12\n3\n"
    let (b1, s) := s.eatChar '1'
    let p2 := s.peek
    let (b2, s) := s.eatChar '2'
    let (b3, s) := s.eatChar '\n'
    let p3 := s.peek
    let (b4, s) := s.eatChar '3'
    b1 && b2 && b3 && b4 && p2 == some '2' && p3 == some '3' && s.getPos == (2, 2) := by
  decide

/-- Positions after newlines: `skip_to_newline` stops before the newline, `advance` crosses it. -/
example : (Stream.ofString "ab\ncd").skipToNewline = ⟨"\ncd".toList, 1, 3⟩ := by decide
example : (Stream.ofString "ab\ncd").advance 4 = ⟨"d".toList, 2, 2⟩ := by decide
example : (Stream.ofString "a\n\nb").advance 3 = ⟨"b".toList, 3, 1⟩ := by decide

/-! ## `basic_parser.rs` unit tests -/

/-- `comment_test`. -/
example : parseString comment "# hello" = .ok () := by decide

/-- `comment_test_fail` (`#[should_panic]`): the newline is left over. -/
example : parseString comment "# hello\nsomething" =
    .error (.fatal ⟨(1, 8), (1, 8)⟩ (.garbageAtEndOfLineChar '\n')) := by decide

/-- `lines_test`. -/
example : linesOf "hello\nworld\n" = .ok [.ok "hello", .ok "world"] := by decide
example : linesOf "   hello\nworld\n" = .ok [.ok "hello", .ok "world"] := by decide
example : linesOf "hello  \nworld\n" = .ok [.ok "hello", .ok "world"] := by decide
example : linesOf "hello\n   world\n" = .ok [.ok "hello", .ok "world"] := by decide
example : linesOf "hello\nworld  \n" = .ok [.ok "hello", .ok "world"] := by decide
/-- `lines_test`, missing final newline: `input("hello\nworld")[2]` is an error. -/
example : linesOf "hello\nworld" =
    .ok [.ok "hello", .ok "world", .error (.fatal ⟨(2, 6), (2, 6)⟩ .missingLineTerminator)] := by
  decide
/-- `lines_test`, garbage at end of line: `input("hello\nworld:\n")[2]` is an error. The line is
then skipped up to its newline only, so the next iteration starts at that newline and reports a
second error for this test token (a `Sudo` line would be a `LineComment` there). -/
example : linesOf "hello\nworld:\n" =
    .ok [.ok "hello", .ok "world", .error (.fatal ⟨(2, 6), (2, 6)⟩ .garbageAtEndOfLine),
      .error (.fatal ⟨(2, 7), (2, 7)⟩ (.expected "elem"))] := by decide

/-- `whitespace_test`. -/
example : parseString (parseVec {} "elem" (token stringToken)) "hello,something" =
    .ok ["hello", "something"] := by decide
example : parseString (parseVec {} "elem" (token stringToken)) "hello , something" =
    .ok ["hello", "something"] := by decide
example : parseString (parseVec {} "elem" (token stringToken)) "hello, something" =
    .ok ["hello", "something"] := by decide
example : parseString (parseVec {} "elem" (token stringToken)) "hello ,something" =
    .ok ["hello", "something"] := by decide
example : parseString (parseVec {} "elem" (token stringToken)) "hello\\\n,something" =
    .ok ["hello", "something"] := by decide

/-! ## Tokens: escapes, line continuation, length -/

/-- Backslash-newline inside a token that accepts a space: read as `' '`. -/
example : runOn (token contToken) "ab\\\ncd" = (.ok "ab cd", ⟨[], 2, 3⟩) := by decide
/-- Backslash-newline inside a token that does not accept a space: the token ends, the two
characters are consumed. -/
example : runOn (token userToken) "ab\\\ncd" = (.ok "ab", ⟨"cd".toList, 2, 1⟩) := by decide
/-- Backslash-newline at the start of such a token: `Reject` after consuming input. -/
example : runOn (token userToken) "\\\ncd" = (.error .reject, ⟨"cd".toList, 2, 1⟩) := by decide
/-- Any other escape is fatal, at the position after the backslash. -/
example : runOn (token userToken) "a\\x" =
    (.error (.fatal ⟨(1, 3), (1, 3)⟩ .illegalEscapeSequence), ⟨"x".toList, 1, 3⟩) := by decide
/-- A backslash the token accepts is literal when the next character is not escaped. -/
example : runOn (token backToken) "a\\b" = (.ok "a\\b", ⟨[], 1, 4⟩) := by decide

/-- The length check happens before appending: `ab€` (5 bytes) passes `MAX_LEN = 3`; the next
character fails. -/
example : runOn (token smallToken) "ab€" = (.ok "ab€", ⟨[], 1, 4⟩) := by decide
example : runOn (token smallToken) "ab€c" =
    (.error (.fatal ⟨(1, 5), (1, 5)⟩ .tokenExceedsMaximumLength), ⟨[], 1, 5⟩) := by decide

/-! ## `Meta<Hostname>`, `Qualified`, `SpecList<Hostname>` -/

example : runOn (metaHostname O) "ALL" = (.ok .all, ⟨[], 1, 4⟩) := by decide
example : runOn (metaHostname O) "FOO_1" = (.ok (.alias "FOO_1"), ⟨[], 1, 6⟩) := by decide
example : runOn (metaHostname O) "foo" = (.ok (.only "foo"), ⟨[], 1, 4⟩) := by decide
example : runOn (metaHostname O) "ALLx" = (.ok (.only "ALLx"), ⟨[], 1, 5⟩) := by decide
example : runOn (metaHostname O) "ALL_" = (.ok (.alias "ALL_"), ⟨[], 1, 5⟩) := by decide
/-- `Meta<T>` widens the classes by `char::is_uppercase`: a non-ASCII uppercase letter becomes
part of a host name that `Hostname` alone would not accept. -/
example : runOn (metaHostname O) "Éa" = (.ok (.only "Éa"), ⟨[], 1, 3⟩) := by decide

/-- IPv4-like names are refused, with a span over the token; so are `123` and `1.2.3`. -/
example : runOn (metaHostname O) "1.2.3.4" =
    (.error (.fatal ⟨(1, 1), (1, 8)⟩ .hostIPv4Address), ⟨[], 1, 8⟩) := by decide
example : runOn (metaHostname O) "123" =
    (.error (.fatal ⟨(1, 1), (1, 4)⟩ .hostIPv4Address), ⟨[], 1, 4⟩) := by decide
example : runOn (metaHostname O) "1.2.3.4.5" = (.ok (.only "1.2.3.4.5"), ⟨[], 1, 10⟩) := by decide
example : runOn (metaHostname O) "1234.1.1.1" = (.ok (.only "1234.1.1.1"), ⟨[], 1, 11⟩) := by
  decide

/-- `!` folding: odd count `forbid`, even count `allow`, whitespace allowed after each `!`. -/
example : runOn (qualified "host name" (metaHostname O)) "!foo" =
    (.ok (.forbid (.only "foo")), ⟨[], 1, 5⟩) := by decide
example : runOn (qualified "host name" (metaHostname O)) "!!foo" =
    (.ok (.allow (.only "foo")), ⟨[], 1, 6⟩) := by decide
example : runOn (qualified "host name" (metaHostname O)) "!!!foo" =
    (.ok (.forbid (.only "foo")), ⟨[], 1, 7⟩) := by decide
example : runOn (qualified "host name" (metaHostname O)) "! ! foo" =
    (.ok (.allow (.only "foo")), ⟨[], 1, 8⟩) := by decide
example : runOn (qualified "host name" (metaHostname O)) "!" =
    (.error (.fatal ⟨(1, 2), (1, 2)⟩ (.expected "host name")), ⟨[], 1, 2⟩) := by decide

example : runOn (specListHostname O .release) "a , !b,ALL" =
    (.ok [.allow (.only "a"), .forbid (.only "b"), .allow .all], ⟨[], 1, 11⟩) := by decide
/-- Prefix acceptance: the list ends where the next separator is missing. -/
example : runOn (specListHostname O .release) "a b" = (.ok [.allow (.only "a")], ⟨"b".toList, 1, 3⟩) := by
  decide

/-! ## `parse_lines` over `SpecList<Hostname>` -/

def linesHostOf (text : String) : Parsed (List (Parsed (SpecList Hostname))) :=
  (runOn (parseLines "host name" (specListHostname O .release)) text).1

/-- Missing final newline. -/
example : linesHostOf "foo" =
    .ok [.ok [.allow (.only "foo")], .error (.fatal ⟨(1, 4), (1, 4)⟩ .missingLineTerminator)] := by
  decide
/-- Garbage at end of line, then the newline itself starts a new (failing) item. -/
example : linesHostOf "foo bar\n" =
    .ok [.ok [.allow (.only "foo")], .error (.fatal ⟨(1, 5), (1, 5)⟩ .garbageAtEndOfLine),
      .error (.fatal ⟨(1, 8), (1, 8)⟩ (.expected "host name"))] := by decide
/-- An error inside the list drops the line; the next line is parsed on its own. -/
example : linesHostOf "foo,\nbar\n" =
    .ok [.error (.fatal ⟨(1, 5), (1, 5)⟩ (.expected "host name")), .ok [.allow (.only "bar")]] := by
  decide
/-- A line continuation inside a list, and positions on the following lines. -/
example : linesHostOf "foo \\\n,bar\nx\n" =
    .ok [.ok [.allow (.only "foo"), .allow (.only "bar")], .ok [.allow (.only "x")]] := by decide

/-! ## Rendered messages -/

example : (ErrKind.expectingSyntax '=' (some 'x')).render = "expecting '=' but found 'x'" := by
  decide
example : (ErrKind.expectingSyntax '=' none).render = "expecting '=' but found 'EOF'" := by decide

/-! ## Comparison with the legacy Rust parser (`#guard` tests)

Each line runs one production on one input and renders `result @line:col rest=remaining`
(backslash and newline escaped). The expected strings are the output of the legacy Rust code. -/

def showStatus : Status → String
  | .fatal sp k => s!"fatal {sp.start.1}:{sp.start.2}-{sp.stop.1}:{sp.stop.2} {esc k.render}"
  | .reject => "reject"
where
  esc (s : String) : String := (s.replace "\\" "\\\\").replace "\n" "\\n"

def esc (s : String) : String := showStatus.esc s

def showParsed (f : α → String) : Parsed α → String
  | .ok x => "ok " ++ f x
  | .error e => showStatus e

def showMeta : Meta Hostname → String
  | .all => "ALL"
  | .alias a => "alias:" ++ esc a
  | .only h => "only:" ++ esc h

def showQual : Qualified (Meta Hostname) → String
  | .allow m => "allow(" ++ showMeta m ++ ")"
  | .forbid m => "forbid(" ++ showMeta m ++ ")"

def showList (f : α → String) (l : List α) : String :=
  "[" ++ ",".intercalate (l.map f) ++ "]"

def showRun (f : α → String) : Parsed α × Stream → String
  | (r, s) => s!"{showParsed f r} @{s.line}:{s.col} rest={esc (String.ofList s.rest)}"

def showLines (f : α → String) : Parsed (List (Parsed α)) × Stream → String :=
  showRun fun items => "[" ++ "; ".intercalate (items.map (showParsed f)) ++ "]"

def linesString (i : String) := showLines esc (runOn (parseLines "elem" (token stringToken)) i)
def vecString (i : String) :=
  showRun (showList esc) (runOn (expectComplete "elem" (parseVec {} "elem" (token stringToken))) i)
def commentComplete (i : String) := showRun (fun _ => "()") (runOn (expectComplete "elem" comment) i)
def tokCont (i : String) := showRun esc (runOn (token contToken) i)
def tokUser (i : String) := showRun esc (runOn (token userToken) i)
def tokBack (i : String) := showRun esc (runOn (token backToken) i)
def tokSmall (i : String) := showRun esc (runOn (token smallToken) i)
def metaHost (i : String) := showRun showMeta (runOn (metaHostname O) i)
def qualHost (i : String) := showRun showQual (runOn (qualified "host name" (metaHostname O)) i)
def specListHost (i : String) := showRun (showList showQual) (runOn (specListHostname O .release) i)
def linesHost (i : String) :=
  showLines (showList showQual) (runOn (parseLines "host name" (specListHostname O .release)) i)
def expectEq (i : String) := showRun (fun _ => "()") (runOn (expectSyntax '=') i)
def aliasName (i : String) := showRun esc (runOn (token aliasNameToken) i)

#guard linesString "hello\nworld\n" == "ok [ok hello; ok world] @3:1 rest="
#guard linesString "   hello\nworld\n" == "ok [ok hello; ok world] @3:1 rest="
#guard linesString "hello  \nworld\n" == "ok [ok hello; ok world] @3:1 rest="
#guard linesString "hello\n   world\n" == "ok [ok hello; ok world] @3:1 rest="
#guard linesString "hello\nworld  \n" == "ok [ok hello; ok world] @3:1 rest="
#guard linesString "hello\nworld" == "ok [ok hello; ok world; fatal 2:6-2:6 missing line terminator at end of file] @2:6 rest="
#guard linesString "hello\nworld:\n" == "ok [ok hello; ok world; fatal 2:6-2:6 garbage at end of line; fatal 2:7-2:7 expected elem] @3:1 rest="
#guard linesString "" == "ok [] @1:1 rest="
#guard linesString "\n\n" == "ok [fatal 1:1-1:1 expected elem; fatal 2:1-2:1 expected elem] @3:1 rest="
#guard linesString "  \n" == "ok [fatal 1:3-1:3 expected elem] @2:1 rest="
#guard linesString "hello # c\nworld\n" == "ok [ok hello; ok world] @3:1 rest="
#guard linesString "a \\\nb\n" == "ok [ok a; fatal 2:1-2:1 garbage at end of line; fatal 2:2-2:2 expected elem] @3:1 rest="
#guard linesString "a\\x\nb\n" == "ok [fatal 1:3-1:3 stray escape sequence; fatal 1:4-1:4 expected elem; ok b] @3:1 rest="
#guard linesString "a\n  " == "ok [ok a] @2:3 rest="
#guard linesString "#x\nb\n" == "ok [fatal 1:1-1:1 expected elem; ok b] @3:1 rest="

#guard vecString "hello,something" == "ok [hello,something] @1:16 rest="
#guard vecString "hello , something" == "ok [hello,something] @1:18 rest="
#guard vecString "hello, something" == "ok [hello,something] @1:17 rest="
#guard vecString "hello ,something" == "ok [hello,something] @1:17 rest="
#guard vecString "hello\\\n,something" == "ok [hello,something] @2:11 rest="
#guard vecString "hello," == "fatal 1:7-1:7 expected elem @1:7 rest="
#guard vecString "hello,,x" == "fatal 1:7-1:7 expected elem @1:7 rest=,x"
#guard vecString "hello world" == "fatal 1:7-1:7 garbage at end of line: w @1:7 rest=world"

#guard commentComplete "# hello" == "ok () @1:8 rest="
#guard commentComplete "# hello\nsomething" == "fatal 1:8-1:8 garbage at end of line: \\n @1:8 rest=\\nsomething"
#guard commentComplete "x" == "fatal 1:1-1:1 expected elem @1:1 rest=x"

#guard tokCont "ab\\\ncd" == "ok ab cd @2:3 rest="
#guard tokCont "\\\ncd" == "ok  cd @2:3 rest="
#guard tokCont "ab\\,cd" == "ok ab,cd @1:7 rest="
#guard tokCont "ab\\x" == "fatal 1:4-1:4 illegal escape sequence @1:4 rest=x"

#guard tokUser "ab\\\ncd" == "ok ab @2:1 rest=cd"
#guard tokUser "\\\ncd" == "reject @2:1 rest=cd"
#guard tokUser "a\\x" == "fatal 1:3-1:3 illegal escape sequence @1:3 rest=x"
#guard tokUser "a\\ b" == "ok a b @1:5 rest="
#guard tokUser "a\\\\b" == "ok a\\\\b @1:5 rest="
#guard tokUser "\\" == "fatal 1:2-1:2 illegal escape sequence @1:2 rest="
#guard tokUser "a\\" == "fatal 1:3-1:3 illegal escape sequence @1:3 rest="

#guard tokBack "a\\b" == "ok a\\\\b @1:4 rest="
#guard tokBack "a\\,b" == "ok a,b @1:5 rest="
#guard tokBack "a\\\nb" == "ok a\\\\ @1:3 rest=\\nb"

#guard tokSmall "abc" == "ok abc @1:4 rest="
#guard tokSmall "abcd" == "fatal 1:5-1:5 token exceeds maximum length @1:5 rest="
#guard tokSmall "ab€" == "ok ab€ @1:4 rest="
#guard tokSmall "ab€c" == "fatal 1:5-1:5 token exceeds maximum length @1:5 rest="
#guard tokSmall "a€" == "ok a€ @1:3 rest="
#guard tokSmall "€b" == "fatal 1:3-1:3 token exceeds maximum length @1:3 rest="
#guard tokSmall "€bc" == "fatal 1:3-1:3 token exceeds maximum length @1:3 rest=c"

#guard metaHost "ALL" == "ok ALL @1:4 rest="
#guard metaHost "FOO_1" == "ok alias:FOO_1 @1:6 rest="
#guard metaHost "foo" == "ok only:foo @1:4 rest="
#guard metaHost "ALLx" == "ok only:ALLx @1:5 rest="
#guard metaHost "ALL_" == "ok alias:ALL_ @1:5 rest="
#guard metaHost "Foo" == "ok only:Foo @1:4 rest="
#guard metaHost "FOO.bar" == "ok only:FOO.bar @1:8 rest="
#guard metaHost "ALL " == "ok ALL @1:4 rest= "
#guard metaHost "Éa" == "ok only:Éa @1:3 rest="
#guard metaHost "1.2.3.4" == "fatal 1:1-1:8 hosts cannot be specified using an IPv4 address @1:8 rest="
#guard metaHost "123" == "fatal 1:1-1:4 hosts cannot be specified using an IPv4 address @1:4 rest="
#guard metaHost "1.2.3" == "fatal 1:1-1:6 hosts cannot be specified using an IPv4 address @1:6 rest="
#guard metaHost "1.2.3.4.5" == "ok only:1.2.3.4.5 @1:10 rest="
#guard metaHost "1234.1.1.1" == "ok only:1234.1.1.1 @1:11 rest="
#guard metaHost "1..2" == "ok only:1..2 @1:5 rest="
#guard metaHost "1.2.3.a" == "ok only:1.2.3.a @1:8 rest="
#guard metaHost "12.34.56.789" == "fatal 1:1-1:13 hosts cannot be specified using an IPv4 address @1:13 rest="
#guard metaHost "A1.2.3.4" == "ok only:A1.2.3.4 @1:9 rest="
#guard metaHost "-" == "ok only:- @1:2 rest="
#guard metaHost "" == "reject @1:1 rest="
#guard metaHost " x" == "reject @1:1 rest= x"

/-- The length limit on `Meta<Hostname>` (`MAX_LEN = 255` bytes): 255 bytes pass; a 2-byte last
character after 254 bytes passes too (256 bytes); one more character after that fails. -/
def a254 : String := String.ofList (List.replicate 254 'a')
def a255 : String := String.ofList (List.replicate 255 'a')
#guard metaHost a255 == "ok only:" ++ a255 ++ " @1:256 rest="
#guard metaHost (a254 ++ "É") == "ok only:" ++ a254 ++ "É @1:256 rest="
#guard metaHost (a254 ++ "Éb") == "fatal 1:257-1:257 token exceeds maximum length @1:257 rest="
#guard metaHost (a255 ++ "b") == "fatal 1:257-1:257 token exceeds maximum length @1:257 rest="

#guard qualHost "foo" == "ok allow(only:foo) @1:4 rest="
#guard qualHost "!foo" == "ok forbid(only:foo) @1:5 rest="
#guard qualHost "!!foo" == "ok allow(only:foo) @1:6 rest="
#guard qualHost "!!!foo" == "ok forbid(only:foo) @1:7 rest="
#guard qualHost "! ! foo" == "ok allow(only:foo) @1:8 rest="
#guard qualHost "!" == "fatal 1:2-1:2 expected host name @1:2 rest="
#guard qualHost "! " == "fatal 1:3-1:3 expected host name @1:3 rest="
#guard qualHost "!!" == "fatal 1:3-1:3 expected host name @1:3 rest="
#guard qualHost "!1.2.3.4" == "fatal 1:2-1:9 hosts cannot be specified using an IPv4 address @1:9 rest="
#guard qualHost "!ALL" == "ok forbid(ALL) @1:5 rest="
#guard qualHost "x!" == "ok allow(only:x) @1:2 rest=!"

#guard specListHost "a,b" == "ok [allow(only:a),allow(only:b)] @1:4 rest="
#guard specListHost "a , !b,ALL" == "ok [allow(only:a),forbid(only:b),allow(ALL)] @1:11 rest="
#guard specListHost "a," == "fatal 1:3-1:3 expected host name @1:3 rest="
#guard specListHost "a,,b" == "fatal 1:3-1:3 expected host name @1:3 rest=,b"
#guard specListHost ",a" == "reject @1:1 rest=,a"
#guard specListHost "a b" == "ok [allow(only:a)] @1:3 rest=b"
#guard specListHost "a,\\\n b" == "ok [allow(only:a),allow(only:b)] @2:3 rest="

/-- The list limit (`Many::LIMIT = 127`): 127 elements pass; the 128th separator is fatal. -/
def hosts (n : Nat) : String := ",".intercalate (List.replicate n "a")
#guard specListHost (hosts 127) ==
  "ok [" ++ ",".intercalate (List.replicate 127 "allow(only:a)") ++ "] @1:254 rest="
#guard specListHost (hosts 128) == "fatal 1:255-1:255 too many items in list @1:255 rest=a"

#guard linesHost "foo\n" == "ok [ok [allow(only:foo)]] @2:1 rest="
#guard linesHost "foo" == "ok [ok [allow(only:foo)]; fatal 1:4-1:4 missing line terminator at end of file] @1:4 rest="
#guard linesHost "foo bar\n" == "ok [ok [allow(only:foo)]; fatal 1:5-1:5 garbage at end of line; fatal 1:8-1:8 expected host name] @2:1 rest="
#guard linesHost "foo,\nbar\n" == "ok [fatal 1:5-1:5 expected host name; ok [allow(only:bar)]] @3:1 rest="
#guard linesHost "foo # c\n" == "ok [ok [allow(only:foo)]] @2:1 rest="
#guard linesHost "a,b\n\n  c\n" == "ok [ok [allow(only:a),allow(only:b)]; fatal 2:1-2:1 expected host name; ok [allow(only:c)]] @4:1 rest="
#guard linesHost "1.2.3.4\nb\n" == "ok [fatal 1:1-1:8 hosts cannot be specified using an IPv4 address; ok [allow(only:b)]] @3:1 rest="
#guard linesHost "foo \\\n,bar\nx\n" == "ok [ok [allow(only:foo),allow(only:bar)]; ok [allow(only:x)]] @4:1 rest="
#guard linesHost "foo\\\nbar\n" == "ok [ok [allow(only:foo)]; fatal 2:1-2:1 garbage at end of line; fatal 2:4-2:4 expected host name] @3:1 rest="
#guard linesHost "!\n" == "ok [fatal 1:2-1:2 expected host name] @2:1 rest="

#guard expectEq "=x" == "ok () @1:2 rest=x"
#guard expectEq "= x" == "ok () @1:3 rest=x"
#guard expectEq "=\\x" == "fatal 1:3-1:3 expecting '=' but found 'x' @1:3 rest=x"
#guard expectEq "x" == "fatal 1:1-1:1 expecting '=' but found 'x' @1:1 rest=x"
#guard expectEq "" == "fatal 1:1-1:1 expecting '=' but found 'EOF' @1:1 rest="
#guard expectEq "=\\\n x" == "ok () @2:2 rest=x"

#guard aliasName "FOO" == "ok FOO @1:4 rest="
#guard aliasName "FOO_1 " == "ok FOO_1 @1:6 rest= "
#guard aliasName "Foo" == "ok F @1:2 rest=oo"
#guard aliasName "1FOO" == "reject @1:1 rest=1FOO"
#guard aliasName "F-O" == "ok F @1:2 rest=-O"

end SudoersSpec.Syntax.Tests
