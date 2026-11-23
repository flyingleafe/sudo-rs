# `SudoersSpec.Grammar`: the declarative grammar and PT2 to PT5

PLAN.md section 5.2 and theorems PT2 to PT5 of section 4, stage P1: a declarative grammar for
the host list `SpecList<Hostname>` (`Host_List` of `docs/man/sudoers.5.md`), built on a generic
layer that P2 and P3 instantiate, and the theorems relating it to the reference parser
`SudoersSpec.Syntax.specListHostname` (`Syntax/README.md`). Core Lean only. Everything is
kernel-checked; no hypothesis is added to PT2 to PT4; PT5 adds one hypothesis on the character
oracle (`HostOracle`, below).

## Files

| File | Content |
|---|---|
| `Basic.lean` | `Gram`, `NextNot`, the theorem shapes `RejectPure`, `Sound`, `Complete`, `Trunc`, `Derives`; positions (`Sound.pos`, `Complete.run_eq`); `run_ok_iff`, `Complete.unambiguous`, `Complete.derives_unique`; `PureG`, `SeqG` with `pure_*`, `bind_*`; `loop_rel` (induction over loop iterations relating input and output streams) |
| `Lexical.lean` | blanks, `Ws` (trailing whitespace), `SynG` (`try_syntax`, `expect_syntax`, `is_syntax`), `NontermG` (`try_nonterminal`, `expect_nonterminal`) |
| `Token.lean` | `EscUnit`, `EscStop`, `EscRejects`, `TokTail`, `LenOK`, `TokenG` for any `TokenSpec`; the no-escape form `tokenG_noEsc` |
| `List.lean` | `Bangs`, `QualG` (`Qualified<T>`), `ListTail`, `ListG` (`parse_list`), `SpecListG` |
| `IPv4.lean` | `IPv4Like`, `looksLikeIPv4_iff` (the `rsplitn` test of `Hostname::construct`, declaratively) |
| `Hostname.lean` | `AliasNameG`, `HostnameG`, `hostChar`, `MetaHostVal`, `HostItemG`, `HostListG`; PT2 to PT4 for the standalone name tokens and `SpecList<Hostname>` |
| `RoundTrip.lean` | `HostOracle`, the printer, `Printable`, PT5, `printable_iff_derivable` |
| `Follow.lean` | `HeadOnly`; the exact follow condition of a host list (`hostList_follow_iff`) |
| `Examples.lean` | non-vacuity: derivations, applications of PT2 to PT5 on concrete inputs, `HostOracle CharOracle.latin1`, the PT2 counterexample, negative controls |

## Shape of the grammar and of the theorems

A nonterminal is a relation with a right context:

```lean
abbrev Gram (α : Type) := List Char → α → List Char → Prop   -- G c a rest
def NextNot (P : Char → Prop) (r : List Char) : Prop := ∀ d, r.head? = some d → ¬ P d
```

`G c a rest`: the characters `c` derive the value `a` when `rest` follows them. The grammar
only asks negative questions about the right context (`NextNot`), and those questions are the
follow conditions: maximal munch of tokens and of whitespace, the end of a list, the end of a
run of `!`. Inside a production the right context of a part is what the later parts consume
followed by the right context of the whole, so the follow conditions between parts are part of
the derivation. PLAN.md's `Derives c a` is `Derives G c a := ∃ rest, G c a rest`; with `Trunc`
(below) it is `G c a []`.

```lean
def RejectPure (p : Parser α) : Prop :=                       -- PT2
  ∀ s s', p.run s = (.error .reject, s') → s' = s
def Sound (p : Parser α) (G : Gram α) : Prop :=               -- PT3
  ∀ s a s', p.run s = (.ok a, s') → ∃ c, s.rest = c ++ s'.rest ∧ G c a s'.rest
def Complete (p : Parser α) (G : Gram α) : Prop :=            -- PT4
  ∀ c a rest s, G c a rest → s.rest = c ++ rest → ∃ s', p.run s = (.ok a, s') ∧ s'.rest = rest
def Trunc (G : Gram α) : Prop := ∀ c a x y, G c a (x ++ y) → G c a x
```

Positions come for free from `Parser.reaches`: `Sound.pos` adds
`s'.getPos = posAfter c s.getPos`, `Complete.run_eq` gives the whole output stream
`⟨rest, posAfter c (line, col)⟩`. `run_ok_iff` combines PT3 and PT4: the parser succeeds on
`c ++ rest` leaving `rest` iff `G c a rest`. So the follow condition of PT4 is exact: it is
`G c a rest` for the actual `rest`.

## Lexical conventions (as the code has them)

* Blank: `' '` or `'\t'` only (`"\t ".contains(c)`).
* `W`, the whitespace a terminal swallows (`TrailingWhitespace::parse`):
  `W ::= blank* ('\' newline W)?`, maximal. In front of a `\` not followed by a newline the
  code fails (`stray escape sequence`), so a derivation of `W` never stops in front of `\`:
  `Ws.stop` requires `NextNot (fun d => blank d = true ∨ d = '\\') rest`. Comments are not
  whitespace.
* `try_syntax(ch)` consumes `ch W` (`SynG`); `try_nonterminal` and `expect_nonterminal`
  consume `X W` (`NontermG`). A raw `token` does not take this extra whitespace pass.
* Token: units read by `accept_escaped`, maximal (table in `Token.lean`): plain `c`
  (`pred c`, and `c ≠ \` if escapes are allowed), escaped `\ d` (`T.escaped d`), a literal `\`
  (`pred '\'`, next character not `T.escaped`), continuation `\ newline` read as `' '`
  (`pred ' '`, newline not escaped, `pred '\'` false). The token ends in front of a character
  that `accept` refuses and that does not open an escape (`EscStop`), or silently after
  `\ newline` when escapes are allowed, newline is not escaped and `accept` takes neither `\`
  nor `' '` (`TokTail.term`; those two characters are consumed).
* Length: `str.len() >= MAX_LEN` is checked on the UTF-8 length of the characters read so far,
  before each further character is appended (`LenOK`, closed form `lenOK_iff`): a token of
  `n` decoded characters passes the length check iff `n = 1` or its first `n - 1`
  characters take fewer than `MAX_LEN` bytes. For `MAX_LEN ≥ 1`, the result can be up to
  `MAX_LEN + 3` bytes long.

## The generic layer

| Production | Grammar | PT3 / PT4 | PT2 |
|---|---|---|---|
| `TrailingWhitespace` | `Ws`, `WsG` | `trailingWhitespace_sound/complete` | never rejects: `trailingWhitespace_rejectPure` |
| `try_syntax(ch)` | `SynG ch` | `trySyntax_sound/complete` | exact: `trySyntax_reject_iff` (rejects iff `ch` is not next, consuming nothing) |
| `expect_syntax(ch)` | `SynG ch` | `expectSyntax_sound/complete` | never rejects |
| `is_syntax(ch)` | `isSyntax_true_iff`, `isSyntax_false_iff` | | never rejects |
| `try_nonterminal(p)` | `NontermG G` | `tryNonterminal_sound/complete` from those of `p` | exact transfer: `tryNonterminal_reject` (rejects iff `p` rejects, same stream) |
| `expect_nonterminal(p)` | `NontermG G` | `expectNonterminal_sound/complete` | never rejects |
| `accept_escaped(T, pred)` | `EscUnit T pred` | `acceptEscaped_sound/complete` | exact: `acceptEscaped_reject` (+ converses `acceptEscaped_stop`, `acceptEscaped_rejects`) |
| `impl<T: Token> Parse for T` | `TokenG T` | `token_sound/complete` | exact: `token_reject`, `token_rejectPure_iff`; fails outside the condition (below) |
| `Qualified<T>` | `QualG G` | `qualified_sound/complete` | `qualified_reject_iff`: the element rejects and no `!` is next |
| `parse_list(sep, max)`, `Vec<T>` | `ListG G sep max` | `parseList_sound/complete` | `parseList_reject_iff`: same reject as the element |
| `SpecList<T>` | `SpecListG G m` | `specList_sound/complete` | `specList_reject_iff`: `Meta<T>` rejects and no `!` is next |
| `pure a`, `p >>= f` | `PureG a`, `SeqG G H` | `pure_sound/complete`, `bind_sound/complete` | |

The relations, abbreviated (`Lexical.lean`, `Token.lean`, `List.lean` have them in full):

```lean
inductive Ws : List Char → List Char → Prop
  | stop : (∀ x ∈ bs, blank x = true) → NextNot (fun d => blank d = true ∨ d = '\\') rest → Ws bs rest
  | cont : (∀ x ∈ bs, blank x = true) → Ws w rest → Ws (bs ++ '\\' :: '\n' :: w) rest
def NontermG (G : Gram α) : Gram α :=
  fun c a rest => ∃ c₁ w, c = c₁ ++ w ∧ G c₁ a (w ++ rest) ∧ Ws w rest
inductive TokenG (T : TokenSpec α) : Gram α
  | mk : EscUnit T T.accept1st u x (c' ++ rest) → TokTail T c' xs rest →
      LenOK T.maxLen [x] xs → T.construct (x :: xs) = .ok a → TokenG T (u ++ c') a rest
inductive QualG (G : Gram α) : Gram (Qualified α)
  | mk : Bangs n b (c ++ rest) → NextNot (· = '!') (c ++ rest) → NontermG G c a rest →
      QualG G (b ++ c) (Qualified.ofBangs n a) rest          -- ('!' W)^n, odd n = forbid
inductive ListG (G : Gram α) (sep : Char) (max : Nat) : Gram (List α)
  | mk : NontermG G c a (c' ++ rest) → ListTail G sep c' as rest → (as = [] ∨ as.length < max) →
      ListG G sep max (c ++ c') (a :: as) rest               -- ListTail ends with NextNot (· = sep)
```

### PT2 for tokens: the exact condition and the counterexample

```lean
def EscRejects (T : TokenSpec α) (pred : Char → Bool) : Prop :=
  T.allowEscape = true ∧ T.escaped '\n' = false ∧ pred '\\' = false ∧ pred ' ' = false
theorem token_reject (T : TokenSpec α) {s s' : Stream}
    (h : (token T).run s = (.error .reject, s')) :
    (s' = s ∧ EscStop T T.accept1st s.rest) ∨
      (EscRejects T T.accept1st ∧ s.rest = '\\' :: '\n' :: s'.rest)
theorem token_rejectPure_iff (T : TokenSpec α) :
    RejectPure (token T) ↔ ¬ EscRejects T T.accept1st
```

`token_reject_of_escRejects` is the converse: under `EscRejects T T.accept1st` the token
rejects on every input starting with `\ newline`, having consumed both characters. Kernel-checked
instance: `Examples.escTok` (escapes allowed, `\` and space escaped, class ASCII alphanumeric),
`(token escTok).run (Stream.ofString "\\\nab") = (.error .reject, ⟨"ab".toList, 2, 1⟩)` and
`escTok_not_rejectPure`; the same input makes `parse_list` over `Qualified` of that token reject
after consuming. The transfer lemmas preserve the element's remaining stream on a rejection
that reaches the caller; a qualifying `!` converts a later element rejection to a fatal error.

`AliasNameG` uses `AliasShape`, the standalone name's 255-byte check and maximal munch. It
does not reserve `ALL`; that check belongs to alias declarations. `HostnameG` uses the ASCII
host class, the same byte check, maximal munch and the non-IPv4 condition. Their PT2 to PT4
lemmas are `aliasName_rejectPure/sound/complete` and `hostname_rejectPure/sound/complete`.

## The instance: `SpecList<Hostname>` (`Host_List`)

```
Host_List ::= Host (',' W Host)*        at most 127 items; ends before a character other than ','
Host      ::= ('!' W)* Item W           an odd number of '!' gives forbid; Item not starting with '!'
Item      ::= hostChar+                 maximal; fewer than 255 bytes before the last character
              classified (MetaHostVal): ALL | alias name | host name
hostChar  ::= ASCII letter | digit | '.' | '-' | '_' | any char::is_uppercase character
```

```lean
def hostChar (O : CharOracle) (c : Char) : Bool := Hostname.accept c || O.isUppercase c
def AliasShape (n : List Char) : Prop :=          -- NAME ::= [A-Z][A-Z0-9_]*
  ∃ x xs, n = x :: xs ∧ isAsciiUppercase x = true ∧ ∀ y ∈ xs, AliasName.accept y = true
def IPv4Part (O : CharOracle) (p : List Char) : Prop :=
  p ≠ [] ∧ utf8Len p ≤ 3 ∧ ∀ x ∈ p, O.isNumeric x = true ∧ x ≠ '.'
def IPv4Like (O : CharOracle) (raw : List Char) : Prop :=
  ∃ parts, parts ≠ [] ∧ parts.length ≤ 4 ∧ raw = joinWith '.' parts ∧ ∀ p ∈ parts, IPv4Part O p
inductive MetaHostVal (O : CharOracle) : List Char → Meta Hostname → Prop
  | all   : trimEnd O raw = "ALL".toList → MetaHostVal O raw .all
  | alias : trimEnd O raw ≠ "ALL".toList → AliasShape (trimEnd O raw) →
      MetaHostVal O raw (.alias (String.ofList (trimEnd O raw)))
  | host  : ¬ AliasShape (trimEnd O raw) → ¬ IPv4Like O raw →
      MetaHostVal O raw (.only (String.ofList raw))
structure HostItemG (O : CharOracle) (c : List Char) (a : Meta Hostname) (rest : List Char) : Prop where
  ne : c ≠ []
  chars : ∀ x ∈ c, hostChar O x = true
  len : utf8Len c.dropLast < 255
  stop : NextNot (fun d => hostChar O d = true) rest
  val : MetaHostVal O c a
def HostListG (O : CharOracle) : Gram (SpecList Hostname) :=
  SpecListG (HostItemG O) hostnameMany          -- = ListG (QualG (HostItemG O)) ',' 127
```

`tokenG_metaHost_iff` proves `TokenG (metaToken O (hostnameToken O)) ↔ HostItemG O` (no
escapes, `tokenG_noEsc`; `Meta::construct` ↔ `MetaHostVal`, `metaConstruct_iff`;
`Hostname::looksLikeIPv4` ↔ `IPv4Like`, `looksLikeIPv4_iff`). `MetaHostVal` transcribes the
code: the `ALL`/alias decision is made on the text without trailing `char::is_whitespace`
characters; under `HostOracle` that text is the token itself (`HostOracle.metaHostVal_iff`).

### Theorems

```lean
-- PT2
theorem specListHostname_rejectPure (O : CharOracle) (D : Descriptions) :
    RejectPure (specListHostname O D)
-- PT3
theorem specListHostname_sound (O : CharOracle) (D : Descriptions) {s s' : Stream}
    {a : SpecList Hostname} (h : (specListHostname O D).run s = (.ok a, s')) :
    ∃ c, s.rest = c ++ s'.rest ∧ HostListG O c a s'.rest ∧ s'.getPos = posAfter c s.getPos
-- PT4
theorem specListHostname_complete (O : CharOracle) (D : Descriptions) {c rest : List Char}
    {a : SpecList Hostname} (h : HostListG O c a rest) (line col : Nat) :
    (specListHostname O D).run ⟨c ++ rest, line, col⟩ =
      (.ok a, ⟨rest, (posAfter c (line, col)).1, (posAfter c (line, col)).2⟩)
-- PT3 + PT4
theorem specListHostname_run_ok_iff (O : CharOracle) (D : Descriptions) {c rest : List Char}
    {a : SpecList Hostname} {s : Stream} (hs : s.rest = c ++ rest) :
    (∃ s', (specListHostname O D).run s = (.ok a, s') ∧ s'.rest = rest) ↔ HostListG O c a rest
-- PT4 corollaries: the grammar is unambiguous
theorem hostList_unambiguous (O : CharOracle) {c c' r r' : List Char} {a a' : SpecList Hostname}
    (h1 : HostListG O c a r) (h2 : HostListG O c' a' r') (he : c ++ r = c' ++ r') :
    c = c' ∧ a = a'
theorem hostList_derives_unique (O : CharOracle) {c : List Char} {a a' : SpecList Hostname}
    (h1 : Derives (HostListG O) c a) (h2 : Derives (HostListG O) c a') : a = a'
-- the follow condition, explicitly (Follow.lean)
def ListFollowChar (O : CharOracle) (c : List Char) (d : Char) : Prop :=
  d ≠ ',' ∧ ¬ (blank d = true ∨ d = '\\') ∧ (EndsHost O c → hostChar O d = false)
theorem hostList_follow_iff {O : CharOracle} (hO : HostOracle O) {c : List Char}
    {a : SpecList Hostname} {rest : List Char} :
    HostListG O c a rest ↔
      HostListG O c a [] ∧ ∀ d, rest.head? = some d → ListFollowChar O c d
-- PT5 (RoundTrip.lean)
theorem specListHostname_roundTrip (O : CharOracle) (hO : HostOracle O) (D : Descriptions)
    {a : SpecList Hostname} (ha : Printable O a) {rest : List Char} (hr : PrintFollow O rest)
    (line col : Nat) :
    (specListHostname O D).run ⟨printHostList a ++ rest, line, col⟩ =
      (.ok a, ⟨rest, (posAfter (printHostList a) (line, col)).1,
        (posAfter (printHostList a) (line, col)).2⟩)
theorem printable_iff_derivable {O : CharOracle} (hO : HostOracle O) (a : SpecList Hostname) :
    Printable O a ↔ ∃ c rest, HostListG O c a rest
```

The follow condition in words: after a host list the next character, if any, is not `,` (the
list would go on), not a blank and not `\` (the whitespace after the last item is maximal; a `\`
without newline is fatal), and, if the list text ends with a host-name character (no whitespace
after the last item), not a host-name character (maximal munch). `#` (a comment), `=`, `:`, `)`
and a newline may follow. PT2 to PT4 hold for every oracle; only the explicit form of the follow
condition and PT5 use `HostOracle`.

PT5. `printHostList` prints items separated by `", "`, `!` before a forbidden item, no
whitespace at either end. `Printable O a`: `a ≠ []`, `a.length ≤ 127`, and every item is `ALL`,
an alias name (`AliasShape`, not `ALL`) or a host name (non-empty, all `hostChar`, not
`AliasShape` — which excludes `ALL` and anything shaped like an alias — and not `IPv4Like`), with
fewer than 255 bytes before the last character. `PrintFollow O rest`: the next character is not
a host-name character, a blank, `\` or `,`. `printable_iff_derivable` shows that `Printable` is
exactly the set of values the grammar (hence, by PT3, the parser) produces.

## The hypothesis on `CharOracle`

```lean
structure HostOracle (O : CharOracle) : Prop where
  upper_ascii : ∀ c : Char, c.toNat < 128 → O.isUppercase c = isAsciiUppercase c
  ws_ascii : ∀ c : Char, c.toNat < 128 → O.isWhitespace c = asciiWhiteSpace c
  upper_not_ws : ∀ c : Char, O.isUppercase c = true → O.isWhitespace c = false
```

`asciiWhiteSpace c` is `c` in U+0009..U+000D or U+0020. Justification: the Rust documentation of
`char::is_uppercase` and `char::is_whitespace` (their ASCII members are `A`..`Z` and
U+0009..U+000D, U+0020), and the Unicode tables (`White_Space` contains no character with the
`Uppercase` property). Use: blanks, `\`, `,`, `!` and newline are not host-name characters (PT5,
`hostList_follow_iff`), and no host-name character is white space, so `trimEnd` does nothing to a
host token (PT5, `HostOracle.metaHostVal_iff`). Non-vacuity: `Examples.hostOracle_latin1`
(the test oracle satisfies it). PT2 to PT4 need no hypothesis.

## Where the man page and the code disagree (the grammar follows the code)

1. `NAME ::= [A-Z]([A-Z][0-9]_)*` in the man page reads as repeated three-character groups; the
   prose and the code accept `[A-Z][A-Z0-9_]*` (`AliasShape`).
2. The man page says `!`, `=`, `:`, `,`, `(`, `)`, `\` must be escaped with a backslash inside a
   host name. `Hostname` has no escapes: a `\` ends the item, and is a fatal error
   (`stray escape sequence`) unless a newline follows (line continuation).
3. The man page allows shell wildcards in host names; `*`, `?`, `[`, `]` are not host-name
   characters, so the item ends in front of them.
4. "host name" has no lexical definition in the man page. The code: ASCII letters and digits,
   `.`, `-`, `_`, and (through `Meta<Hostname>`) every `char::is_uppercase` character, including
   non-ASCII ones that `Hostname` alone refuses.
5. A host name shaped like an alias name (upper case, digits, `_`, starting with an upper-case
   letter) is always an alias reference, never a host name; `ALL` is the wildcard. The man
   page's `Host ::= '!'* host name | '!'* Host_Alias` does not say how the two are told apart.
6. Names of at most four dot-separated numeric parts of at most 3 bytes each (`123`, `1.2.3`,
   `1.2.3.4`) are refused with a fatal error; the man page does not mention it.
7. Whitespace and line continuations may follow each `!` (`'!' W`); the EBNF writes `'!'*`.
8. Limits not in the man page: at most 127 items per list; a host item may have at most 254
   bytes before its last character.
9. Comments are not whitespace inside a list: `#` ends the list (it is an admissible follow), it
   does not continue it (already noted in `Syntax/README.md`).

## How P2 and P3 instantiate the generic layer

* A token `X` is a `TokenSpec`; its grammar is `TokenG X` with PT2 to PT4 for free
  (`token_sound`, `token_complete`, `token_reject`). For a class without escapes `tokenG_noEsc`
  gives the plain form; with escapes the units are `EscUnit`. A readable grammar for the token
  is a relation proved equivalent to `TokenG X` (as `tokenG_metaHost_iff`); `Sound.mono` and
  `Complete.mono` move the theorems to it. The value condition is `T.construct (x :: xs) = .ok a`;
  for a constructor that consults an oracle (`SimpleCommand`) the grammar takes the oracle as a
  parameter, as `MetaHostVal` takes `O`.
* `Meta<T>` is `metaToken O T`; `metaConstruct_iff` is the pattern for its classification.
* `Spec<T>`, `SpecList<T>`, `Vec<T>` are `QualG`, `SpecListG`, `ListG` with the element grammar:
  `specList_sound (hp : Sound p G)`, `specList_complete (hp : Complete p G)`, `specList_reject`.
* A production in `do` notation: `bind_sound`, `bind_complete` (grammar `SeqG G H`) and
  `pure_*`; syntax characters with `trySyntax_*`/`expectSyntax_*` (`SynG`); nonterminals with
  `tryNonterminal_*`/`expectNonterminal_*` (`NontermG`). A branch on `is_syntax` uses
  `isSyntax_true_iff`/`isSyntax_false_iff`; the "false" branch adds `NextNot (· = ch)` to the
  right context, as `QualG` does for `!`.
* Loops: `loop_rel` (soundness, by induction over the iterations with the stream) and induction
  on the derivation with `Parser.loop_run` (completeness), as in `tokenLoop_*`, `bangLoop_*`,
  `listLoop_*`.
* Unambiguity comes from PT4 alone (`Complete.unambiguous`); `Derives`-uniqueness also needs
  `Trunc`, which holds as long as the follow conditions are negative (`NextNot`); every
  combinator here preserves it (`*.trunc`). A production whose follow condition is positive
  (one that peeks and restores, `get_directive`) breaks `Trunc`, not `Complete.unambiguous`.
* Productions that reject after consuming (`UserSpecifier` on a quoted non-user, F-P3, and
  every token with `EscRejects`) get PT2 as an exact statement in the style of `token_reject`;
  the transfer lemmas (`tryNonterminal_reject`, `qualified_reject`, `parseList_reject`) carry it
  through the combinators.

## Non-vacuity (`Examples.lean`)

Derivations from the constructors (`Ws` with a continuation, items `web1` and `SERVERS`,
`!!ALL`); the sample `[allow web1, forbid DB, allow ALL]`: printed as `web1, !DB, ALL`,
printable, derived, PT4 and PT5 applied and compared with the kernel evaluation of the parser,
the unambiguity corollary, the follow condition (`#` may follow, `,` and a host character may
not); PT3 applied to a run with blanks, a line continuation, `!!` and `É`; PT2 applied to a
rejected input; the token PT2 counterexample; negative controls `1.2.3.4`, `123`, `a, `, the
empty text and `a \x` (no derivation for any value and right context).

## P1 proof size

Measured on this directory (lines without blank lines and comments; `theorem`/`example` and
definitions counted at the start of a line):

| File | Lean lines | theorems + examples | definitions |
|---|---|---|---|
| `Basic.lean` | 178 | 22 | 10 |
| `Lexical.lean` | 360 | 45 | 5 |
| `Token.lean` | 581 | 29 | 7 |
| `List.lean` | 602 | 34 | 9 |
| `IPv4.lean` | 193 | 10 | 4 |
| `Hostname.lean` | 208 | 26 | 9 |
| `RoundTrip.lean` | 299 | 26 | 10 |
| `Follow.lean` | 292 | 23 | 5 |
| `Examples.lean` | 158 | 36 | 3 |
| total | 2871 | 251 | 62 |

The Rust it describes (legacy `70fdb56b`, code lines without comments): `char_stream.rs` 47,
`basic_parser.rs` without tests 233 (of which `parse_lines` and `Comment`, about 35, are not part
of this fragment), `Hostname`/`Meta<T>`/`AliasName` in `tokens.rs` 73, `Qualified<T>` in `ast.rs`
23: about 340 lines, so about 8 lines of grammar proof per Rust line. The generic layer
(`Basic`, `Lexical`, `Token`, `List`: 1721 lines) is reused by P2 and P3; the name and host-list
instances with PT5 and the follow condition are 992 lines.

## P2: permission lines

`PermissionAtoms`, `PermissionRunAs`, `PermissionTags`, `Permission`, and
`PermissionDispatch` give the syntax judgments for a permission specification;
`PermissionPrint` and `PermissionExamples` give its round trip and a concrete derivation.
No judgment is defined by a successful parser run. Tokens reuse `TokenG` over the
reference character classes, escape tables, length limits and value constructors.
The command constructor splits the decoded token into a path and argument words and
uses the given filesystem and glob oracles. No equality between different oracle
snapshots is assumed.

The outer rule is a user list followed by a `:`-separated list of `Host_List = Entries`
groups. An entry is optional runas followed by tags and a qualified command. Variants
of the grammar account for the leading `#` branch and quoted or ordinary first users
in the actual `Syntax.sudo` production. The ordinary case requires `OrdinaryKey`:
the first user cannot select a directive. This does not constrain a first user in
the explicitly quoted or numeric branch. `permissionLine` is the same body without
the outer dispatch.

* `IdentifierG` recognizes bare names or `#` and a decimal `u32`. The bare markers
  (`#`, `%`, `%:`, and the opening quote) differ from punctuation that consumes `Ws`.
  `UserSpecifierG` handles the nested, re-escaped input of quoted users. `MetaG` uses
  the lexical rejection judgment `TokenRejectG`, not just an empty optional token.
* A maximal alias-shaped keyword before a command is a tag, `ALL` or an alias.
  `MetaTagG` checks the required punctuation and payload for known tags, and tests
  the absence of `=` after an alias. `TagLoopG` accounts for the tag count limit;
  after the failed keyword probe, command syntax is `QualG` over `CommandTokenG`.
* The general PT3 grammar includes the successful outcomes of runas defaults after
  a swallowed error. `MissG` records the consumed prefix and a `NoMatch` judgment
  (no successful user/group-list derivation from that input). It does not characterize
  the exact cursor endpoint of an unsuccessful list or its diagnostic.
* PT3 carries the outer stream position exactly. For a span-bearing ignored tag, the
  broad structural relation checks the span's internal displacement over the keyword
  and whitespace; its start is existential, not guarded by the outer stream position.
  The clean grammar for PT4 excludes span-bearing modifiers. It permits an empty
  runas user list only under the lexical guard `EmptyRunasUsers`, and does not use
  the recovered runas cases.

The central statements for the actual `sudo` branch are:

```lean
sudo_permission_sound (O : Oracles) (D : Descriptions) {s t : Stream} {a : PermissionSpec}
    (h : (sudo O D).run s = (.ok (.spec a), t)) :
    ∃ c, s.rest = c ++ t.rest ∧ SudoPermissionG O c a t.rest ∧
      t.getPos = posAfter c s.getPos

sudo_permission_pt4 (O : Oracles) (D : Descriptions) {c r : List Char}
    {a : PermissionSpec} (h : PositiveSudoPermissionG O c a r) (line col : Nat) :
    (sudo O D).run ⟨c ++ r, line, col⟩ =
      (.ok (.spec a), ⟨r, (posAfter c (line, col)).1, (posAfter c (line, col)).2⟩)

sudo_permission_roundTrip (O : Oracles) (D : Descriptions) {a : PermissionSpec}
    (h : PrintableSudoPermission O a) (rest : List Char) (line col : Nat) :
    let c := (PermissionPrint.permissionSpec a).toList
    (sudo O D).run ⟨c ++ '\n' :: rest, line, col⟩ =
      (.ok (.spec a), ⟨'\n' :: rest, (posAfter c (line, col)).1, (posAfter c (line, col)).2⟩)
```

PT4 takes the exact right context of the derivation. PT5 uses a physical newline as
the follow character and can leave any tail after it, by `positiveSudoPermission_headOnly`.
Neither theorem consumes the newline, strips a leading indent, nor proves anything about
file-level recovery. No constraints on starting `line` and `col` are needed for the
Lean stream. PT4 also implies `sudo_permission_unambiguous` on a fixed input.

`PermissionPrint.permissionSpec` transcribes the permission-printer equations in
`Differential.Print` into the core-only package; the spec cannot import the harness.
`PrintableSudoPermission O a` is the explicit, oracle-relative grammar criterion
`PositiveSudoPermissionG O (PermissionPrint.permissionSpec a).toList a ['\n']`.
In particular, the list counts and byte limits must fit, the name classes and
all/alias/plain classifications must agree with the values, a command pattern must
survive canonicalization and glob compilation under `O`, and the printed argument
words must reconstruct the given `Args` (including `*` and `""` sentinels). The
printer does not escape values or print `CWD`, AppArmor, ignored, or no-op modifiers.
The criterion also excludes collisions in which a printed alias is read as a
keyword or the first user selects a directive. It is not a claim that every output
of the differential generator satisfies this judgment. No cross-package equivalence
or generator-range theorem is needed for the Lean theorem above; those are not
checked here. The example `PermissionExamples.simpleSudoPrintable` constructs a
derivation directly, then uses PT5 on it.
