import SudoersSpec.Syntax.SettingsParser

/-!
# `ast.rs`: `Sudo`, directives, includes; the entry point

The AST types `SudoersSpec/Ast.lean` does not have (`ConfigScope`, `Directive`, `Sudo`), the
productions `parse_include`, `get_directive` and `impl Parse for Sudo`, and `parseSudoers`, the
reference parser of a whole file (PLAN.md section 5.1).

The `@socket` directive and `PeerSpec` exist only with the feature `unstable-remote-sudoers`,
which is off by default; they are not transcribed.
-/

namespace SudoersSpec.Syntax

open Parser

/-! ## AST -/

/-- `tokens::SimpleCommand = glob::Pattern`, kept as its text. -/
abbrev SimpleCommand := String

/-- `ast.rs` `ConfigScope`: the scope of a `Defaults` line. -/
inductive ConfigScope where
  | generic
  | host (hosts : SpecList Hostname)
  | user (users : SpecList UserSpecifier)
  | runAs (users : SpecList UserSpecifier)
  | command (cmds : SpecList SimpleCommand)
  deriving DecidableEq, Repr

/-- `ast.rs` `Directive`: alias definitions and `Defaults`. -/
inductive Directive where
  | userAlias (defs : List (Def UserSpecifier))
  | hostAlias (defs : List (Def Hostname))
  | cmndAlias (defs : List (Def Command))
  | runasAlias (defs : List (Def UserSpecifier))
  | defaults (mods : List Settings.SettingsModifier) (scope : ConfigScope)
  deriving DecidableEq, Repr

/-- `Directive::could_be_username`. -/
def Directive.couldBeUsername : Directive → Bool
  | .defaults _ .generic | .userAlias _ | .hostAlias _ | .cmndAlias _ | .runasAlias _ => true
  | .defaults _ _ => false

/-- `ast.rs` `Sudo`: one line of a sudoers file. -/
inductive Sudo where
  | spec (p : PermissionSpec)
  | decl (d : Directive)
  | include (path : String) (span : Span)
  | includeDir (path : String) (span : Span)
  | lineComment
  deriving DecidableEq, Repr

/-! ## `parse_include` -/

/-- `get_path` inside `parse_include`: a quoted `QuotedIncludePath` and `"` (expected), or an
`IncludePath` that must be followed directly by a newline (after its trailing whitespace; the
end of the input or a comment is refused). The span runs from `key_pos` to here. -/
def getPath (O : Oracles) (D : Descriptions) (keyPos : Nat × Nat) : Parser (String × Span) := do
  let quote ← eatChar '"'
  let path ← if quote then do
      let path ← expectNonterminal D.quotedIncludePath (token (quotedIncludePathToken O.char))
      expectSyntax '"'
      pure path
    else do
      let valuePos ← getPos
      let path ← expectNonterminal D.includePath (token (includePathToken O.char))
      let next ← peek
      if next != some '\n' then fatalFrom valuePos .useQuotesAroundFilenames else pure path
  let endPos ← getPos
  pure (path, ⟨keyPos, endPos⟩)

/-- `parse_include`: the directive name after `@` or `#` as an optional `Username`;
`include` or `includedir` and a path, anything else the fatal `"unknown directive"`. -/
def parseInclude (O : Oracles) (D : Descriptions) : Parser Sudo := do
  let keyPos ← getPos
  let key ← tryNonterminal (parseOption (token (usernameToken O)))
  match key with
  | some "include" =>
    let (path, span) ← getPath O D keyPos
    pure (.include path span)
  | some "includedir" =>
    let (path, span) ← getPath O D keyPos
    pure (.includeDir path span)
  | _ => fatalFrom keyPos .unknownDirective

/-! ## `get_directive` -/

/-- `SpecList<SimpleCommand>`. -/
def specListSimpleCommand (O : Oracles) (D : Descriptions) : Parser (SpecList SimpleCommand) :=
  specList {} D.simpleCommand (token (metaToken O.char (simpleCommandToken O)))

/-- The scope of a `Defaults` line whose keyword allows one. `Defaults@`: back to the clone of
the stream taken before the user list, 9 characters forward (`stream.advance(DEFAULTS_LEN + 1)`),
trailing whitespace, a host list. Otherwise `:` users, `!` commands, `>` runas users, or none. -/
def defaultsScope (O : Oracles) (D : Descriptions) (rest : List Char) (s0 : Stream) :
    AParser s0 ConfigScope := do
  if rest.head? == some '@' then
    AParser.restore
    (Parser.advance 9 : Parser Unit)
    (skipTrailingWhitespace : Parser Unit)
    let hosts ← (expectNonterminal D.hostname (specListHostname O.char D) : Parser _)
    pure (.host hosts)
  else
    let colon ← (isSyntax ':' : Parser Bool)
    if colon then
      let users ← (expectNonterminal D.userSpecifier (specListUserSpecifier O D) : Parser _)
      pure (.user users)
    else
      let bang ← (isSyntax '!' : Parser Bool)
      if bang then
        let cmds ← (expectNonterminal D.simpleCommand (specListSimpleCommand O D) : Parser _)
        pure (.command cmds)
      else
        let gt ← (isSyntax '>' : Parser Bool)
        if gt then
          let users ← (expectNonterminal D.userSpecifier (specListUserSpecifier O D) : Parser _)
          pure (.runAs users)
        else
          pure .generic

/-- `get_directive(perhaps_keyword, stream, begin_state)` with `begin_state = s0`: rejects
unless the first user is a plain name. `User_Alias`, `Host_Alias`, `Cmnd_Alias`/`Cmd_Alias`,
`Runas_Alias` and their definitions; any name that starts with `Defaults` is a `Defaults` line.
A scope is allowed if the name continues with `@`, or if the stream is on the line of `s0`
exactly 8 columns after it (`Defaults` and no whitespace: the scope characters are not part of
a user name); then the settings. -/
def getDirective (O : Oracles) (D : Descriptions) (perhapsKeyword : Spec UserSpecifier)
    (s0 : Stream) : AParser s0 Directive :=
  match perhapsKeyword with
  | .allow (.only (.user (.name keyword))) =>
    let beginPos := s0.getPos
    match keyword with
    | "User_Alias" => do
      let d ← (expectNonterminal D.def_
        (defs D userSpecifierMany D.userSpecifier (metaUserSpecifier O D)) : Parser _)
      pure (.userAlias d)
    | "Host_Alias" => do
      let d ← (expectNonterminal D.def_
        (defs D hostnameMany D.hostname (metaHostname O.char)) : Parser _)
      pure (.hostAlias d)
    | "Cmnd_Alias" | "Cmd_Alias" => do
      let d ← (expectNonterminal D.def_
        (defs D {} D.command (token (metaToken O.char (commandToken O)))) : Parser _)
      pure (.cmndAlias d)
    | "Runas_Alias" => do
      let d ← (expectNonterminal D.def_
        (defs D userSpecifierMany D.userSpecifier (metaUserSpecifier O D)) : Parser _)
      pure (.runasAlias d)
    | _ =>
      if "Defaults".toList.isPrefixOf keyword.toList then do
        let rest := keyword.toList.drop 8
        let pos ← (Parser.getPos : Parser _)
        let allowScopeModifier :=
          rest.head? == some '@' || (pos.1 == beginPos.1 && pos.2 - beginPos.2 == 8)
        let scope ← if allowScopeModifier then defaultsScope O D rest s0 else pure .generic
        let mods ← (expectNonterminal D.settingsModifier
          (parseVec settingsModifierMany D.settingsModifier (settingsModifier O D)) : Parser _)
        pure (.defaults mods scope)
      else
        (Parser.reject : Parser _)
  | _ => (Parser.reject : Parser _)

/-! ## `Sudo` -/

/-- The `#` branch of `Sudo::parse`: a user id if an `Identifier` can be read (then more users
after `,` and the permissions), otherwise, after any failure of `Identifier` including fatal
ones and from wherever it stopped, `parse_include`, and if that fails too the rest of the
physical line is a comment (F-P4). -/
def sudoHash (O : Oracles) (D : Descriptions) : Parser Sudo := do
  match ← observe (tryNonterminal (identifier O D)) with
  | .ok ident =>
    let firstUser : Spec UserSpecifier := .allow (.only (.user ident))
    let comma ← isSyntax ','
    let users ← if comma then do
        let rest ← expectNonterminal D.userSpecifier (specListUserSpecifier O D)
        pure (firstUser :: rest)
      else
        pure [firstUser]
    let perms ← expectNonterminal D.hostsRunasCommands (permissions O D)
    pure (.spec ⟨users, perms⟩)
  | .error _ =>
    match ← observe (parseInclude O D) with
    | .ok r => pure r
    | .error _ =>
      skipToNewline
      pure .lineComment

/-- The rest of `Sudo::parse` from `let start_state = stream.clone();` on, anchored at that
clone: a quoted first user forces a permission line; otherwise a user list (tried), then a
directive if `get_directive` accepts the first user (`"ambiguous syntax"` if there are several
users and the directive could be a user name), else the permissions; no user list at all is a
`LineComment` that leaves the line as it is. -/
def sudoMain (O : Oracles) (D : Descriptions) (s0 : Stream) : AParser s0 Sudo := do
  let next ← (peek : Parser _)
  if next == some '"' then
    let users ← (expectNonterminal D.userSpecifier (specListUserSpecifier O D) : Parser _)
    let perms ← (expectNonterminal D.hostsRunasCommands (permissions O D) : Parser _)
    pure (.spec ⟨users, perms⟩)
  else
    let users? ← (Parser.maybe (tryNonterminal (specListUserSpecifier O D)) : Parser _)
    match users? with
    | none => pure .lineComment
    | some users =>
      -- `users[0]`: `parse_list` never returns an empty list (`parseList_ne_nil`)
      let key := users.headD (.allow .all)
      let startPos := s0.getPos
      let directive? ← AParser.maybe (getDirective O D key s0)
      match directive? with
      | some directive =>
        if users.length != 1 && directive.couldBeUsername then
          (fatalFrom startPos .ambiguousSyntax : Parser _)
        else
          pure (.decl directive)
      | none =>
        let perms ← (expectNonterminal D.hostsRunasCommands (permissions O D) : Parser _)
        pure (.spec ⟨users, perms⟩)

/-- `impl Parse for Sudo`: `@` starts an include directive; `#` a user id, an include directive
or a comment; anything else `sudoMain`. -/
def sudo (O : Oracles) (D : Descriptions) : Parser Sudo := do
  let at_ ← eatChar '@'
  if at_ then
    parseInclude O D
  else
    let next ← peek
    if next == some '#' then
      sudoHash O D
    else
      Parser.anchored (sudoMain O D)

/-! ## The entry point -/

/-- `parse_lines::<Sudo>` on the characters of a file, with the descriptions `D`: the items, or
`.error msg` if Rust panics (the first item carrying `ErrKind.unwrapNone`). -/
def parseSudoersWith (D : Descriptions) (O : Oracles) (src : List Char) :
    Except String (List (Parsed Sudo)) :=
  match ((parseLines D.sudo (sudo O D)).run (Stream.new src)).1 with
  | .ok items =>
    if items.any (fun i => match i with | .error (.fatal _ .unwrapNone) => true | _ => false) then
      .error ErrKind.unwrapNone.render
    else
      .ok items
  | .error _ => .ok []

/-- The reference parser of a sudoers file (PLAN.md section 5.1): `parse_lines::<Sudo>` of a
release build. -/
def parseSudoers (O : Oracles) (src : List Char) : Except String (List (Parsed Sudo)) :=
  parseSudoersWith .release O src

/-- No item of the reference parser is `Err(Reject)`: the `panic!("internal parser error")` of
`Sudoers::process` is unreachable (PT1 at the level of the reference parser). -/
theorem parseSudoersWith_ne_reject (D : Descriptions) (O : Oracles) (src : List Char)
    (items : List (Parsed Sudo)) (h : parseSudoersWith D O src = .ok items) :
    ∀ item ∈ items, item ≠ .error .reject := by
  obtain ⟨items', h', hne⟩ := parseLines_ok D.sudo (sudo O D) (Stream.new src)
  simp only [parseSudoersWith, h'] at h
  split at h
  · cases h
  · cases h; exact hne

theorem parseSudoers_ne_reject (O : Oracles) (src : List Char) (items : List (Parsed Sudo))
    (h : parseSudoers O src = .ok items) : ∀ item ∈ items, item ≠ .error .reject :=
  parseSudoersWith_ne_reject _ O src items h

end SudoersSpec.Syntax
