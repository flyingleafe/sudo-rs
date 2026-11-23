import SudoersSpec.Syntax.Tokens
import SudoersSpec.Syntax.AstNames

/-!
# `ast.rs` (core part): `Qualified<T>` and `SpecList<Hostname>`

The productions of `ast.rs` over the AST types of `SudoersSpec/Ast.lean`.
-/

namespace SudoersSpec.Syntax

open Parser

/-- `impl<T: Parse + UserFriendly> Parse for Qualified<T>`:
```
if is_syntax('!', stream)? {
    let mut neg = true;
    while is_syntax('!', stream)? { neg = !neg; }
    let ident = expect_nonterminal(stream)?;
    if neg { make(Qualified::Forbid(ident)) } else { make(Qualified::Allow(ident)) }
} else {
    let ident = try_nonterminal(stream)?;
    make(Qualified::Allow(ident))
}
```
An odd number of `!` gives `forbid`, an even number `allow`; whitespace may follow each `!`. The
loop `while is_syntax('!')?` is `whileMaybe (trySyntax '!')` (`is_syntax` is
`maybe(try_syntax(..))?.is_some()`). -/
def qualified (description : String) (p : Parser α) : Parser (Qualified α) := do
  if ← isSyntax '!' then
    let neg ← whileMaybe (trySyntax '!') (trySyntax_consumes '!')
      (fun neg () => pure (.next !neg)) id true
    let ident ← expectNonterminal description p
    if neg then pure (.forbid ident) else pure (.allow ident)
  else
    let ident ← tryNonterminal p
    pure (.allow ident)

/-- `impl<T: Many> Many for Qualified<T>`: the separator and limit of `T`. -/
def qualifiedMany (m : Many) : Many := m

theorem isSyntax_true_lt {c : Char} {s s' : Stream} (h : (isSyntax c).run s = (.ok true, s')) :
    s'.rest.length < s.rest.length := by
  obtain ⟨r, s₁, h₁, h⟩ := run_bind_eq_ok.mp h
  cases r with
  | none => simp at h
  | some u =>
    simp only [run_pure, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    exact (trySyntax_consumes c).maybe_some h₁

theorem qualified_consumes {p : Parser α} (hp : p.Consumes) (description : String) :
    (qualified description p).Consumes := by
  intro s q s' h
  obtain ⟨b, s₁, h₁, h⟩ := run_bind_eq_ok.mp h
  cases b with
  | true =>
    exact Nat.lt_of_le_of_lt (length_le_of_run h) (isSyntax_true_lt h₁)
  | false =>
    simp only [Bool.false_eq_true, ite_false] at h
    have l₁ := length_le_of_run h₁
    obtain ⟨x, s₂, h₂, h⟩ := run_bind_eq_ok.mp h
    simp only [run_pure, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    exact Nat.lt_of_lt_of_le (tryNonterminal_consumes hp _ _ _ h₂) l₁

/-- The parser of `Spec<T> = Qualified<Meta<T>>` from the parser of `Meta<T>`. -/
def spec (description : String) (p : Parser (Meta α)) : Parser (Spec α) :=
  qualified description p

/-- The parser of `SpecList<T> = Vec<Qualified<Meta<T>>>` (`impl Parse for Vec<T>`) with the
`Many` of `T`. -/
def specList (m : Many) (description : String) (p : Parser (Meta α)) : Parser (SpecList α) :=
  parseVec (qualifiedMany (metaMany m)) description (spec description p)

/-- `Meta<Hostname>`: the token `metaToken O (hostnameToken O)`. -/
def metaHostname (O : CharOracle) : Parser (Meta Hostname) :=
  token (metaToken O (hostnameToken O))

/-- `SpecList<Hostname>`, the host list of a permission line and of `Host_Alias`. -/
def specListHostname (O : CharOracle) (D : Descriptions) : Parser (SpecList Hostname) :=
  specList hostnameMany D.hostname (metaHostname O)

theorem metaHostname_consumes (O : CharOracle) : (metaHostname O).Consumes :=
  token_consumes _

theorem specListHostname_consumes (O : CharOracle) (D : Descriptions) :
    (specListHostname O D).Consumes :=
  parseVec_consumes (qualified_consumes (metaHostname_consumes O) _) _ _

/-! ## Helpers -/

/-- `try_nonterminal::<Option<T>>` returns `some` only after `T` consumed. -/
theorem tryNonterminal_parseOption_consumesSome {p : Parser α} (hp : p.Consumes) :
    (tryNonterminal (parseOption p)).ConsumesSome := by
  intro s a s' h
  obtain ⟨r, s₁, h₁, h⟩ := run_bind_eq_ok.mp h
  obtain ⟨_, s₂, h₂, h⟩ := run_bind_eq_ok.mp h
  simp only [run_pure, Prod.mk.injEq, Except.ok.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  have l₂ := length_le_of_run h₂
  have := hp.maybe_consumesSome s a s₁ h₁
  omega

/-! ## `Identifier`, `Meta<Identifier>` -/

/-- `impl Parse for Identifier`: `#` and a `DigitsU32` (expected), or a `Username` (tried). -/
def identifier (O : Oracles) (D : Descriptions) : Parser Identifier := do
  if ← eatChar '#' then
    let guid ← expectNonterminal D.digitsU32 (token digitsU32Token)
    pure (.id guid)
  else
    let name ← tryNonterminal (token (usernameToken O))
    pure (.name name)

/-- `impl Many for Identifier {}`. -/
def identifierMany : Many := {}

theorem identifier_consumes (O : Oracles) (D : Descriptions) : (identifier O D).Consumes := by
  intro s a s' h
  obtain ⟨b, s₁, h₁, h⟩ := run_bind_eq_ok.mp h
  cases b with
  | true =>
    exact Nat.lt_of_le_of_lt (length_le_of_run h) (run_eatChar_true_lt h₁)
  | false =>
    simp only [Bool.false_eq_true, ite_false] at h
    have l₁ := length_le_of_run h₁
    obtain ⟨x, s₂, h₂, h⟩ := run_bind_eq_ok.mp h
    simp only [run_pure, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    exact Nat.lt_of_lt_of_le (tryNonterminal_consumes (token_consumes _) _ _ _ h₂) l₁

/-- `parse_meta`: `ALL`, an alias or a user name as a `Meta<Username>` token (tried, as
`Option`), else `Meta::Only(T::parse(stream)?)` (without trailing whitespace); a user name is
turned into a `T` by `embed`. -/
def parseMeta (O : Oracles) (p : Parser α) (embed : String → α) : Parser (Meta α) := do
  match ← tryNonterminal (parseOption (token (metaToken O.char (usernameToken O)))) with
  | some .all => pure .all
  | some (.alias a) => pure (.alias a)
  | some (.only name) => pure (.only (embed name))
  | none =>
    let x ← p
    pure (.only x)

theorem parseMeta_consumes (O : Oracles) {p : Parser α} (hp : p.Consumes) (embed : String → α) :
    (parseMeta O p embed).Consumes := by
  intro s a s' h
  obtain ⟨r, s₁, h₁, h⟩ := run_bind_eq_ok.mp h
  cases r with
  | some m =>
    have l₁ := tryNonterminal_parseOption_consumesSome (token_consumes _) s m s₁ h₁
    cases m <;> (simp only [run_pure, Prod.mk.injEq] at h; obtain ⟨-, rfl⟩ := h; exact l₁)
  | none =>
    have l₁ := length_le_of_run h₁
    obtain ⟨x, s₂, h₂, h⟩ := run_bind_eq_ok.mp h
    simp only [run_pure, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    exact Nat.lt_of_lt_of_le (hp _ _ _ h₂) l₁

/-- `impl Parse for Meta<Identifier>`: `parse_meta(stream, Identifier::Name)`. -/
def metaIdentifier (O : Oracles) (D : Descriptions) : Parser (Meta Identifier) :=
  parseMeta O (identifier O D) Identifier.name

/-! ## `UserSpecifier`, `Meta<UserSpecifier>` -/

/-- `parse_user` inside `UserSpecifier::parse`: `%` (group) or `%:` (non-Unix group) and an
expected `Identifier`; `+` is the fatal `"netgroups are not supported yet"`; else a tried
`Identifier`. -/
def parseUser (O : Oracles) (D : Descriptions) : Parser UserSpecifier := do
  let percent ← eatChar '%'
  if percent then
    let nonunix ← eatChar ':'
    let ident ← expectNonterminal D.identifier (identifier O D)
    pure (if nonunix then .nonunixGroup ident else .group ident)
  else
    let plus ← eatChar '+'
    if plus then
      fatalHere .netgroupsNotSupported
    else
      let ident ← tryNonterminal (identifier O D)
      pure (.user ident)

/-- `impl Parse for UserSpecifier`. A `"` starts a quoted user: the text up to the next `"` is
read as an `Unquoted<Username>` token (expected; every character `Username` escapes gets a `\`),
and `parse_user` runs on a new stream over that text that starts at the position after the
`"`. Its result is taken as is, also when it did not read the whole text; positions in its
errors are positions in the re-escaped text. A `Reject` from it is returned after the quote was
consumed (F-P3). -/
def userSpecifier (O : Oracles) (D : Descriptions) : Parser UserSpecifier := do
  let quote ← eatChar '"'
  if quote then
    let beginPos ← getPos
    let text ← expectNonterminal D.username (token (unquotedToken O.char (usernameToken O)))
    let r ← nested (parseUser O D) (Stream.newWithPos text.toList beginPos)
    let result ← lift r
    expectSyntax '"'
    pure result
  else
    parseUser O D

/-- `impl Many for UserSpecifier {}`. -/
def userSpecifierMany : Many := {}

theorem parseUser_consumes (O : Oracles) (D : Descriptions) : (parseUser O D).Consumes := by
  intro s a s' h
  obtain ⟨b, s₁, h₁, h⟩ := run_bind_eq_ok.mp h
  cases b with
  | true =>
    exact Nat.lt_of_le_of_lt (length_le_of_run h) (run_eatChar_true_lt h₁)
  | false =>
    simp only [Bool.false_eq_true, ite_false] at h
    have l₁ := length_le_of_run h₁
    obtain ⟨b', s₂, h₂, h⟩ := run_bind_eq_ok.mp h
    have l₂ := length_le_of_run h₂
    cases b' with
    | true => simp at h
    | false =>
      simp only [Bool.false_eq_true, ite_false] at h
      obtain ⟨x, s₃, h₃, h⟩ := run_bind_eq_ok.mp h
      simp only [run_pure, Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      have := tryNonterminal_consumes (identifier_consumes O D) _ _ _ h₃
      omega

theorem userSpecifier_consumes (O : Oracles) (D : Descriptions) :
    (userSpecifier O D).Consumes := by
  intro s a s' h
  obtain ⟨b, s₁, h₁, h⟩ := run_bind_eq_ok.mp h
  cases b with
  | true =>
    exact Nat.lt_of_le_of_lt (length_le_of_run h) (run_eatChar_true_lt h₁)
  | false =>
    simp only [Bool.false_eq_true, ite_false] at h
    exact Nat.lt_of_lt_of_le (parseUser_consumes O D _ _ _ h) (length_le_of_run h₁)

/-- `impl Parse for Meta<UserSpecifier>`: `parse_meta` with `User(Identifier::Name(name))`. -/
def metaUserSpecifier (O : Oracles) (D : Descriptions) : Parser (Meta UserSpecifier) :=
  parseMeta O (userSpecifier O D) (fun name => .user (.name name))

/-- `SpecList<UserSpecifier>` (`Vec<Qualified<Meta<UserSpecifier>>>`). -/
def specListUserSpecifier (O : Oracles) (D : Descriptions) : Parser (SpecList UserSpecifier) :=
  specList userSpecifierMany D.userSpecifier (metaUserSpecifier O D)

/-- `SpecList<Identifier>`. -/
def specListIdentifier (O : Oracles) (D : Descriptions) : Parser (SpecList Identifier) :=
  specList identifierMany D.identifier (metaIdentifier O D)

/-! ## `RunAs` -/

/-- `impl Parse for RunAs`:
```
try_syntax('(', stream)?;
let users = try_nonterminal(stream).unwrap_or_default();
let groups = maybe(try_syntax(':', stream).and_then(|_| try_nonterminal(stream)))?
    .unwrap_or_default();
expect_syntax(')', stream)?;
```
`unwrap_or_default` discards every error of the user list, fatal ones included, and the stream
stays where the list stopped. A `:` followed by a rejected group list gives no groups, with the
`:` consumed. -/
def runAs (O : Oracles) (D : Descriptions) : Parser RunAs := do
  trySyntax '('
  let usersResult ← observe (tryNonterminal (specListUserSpecifier O D))
  let users := match usersResult with
    | .ok users => users
    | .error _ => []
  let groups ← Parser.maybe (do
    trySyntax ':'
    tryNonterminal (specListIdentifier O D))
  expectSyntax ')'
  pure ⟨users, groups.getD []⟩

/-! ## `MetaOrTag`, `CommandSpec` -/

/-- `impl Parse for MetaOrTag`: an `AliasName` keyword, then by keyword: a tag and `:`,
`CWD=` and a `ChDir`, `APPARMOR_PROFILE=` and a `StringParameter`, the fatal errors for
unsupported tags, an ignored tag (its span runs from the keyword to after the trailing
whitespace, before the `:`), `ALL`, or an alias name (fatal if followed by `=`). -/
def metaOrTag (O : Oracles) (D : Descriptions) : Parser (Meta Modifier) := do
  let startPos ← getPos
  let keyword ← tryNonterminal (token aliasNameToken)
  let switch (m : Modifier) : Parser (Meta Modifier) := do
    expectSyntax ':'
    pure (.only m)
  match keyword with
  | "EXEC" => switch .exec
  | "NOEXEC" => switch .noexec
  | "SETENV" => switch .setenv
  | "NOSETENV" => switch .nosetenv
  | "PASSWD" => switch .passwd
  | "NOPASSWD" => switch .nopasswd
  | "CWD" =>
    expectSyntax '='
    let path ← expectNonterminal D.chDir (token (chDirToken O))
    pure (.only (.cwd path))
  | "INTERCEPT" | "CHROOT" | "TIMEOUT" | "NOTBEFORE" | "NOTAFTER" =>
    fatalFrom startPos (.notSupported keyword)
  | "ROLE" | "TYPE" => fatalFrom startPos .selinuxNotSupported
  | "LOG_INPUT" | "NOLOG_INPUT" | "LOG_OUTPUT" | "NOLOG_OUTPUT" | "MAIL" | "NOMAIL" | "FOLLOW" =>
    let here ← getPos
    expectSyntax ':'
    pure (.only (.ignored ⟨startPos, here⟩))
  | "NOFOLLOW" | "NOINTERCEPT" => switch .noop
  | "APPARMOR_PROFILE" =>
    expectSyntax '='
    let profile ← expectNonterminal D.stringParameter (token (stringParameterToken O.char))
    pure (.only (.apparmorProfile profile))
  | "ALL" => pure .all
  | alias =>
    let eq ← isSyntax '='
    if eq then fatalFrom startPos (.unsupportedModifier alias) else pure (.alias alias)

theorem metaOrTag_consumes (O : Oracles) (D : Descriptions) : (metaOrTag O D).Consumes :=
  Consumes.bind_right _ fun _ => Consumes.bind_left (tryNonterminal_consumes (token_consumes _)) _

/-- One iteration of the loop of `CommandSpec::parse` after a `MetaOrTag` was read: a tag is
pushed (`tags.len() > Identifier::LIMIT` is fatal, so at most 127 tags); `ALL` and an alias end
the command spec (`inr`). -/
def commandSpecBody (tags : List Modifier) (kw : Meta Modifier) :
    Parser (Step (List Modifier) (List Modifier ⊕ CommandSpec)) :=
  match kw with
  | .only m =>
    let tags := tags ++ [m]
    if tags.length > identifierMany.limit then fatalHere .tooManyTags else pure (.next tags)
  | .all => pure (.done (.inr ⟨tags, .allow .all⟩))
  | .alias name => pure (.done (.inr ⟨tags, .allow (.alias name)⟩))

/-- `Spec<Command>`: a qualified `Meta<Command>` token. -/
def specCommand (O : Oracles) (D : Descriptions) : Parser (Spec Command) :=
  spec D.command (token (metaToken O.char (commandToken O)))

/-- `impl Parse for CommandSpec`:
`while let Some(MetaOrTag(keyword)) = try_nonterminal(stream)? { .. }`, then an expected
`Spec<Command>`. -/
def commandSpec (O : Oracles) (D : Descriptions) : Parser CommandSpec := do
  let r ← whileSome (tryNonterminal (parseOption (metaOrTag O D)))
    (tryNonterminal_parseOption_consumesSome (metaOrTag_consumes O D)) commandSpecBody .inl []
  match r with
  | .inr cs => pure cs
  | .inl tags =>
    let cmd ← expectNonterminal D.command (specCommand O D)
    pure ⟨tags, cmd⟩

/-! ## The permission tuples -/

/-- `impl Parse for (Option<RunAs>, CommandSpec)`: an optional `RunAs`; after one the command
spec is expected, else tried. -/
def runasCommand (O : Oracles) (D : Descriptions) : Parser (Option RunAs × CommandSpec) := do
  let runas ← tryNonterminal (parseOption (runAs O D))
  let cmd ← if runas.isSome then
      expectNonterminal D.commandSpec (commandSpec O D)
    else
      tryNonterminal (commandSpec O D)
  pure (runas, cmd)

/-- `impl Many for (Option<RunAs>, CommandSpec) {}`. -/
def runasCommandMany : Many := {}

/-- `impl Parse for (SpecList<Hostname>, Vec<(Option<RunAs>, CommandSpec)>)`: hosts (tried),
`=` (expected), the command list (expected). -/
def hostsRunasCommands (O : Oracles) (D : Descriptions) :
    Parser (SpecList Hostname × List (Option RunAs × CommandSpec)) := do
  let hosts ← tryNonterminal (specListHostname O.char D)
  expectSyntax '='
  let runasCmds ← expectNonterminal D.runasCommand
    (parseVec runasCommandMany D.runasCommand (runasCommand O D))
  pure (hosts, runasCmds)

/-- `impl Many for (SpecList<Hostname>, Vec<..>)`: separated by `:`. -/
def hostsRunasCommandsMany : Many := { sep := ':' }

/-- `Vec<(SpecList<Hostname>, Vec<(Option<RunAs>, CommandSpec)>)>`, the `permissions` of a
`PermissionSpec`. -/
def permissions (O : Oracles) (D : Descriptions) :
    Parser (List (SpecList Hostname × List (Option RunAs × CommandSpec))) :=
  parseVec hostsRunasCommandsMany D.hostsRunasCommands (hostsRunasCommands O D)

/-! ## Alias definitions -/

/-- `is_reserved_alias`. -/
def isReservedAlias (name : String) : Bool :=
  name == "ALL" || name == "CHROOT" || name == "CWD" || name == "NOTAFTER" ||
    name == "NOTBEFORE" || name == "ROLE" || name == "TIMEOUT" || name == "TYPE"

/-- `impl Parse for Def<T>`: an `AliasName` (tried; fatal if reserved), `=` (expected), the
`SpecList<T>` (expected, with `T::DESCRIPTION`). `p` parses `Meta<T>`, `m` is `T`'s `Many`. -/
def defParser (m : Many) (description : String) (p : Parser (Meta α)) : Parser (Def α) := do
  let beginPos ← getPos
  let name ← tryNonterminal (token aliasNameToken)
  if isReservedAlias name then
    fatalFrom beginPos (.reservedAliasName name)
  else
    expectSyntax '='
    let items ← expectNonterminal description (specList m description p)
    pure ⟨name, items⟩

/-- `impl<T> Many for Def<T>`: separated by `:`. -/
def defMany : Many := { sep := ':' }

/-- `Defs<T> = Vec<Def<T>>`. -/
def defs (D : Descriptions) (m : Many) (description : String) (p : Parser (Meta α)) :
    Parser (List (Def α)) :=
  parseVec defMany D.def_ (defParser m description p)

end SudoersSpec.Syntax
