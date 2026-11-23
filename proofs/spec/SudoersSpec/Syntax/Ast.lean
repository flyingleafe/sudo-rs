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

end SudoersSpec.Syntax
