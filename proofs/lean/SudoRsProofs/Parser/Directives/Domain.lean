import SudoRsProofs.Parser.Directives.Reference
import SudoersSpec.Grammar.PermissionAtoms

/-! The directive key is read from a successful nonempty list, never from an arbitrary
`String`. Derive its byte bound from the username-token bounds and the reference grammar. -/

open Aeneas Aeneas.Std SudoersSpec
open SudoersSpec.Grammar

namespace SudoRsProofs.Parser

private abbrev D := Syntax.Descriptions.release

/-- Only this branch of `get_directive` calls `chars_of` on the key. -/
def DirectiveKeyFits : Spec UserSpecifier → Prop
  | .allow (.only (.user (.name text))) => text.utf8ByteSize ≤ Usize.max
  | _ => True

private theorem gram_value_bound {α : Type} {p : Syntax.Parser α} {G : Gram α} {P : α → Prop}
    (hc : Complete p G) (hp : ∀ s a t, p.run s = (.ok a, t) → P a)
    {c a rest} (hg : G c a rest) : P a := by
  obtain ⟨t, ht, _⟩ := hc c a rest (Syntax.Stream.new (c ++ rest)) hg rfl
  exact hp _ _ _ ht

private theorem identifier_name_bound {O : Syntax.Oracles}
    (hn : ∀ c text r, UsernameG O c text r → text.utf8ByteSize ≤ Usize.max)
    {c text r} (h : IdentifierG O c (.name text) r) : text.utf8ByteSize ≤ Usize.max := by
  obtain ⟨_, _, b, _, _, h⟩ := h
  cases b
  · obtain ⟨v, ⟨_, _, _, hp, _⟩, he⟩ := h
    cases he
    exact hn _ _ _ hp
  · obtain ⟨_, _, he⟩ := h
    cases he

private theorem direct_user_name_bound {O : Syntax.Oracles}
    (hn : ∀ c text r, UsernameG O c text r → text.utf8ByteSize ≤ Usize.max)
    {c text r} (h : ParseUserG O c (.user (.name text)) r) : text.utf8ByteSize ≤ Usize.max := by
  obtain ⟨_, _, grp, _, _, h⟩ := h
  cases grp
  · obtain ⟨_, _, plus, _, _, h⟩ := h
    cases plus
    · obtain ⟨v, ⟨_, _, _, hi, _⟩, he⟩ := h
      cases he
      exact identifier_name_bound hn hi
    · exact False.elim h
  · obtain ⟨_, _, nonunix, _, _, h⟩ := h
    obtain ⟨_, _, he⟩ := h
    cases nonunix <;> cases he

private theorem user_name_bound {O : Syntax.Oracles}
    (hn : ∀ c text r, UsernameG O c text r → text.utf8ByteSize ≤ Usize.max)
    {c text r} (h : UserSpecifierG O c (.user (.name text)) r) : text.utf8ByteSize ≤ Usize.max := by
  obtain ⟨_, _, q, _, _, h⟩ := h
  cases q
  · exact direct_user_name_bound hn h
  · obtain ⟨_, _, _, _, _, ⟨_, _, _, hu⟩, _⟩ := h
    exact direct_user_name_bound hn hu

private theorem meta_user_name_bound {O : Syntax.Oracles}
    (hn : ∀ c text r, UsernameG O c text r → text.utf8ByteSize ≤ Usize.max)
    (hm : ∀ c text r, TokenG (MetaUsernameToken O) c (.only text) r → text.utf8ByteSize ≤ Usize.max)
    {c text r} (h : MetaUserG O c (.only (.user (.name text))) r) :
    text.utf8ByteSize ≤ Usize.max := by
  obtain ⟨_, _, opt, _, ⟨_, _, _, ho, _⟩, h⟩ := h
  cases opt with
  | none =>
    obtain ⟨_, hv, he⟩ := h
    cases he
    exact user_name_bound hn hv
  | some m =>
    cases ho with
    | some hv =>
      cases m with
      | all => exact False.elim (by cases h.2)
      | «alias» _ => exact False.elim (by cases h.2)
      | «only» v =>
        have hv' : text = v := by simpa [PureG] using h.2
        subst text
        exact hm _ _ _ hv

private theorem qual_user_key_bound {O : Syntax.Oracles}
    (hn : ∀ c text r, UsernameG O c text r → text.utf8ByteSize ≤ Usize.max)
    (hm : ∀ c text r, TokenG (MetaUsernameToken O) c (.only text) r → text.utf8ByteSize ≤ Usize.max)
    {c a r} (h : QualG (MetaUserG O) c a r) : DirectiveKeyFits a := by
  cases h with
  | @mk n _ _ v _ _ _ hv =>
    unfold SudoersSpec.Grammar.Qualified.ofBangs
    split
    · rcases v with _ | u | _
      · trivial
      · cases u with
        | user i =>
          cases i with
          | id _ => trivial
          | «name» a =>
            obtain ⟨_, _, _, hx, _⟩ := hv
            exact meta_user_name_bound hn hm hx
        | group => trivial
        | nonunixGroup => trivial
      · trivial
    · trivial

/-- The successful reference user list has a head, room for the hash-ID prepend, and
representable character-vector conversions for possible directive keys. -/
theorem user_list_domain_of_tokens {O : Syntax.Oracles}
    (hn : ∀ s text t, (Syntax.token (Syntax.usernameToken O)).run s = (.ok text, t) →
      text.utf8ByteSize ≤ Usize.max)
    (hm : ∀ s text t, (Syntax.token (Syntax.metaToken O.char (Syntax.usernameToken O))).run s =
      (.ok (.only text), t) → text.utf8ByteSize ≤ Usize.max)
    {s t : Syntax.Stream} {xs : SpecList UserSpecifier}
    (h : (Syntax.specListUserSpecifier O D).run s = (.ok xs, t)) :
    xs ≠ [] ∧ xs.length ≤ 127 ∧ ∀ key ∈ xs, DirectiveKeyFits key := by
  have hk : ∀ s a t, (Syntax.qualified D.userSpecifier (Syntax.metaUserSpecifier O D)).run s =
      (.ok a, t) → DirectiveKeyFits a := by
    intro s a t h
    obtain ⟨_, _, hg⟩ := qualified_sound (parseMeta_sound O (userSpecifier_sound O D)
      (fun x => .user (.name x))) D.userSpecifier s a t h
    have hw : ∀ c text r, UsernameG O c text r → text.utf8ByteSize ≤ Usize.max :=
      fun _ _ _ hg => gram_value_bound (token_complete _) hn hg
    let P : Meta String → Prop := fun m => match m with
      | .only x => x.utf8ByteSize ≤ Usize.max
      | _ => True
    have hp : ∀ s a t, (Syntax.token (MetaUsernameToken O)).run s = (.ok a, t) → P a := by
      intro s a t h
      cases a with
      | «only» a => exact hm s a t h
      | all => trivial
      | «alias» => trivial
    have hv : ∀ c text r, TokenG (MetaUsernameToken O) c (.only text) r →
        text.utf8ByteSize ≤ Usize.max :=
      fun _ _ _ hg => gram_value_bound (P := P) (token_complete _) hp hg
    exact qual_user_key_bound hw hv hg
  refine ⟨Syntax.parseList_ne_nil h, ?_⟩
  have hp := parseList_success hk h
  change xs.length ≤ max 1 127 ∧ ∀ a ∈ xs, DirectiveKeyFits a at hp
  simpa only [Nat.max_eq_right (by decide : 1 ≤ 127)] using hp

end SudoRsProofs.Parser
