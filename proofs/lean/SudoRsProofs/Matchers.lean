import SudoRsProofs.GetAliases
import SudoRsProofs.AbsMatch

/-!
# The matchers refine the `Oracle`-based matching of the spec

For each matcher of `src/sudoers/mod.rs` the extracted function, or the `Fn::call` of the
closure it returns, equals the spec's matching function (`SudoersSpec.matchUser`, `matchGroup`,
`matchGroupAlias`, `matchHost`, `matchCommand`, `inGroup`, `matchIdentifier`) on the abstracted
arguments, under the hypotheses `InstOracle` / `GlobOracle` / `Oracle.SudoRsHosts` and the
side condition that the names the closure dereferences fit in memory (`IdentFits`,
`UserSpecFits`, `Fits`).

The closure theorems have the shape `∀ x, Good x → inst.call c x = ok (p (f x))` that
`item_verdict_spec`, `find_item_spec` and `get_aliases_spec` take, and the corollaries at the end
of the file instantiate those with every list and alias table `check_permission` scans.
-/

open Aeneas Aeneas.Std Result

namespace SudoRsProofs

/-- The `Fn` instance of the closure returned by `match_user`. -/
local notation "matchUserFn" uInst =>
  sudo_rs.sudoers.match_user.closure.Insts.CoreOpsFunctionFnTupleShared1UserSpecifierBool uInst
/-- The `Fn` instance of the closure returned by `match_group`. -/
local notation "matchGroupFn" gInst =>
  sudo_rs.sudoers.match_group.closure.Insts.CoreOpsFunctionFnTupleShared1IdentifierBool gInst
/-- The `Fn` instance of the closure returned by `match_group_alias`. -/
local notation "matchGroupAliasFn" gInst =>
  sudo_rs.sudoers.match_group_alias.closure.Insts.CoreOpsFunctionFnTupleShared1UserSpecifierBool
    gInst
/-- The `Fn` instance of the closure returned by `match_token` on `tokens::Hostname`. -/
local notation "matchTokenFn" =>
  sudo_rs.sudoers.match_token.closure.Insts.CoreOpsFunctionFnTupleShared1TBool
    sudo_rs.sudoers.tokens.Hostname.Insts.CoreOpsDerefDerefString
/-- The `Fn` instance of the closure returned by `match_command`. -/
local notation "matchCommandFn" =>
  sudo_rs.sudoers.match_command.closure.Insts.CoreOpsFunctionFnTupleShared2PairPatternArgsBool

variable {U G UG : Type} {uInst : sudo_rs.system.interface.UnixUser U UG}
  {eqInst : core.cmp.PartialEq U U} {gInst : sudo_rs.system.interface.UnixGroup G}
  {O : SudoersSpec.Oracle U G}

/-! ## Strings and `bool` equality -/

theorem decide_eq_beq {α : Type} [BEq α] [LawfulBEq α] (a b : α) [Decidable (a = b)] :
    decide (a = b) = (a == b) := by
  by_cases h : a = b <;> simp [h]

theorem decide_str_eq (a b : Str) [Decidable (a = b)] [Decidable (a.val = b.val)] :
    decide (a = b) = decide (a.val = b.val) := by
  by_cases h : a.val = b.val
  · simp [h, (Slice.eq_iff a b).mpr h]
  · have hne : a ≠ b := fun e => h (e ▸ rfl)
    simp [h, hne]

theorem SudoString.deref_eq (s : common.string.SudoString) (h : Fits s.str) :
    common.string.SudoString.Insts.CoreOpsDerefDerefStr.deref s = ok (strOf s.str h) :=
  strOfString_eq h

/-- `SudoString == &str` compares the bytes. -/
theorem SudoString.eq_eq (s : common.string.SudoString) (h : Fits s.str) (a : Str) :
    common.string.SudoString.Insts.CoreCmpPartialEqStr.eq s a =
      ok (decide (sudo_rs.stringBytes s.str = a.val)) := by
  simp only [common.string.SudoString.Insts.CoreCmpPartialEqStr.eq, SudoString.deref_eq s h,
    bind_ok, Str.Insts.CoreCmpPartialEqStr.eq, decide_str_eq, strOf_val]

/-! ## `in_group` -/

/-- **`in_group` is `inGroup`.** -/
@[step]
theorem in_group_spec (hO : InstOracle uInst eqInst gInst O) (u : U) (g : G) :
    sudo_rs.sudoers.in_group uInst gInst u g ⦃ b => b = SudoersSpec.inGroup O u g ⦄ := by
  unfold sudo_rs.sudoers.in_group
  apply WP.spec_bind (hO.as_gid g)
  intro x hx
  simp [hO.in_group_by_gid, hx, SudoersSpec.inGroup]

theorem in_group_eq (hO : InstOracle uInst eqInst gInst O) (u : U) (g : G) :
    sudo_rs.sudoers.in_group uInst gInst u g = ok (SudoersSpec.inGroup O u g) :=
  eq_ok_of_spec (in_group_spec hO u g)

/-! ## `match_identifier` -/

/-- **`match_identifier` is `matchIdentifier`.** -/
theorem match_identifier_eq (hO : InstOracle uInst eqInst gInst O) (u : U)
    (i : sudo_rs.sudoers.ast.Identifier) (hi : IdentFits i) :
    sudo_rs.sudoers.match_identifier uInst u i =
      ok (SudoersSpec.matchIdentifier O u (absIdentifier i)) := by
  cases i with
  | Name s =>
    have hs : Fits s.str := hi
    simp only [sudo_rs.sudoers.match_identifier, SudoString.deref_eq s hs, bind_ok]
    rw [hO.has_name u _ s.str (strOf_val _ _)]
    rfl
  | ID n =>
    simp [sudo_rs.sudoers.match_identifier, sudo_rs.system.interface.UserId.new, hO.has_uid,
      absIdentifier, SudoersSpec.matchIdentifier]

/-! ## `match_user` -/

/-- **The closure of `match_user u` is `matchUser O u`.** -/
theorem match_user_call (hO : InstOracle uInst eqInst gInst O) (u : U)
    (x : sudo_rs.sudoers.ast.UserSpecifier) (hx : UserSpecFits x) :
    (matchUserFn uInst).call u x = ok (SudoersSpec.matchUser O u (absUserSpecifier x)) := by
  cases x with
  | User i =>
    exact match_identifier_eq hO u i hx
  | Group i =>
    cases i <;>
      simp [sudo_rs.sudoers.match_user.closure.Insts.CoreOpsFunctionFnTupleShared1UserSpecifierBool.call,
        common.string.SudoString.as_cstr, hO.in_group_by_name, hO.in_group_by_gid,
        sudo_rs.system.interface.GroupId.new, absUserSpecifier, absIdentifier,
        SudoersSpec.matchUser]
  | NonunixGroup i =>
    simp [sudo_rs.sudoers.match_user.closure.Insts.CoreOpsFunctionFnTupleShared1UserSpecifierBool.call,
      sudoers.warn_ignored, absUserSpecifier, SudoersSpec.matchUser]

@[step]
theorem match_user_spec (hO : InstOracle uInst eqInst gInst O) (u : U) :
    sudo_rs.sudoers.match_user uInst u ⦃ c => ∀ x, UserSpecFits x →
      (matchUserFn uInst).call c x = ok (SudoersSpec.matchUser O u (absUserSpecifier x)) ⦄ := by
  simpa [sudo_rs.sudoers.match_user] using match_user_call hO u

/-! ## `match_group` -/

/-- **The closure of `match_group g` is `matchGroup O g`.** -/
theorem match_group_call (hO : InstOracle uInst eqInst gInst O) (g : G)
    (x : sudo_rs.sudoers.ast.Identifier) (hx : IdentFits x) :
    (matchGroupFn gInst).call g x = ok (SudoersSpec.matchGroup O g (absIdentifier x)) := by
  cases x with
  | Name s =>
    have hs : Fits s.str := hx
    obtain ⟨o, ho, hov⟩ := exists_eq_ok_of_spec (hO.try_as_name g)
    simp only [sudo_rs.sudoers.match_group.closure.Insts.CoreOpsFunctionFnTupleShared1IdentifierBool.call,
      ho, bind_ok]
    cases o with
    | none =>
      have : O.tryAsName g = none := by
        cases h : O.tryAsName g with
        | none => rfl
        | some t =>
          rw [h] at hov
          have : (none : Option (List U8)) = some (sudo_rs.stringBytes t) := hov
          cases this
      simp [this, absIdentifier, SudoersSpec.matchGroup]
    | some a =>
      obtain ⟨t, ht, hta⟩ : ∃ t, O.tryAsName g = some t ∧ sudo_rs.stringBytes t = a.val := by
        cases h : O.tryAsName g with
        | none =>
          rw [h] at hov
          have : some a.val = (none : Option (List U8)) := hov
          cases this
        | some t =>
          rw [h] at hov
          have : some a.val = some (sudo_rs.stringBytes t) := hov
          exact ⟨t, rfl, (Option.some.inj this).symm⟩
      simp only [core.option.Option.is_some_and_some,
        sudo_rs.sudoers.match_group.closure.closure.Insts.CoreOpsFunctionFnOnceTupleShared1StrBool,
        sudo_rs.sudoers.match_group.closure.closure.Insts.CoreOpsFunctionFnOnceTupleShared1StrBool.call_once,
        SudoString.eq_eq s hs, ← hta, stringBytes_inj, absIdentifier, SudoersSpec.matchGroup, ht]
      by_cases h : t = s.str
      · simp [h]
      · simp [h, Ne.symm h]
  | ID n =>
    obtain ⟨y, hy, hyv⟩ := exists_eq_ok_of_spec (hO.as_gid g)
    simp [sudo_rs.sudoers.match_group.closure.Insts.CoreOpsFunctionFnTupleShared1IdentifierBool.call,
      hy, sudo_rs.system.interface.GroupId.new,
      sudo_rs.system.interface.GroupId.Insts.CoreCmpPartialEqGroupId.eq, absIdentifier,
      SudoersSpec.matchGroup, ← hyv, decide_eq_beq, UScalar.eq_equiv]

@[step]
theorem match_group_spec (hO : InstOracle uInst eqInst gInst O) (g : G) :
    sudo_rs.sudoers.match_group gInst g ⦃ c => ∀ x, IdentFits x →
      (matchGroupFn gInst).call c x = ok (SudoersSpec.matchGroup O g (absIdentifier x)) ⦄ := by
  simpa [sudo_rs.sudoers.match_group] using match_group_call hO g

/-! ## `match_group_alias` -/

/-- **The closure of `match_group_alias g` is `matchGroupAlias O g`.** -/
theorem match_group_alias_call (hO : InstOracle uInst eqInst gInst O) (g : G)
    (x : sudo_rs.sudoers.ast.UserSpecifier) (hx : UserSpecFits x) :
    (matchGroupAliasFn gInst).call g x =
      ok (SudoersSpec.matchGroupAlias O g (absUserSpecifier x)) := by
  cases x with
  | User i =>
    simp only [sudo_rs.sudoers.match_group_alias.closure.Insts.CoreOpsFunctionFnTupleShared1UserSpecifierBool.call,
      sudo_rs.sudoers.match_group, bind_ok]
    exact match_group_call hO g i hx
  | Group i | NonunixGroup i =>
    simp [sudo_rs.sudoers.match_group_alias.closure.Insts.CoreOpsFunctionFnTupleShared1UserSpecifierBool.call,
      sudoers.warn_ignored, absUserSpecifier, SudoersSpec.matchGroupAlias]

@[step]
theorem match_group_alias_spec (hO : InstOracle uInst eqInst gInst O) (g : G) :
    sudo_rs.sudoers.match_group_alias gInst g ⦃ c => ∀ x, UserSpecFits x →
      (matchGroupAliasFn gInst).call c x =
        ok (SudoersSpec.matchGroupAlias O g (absUserSpecifier x)) ⦄ := by
  simpa [sudo_rs.sudoers.match_group_alias] using match_group_alias_call hO g

/-! ## Hostnames and `match_token` -/

/-- `Deref<Target = str>` for the current host name (`system::Hostname`). -/
@[step]
theorem system_hostname_deref_spec (h : sudo_rs.system.Hostname) (hf : Fits h.inner) :
    sudo_rs.system.Hostname.Insts.CoreOpsDerefDerefStr.deref h
      ⦃ s => s.val = sudo_rs.stringBytes (absSysHostname h) ⦄ := by
  simp [sudo_rs.system.Hostname.Insts.CoreOpsDerefDerefStr.deref, absSysHostname,
    alloc.string.String.Insts.CoreOpsDerefDerefStr.deref, strOfString_eq hf]

/-- `Deref<Target = String>` for a policy host name (`tokens::Hostname`) is the identity. -/
@[simp]
theorem tokens_hostname_deref_eq (h : sudo_rs.sudoers.tokens.Hostname) :
    sudo_rs.sudoers.tokens.Hostname.Insts.CoreOpsDerefDerefString.deref h = ok h := rfl

/-- **The closure of `match_token(host)` is `matchHost O host`** (sudo-rs compares host names
by string equality: `Oracle.SudoRsHosts`). -/
theorem match_token_call (hH : O.SudoRsHosts) (host : String) (text : Str)
    (ht : text.val = sudo_rs.stringBytes host) (x : sudo_rs.sudoers.tokens.Hostname)
    (hx : Fits x) :
    (matchTokenFn).call text x = ok (SudoersSpec.matchHost O host x) := by
  rw [SudoersSpec.matchHost, hH x host]
  simp only [sudo_rs.sudoers.match_token.closure.Insts.CoreOpsFunctionFnTupleShared1TBool.call,
    tokens_hostname_deref_eq, alloc.string.String.as_str, strOfString_eq hx, bind_ok,
    Str.Insts.CoreCmpPartialEqStr.eq]
  simp only [decide_str_eq, strOf_val, ht, stringBytes_inj]
  rw [decide_eq_beq]

@[step]
theorem match_token_spec (hH : O.SudoRsHosts) (host : String) (text : Str)
    (ht : text.val = sudo_rs.stringBytes host) :
    sudo_rs.sudoers.match_token sudo_rs.sudoers.tokens.Hostname.Insts.CoreOpsDerefDerefString
      text ⦃ c => ∀ x, Fits x → (matchTokenFn).call c x = ok (SudoersSpec.matchHost O host x) ⦄ := by
  simpa [sudo_rs.sudoers.match_token] using match_token_call hH host text ht

end SudoRsProofs
