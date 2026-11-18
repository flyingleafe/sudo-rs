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
  · simp [(Slice.eq_iff a b).mpr h]
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

/-! ## `match_command` -/

section Command

variable {A : GlobAbs}

/-- `OsString == OsString`, read through an injective abstraction. -/
theorem os_eq_eq (hinj : Function.Injective A.os) (a b : std.ffi.os_str.OsString) :
    std.ffi.os_str.OsString.Insts.CoreCmpPartialEqOsString.eq a b = ok (A.os a == A.os b) := by
  simp only [std.ffi.os_str.OsString.Insts.CoreCmpPartialEqOsString.eq]
  congr 1
  by_cases h : a = b
  · simp [h]
  · have : A.os a ≠ A.os b := fun e => h (hinj e)
    simp [h, this]

/-- An element-wise `allM` over a `zip` whose comparison is `==` on abstractions is
`isPrefixOf` on the abstracted lists. -/
theorem allM_zip_isPrefixOf {α : Type} (f : α → String) :
    ∀ l1 l2 : List α, l1.length ≤ l2.length →
      List.allM (fun p : α × α => (ok (f p.1 == f p.2) : Result Bool)) (l1.zip l2) =
        ok ((l1.map f).isPrefixOf (l2.map f))
  | [], l2, _ => by simp; rfl
  | _ :: _, [], h => by simp at h
  | a :: l1, b :: l2, h => by
    simp only [List.zip_cons_cons, List.allM, List.map_cons, List.isPrefixOf]
    cases hab : (f a == f b)
    · simp; rfl
    · simp [allM_zip_isPrefixOf f l1 l2 (by simpa using h)]

theorem isPrefixOf_eq_false_of_length {α : Type} [BEq α] [LawfulBEq α] (l1 l2 : List α)
    (h : l2.length < l1.length) : l1.isPrefixOf l2 = false := by
  cases hp : l1.isPrefixOf l2
  · rfl
  · have := (List.isPrefixOf_iff_prefix.mp hp).length_le
    omega

/-- `args.starts_with(vec)` on `OsString` slices. -/
theorem starts_with_os_eq (hinj : Function.Injective A.os)
    (s vec : Slice std.ffi.os_str.OsString) :
    core.slice.Slice.starts_with sudo_rs.std.ffi.os_str.OsString.Insts.CoreCmpPartialEqOsString
      s vec = ok ((vec.val.map A.os).isPrefixOf (s.val.map A.os)) := by
  simp only [core.slice.Slice.starts_with, os_eq_eq hinj]
  split
  · rename_i h
    rw [isPrefixOf_eq_false_of_length (vec.val.map A.os) (s.val.map A.os) (by simpa using h)]
  · rename_i h
    exact allM_zip_isPrefixOf A.os _ _ (by omega)

/-- `args == vec` on `OsString` slices. -/
theorem slice_eq_os_eq (hinj : Function.Injective A.os)
    (s vec : Slice std.ffi.os_str.OsString) :
    core.slice.cmp.PartialEqSlice.eq sudo_rs.std.ffi.os_str.OsString.Insts.CoreCmpPartialEqOsString
      s vec = ok (s.val.map A.os == vec.val.map A.os) := by
  have hne : ∀ x y, (sudo_rs.std.ffi.os_str.OsString.Insts.CoreCmpPartialEqOsString).ne x y
      ⦃ b => b ↔ ¬ x = y ⦄ := by
    intro x y
    simp [core.cmp.PartialEq.ne.default, std.ffi.os_str.OsString.Insts.CoreCmpPartialEqOsString.eq]
  obtain ⟨b, hb, hbv⟩ := exists_eq_ok_of_spec
    (core.slice.cmp.PartialEqSlice.eq_homo_spec _ s vec hne)
  rw [hb]
  congr 1
  have hmap : Function.Injective (List.map A.os) := List.map_injective_iff.mpr hinj
  by_cases h : s = vec
  · subst h; simpa using hbv
  · have h1 : s.val ≠ vec.val := fun e => h (Slice.ext _ _ e)
    have h2 : s.val.map A.os ≠ vec.val.map A.os := fun e => h1 (hmap e)
    simp only [h, iff_false] at hbv
    simp [hbv, h2]

/-- **The closure of `match_command(path, args)` is `matchCommand O path args`.** -/
theorem match_command_call (hG : GlobOracle A O) (path : std.path.Path)
    (args : Slice std.ffi.os_str.OsString) (x : glob.Pattern × sudo_rs.sudoers.tokens.Args) :
    (matchCommandFn).call (path, matchCommandOptions, args) x =
      ok (SudoersSpec.matchCommand O (A.path path) (args.val.map A.os) (absCommand A x)) := by
  obtain ⟨pat, a⟩ := x
  simp only [sudo_rs.sudoers.match_command.closure.Insts.CoreOpsFunctionFnTupleShared2PairPatternArgsBool.call,
    uncurry]
  rw [hG.glob_matches]
  simp only [bind_ok]
  cases hb : O.globMatches (A.pat pat) (A.path path)
  · simp [SudoersSpec.matchCommand, absCommand, hb]
  · cases a with
    | Prefix vec =>
      simp [starts_with_os_eq hG.os_inj, SudoersSpec.matchCommand, SudoersSpec.argsMatch,
        absCommand, absArgs, hb]
    | Exact vec =>
      simp [Box.Insts.CoreConvertAsRef.as_ref, slice_eq_os_eq hG.os_inj,
        SudoersSpec.matchCommand, SudoersSpec.argsMatch, absCommand, absArgs, hb]

@[step]
theorem match_command_spec (hG : GlobOracle A O) (path : std.path.Path)
    (args : Slice std.ffi.os_str.OsString) :
    sudo_rs.sudoers.match_command (path, args) ⦃ c => c = (path, matchCommandOptions, args) ∧
      ∀ x, (matchCommandFn).call c x =
        ok (SudoersSpec.matchCommand O (A.path path) (args.val.map A.os) (absCommand A x)) ⦄ := by
  simp only [sudo_rs.sudoers.match_command, glob.MatchOptions.new, bind_ok]
  exact spec_of_eq_ok rfl ⟨rfl, match_command_call hG path args⟩

end Command

/-! ## Instantiations of the first layer

`find_item`, `item_verdict` and `get_aliases` applied to the matcher closures, for every list and
alias table `check_permission` scans:
* user list of a rule (`match_user am_user`) and runas user list (`match_user request.user`):
  `find_item_match_user_spec`, `find_item_runas_users_spec`;
* host list (`match_token on_host`): `find_item_match_token_spec`;
* runas group list (`match_group request.group`): `find_item_match_group_spec`,
  `find_item_runas_groups_spec`;
* command entry / list (`match_command (command, arguments)`):
  `item_verdict_match_command_spec`, `find_item_match_command_spec`;
* alias tables: `get_aliases_match_user_spec` (`aliases.user` with `am_user`, `aliases.runas`
  with `request.user`), `get_aliases_match_group_alias_spec` (`aliases.runas` with
  `request.group`), `get_aliases_match_token_spec` (`aliases.host`),
  `get_aliases_match_command_spec` (`aliases.cmnd`).
-/

section Instances

variable {A : GlobAbs}

/-- `find_item` over a user specifier list with the closure of `match_user u`. -/
theorem find_item_match_user_spec (hO : InstOracle uInst eqInst gInst O) (u : U)
    (items : Slice (RSpec sudo_rs.sudoers.ast.UserSpecifier)) (v : sudo_rs.sudoers.FoundAliases)
    (hv : FoundFits v) (hi : ItemsFit items.val) (hg : ItemsGood UserSpecFits items.val) :
    sudo_rs.sudoers.find_item (matchUserFn uInst) items u v ⦃ b =>
      b = (SudoersSpec.findItem (SudoersSpec.matchUser O u) (absFound v)
        (SudoersSpec.withUnit (absSpecList absUserSpecifier items.val))).isSome ⦄ :=
  find_item_spec _ u absUserSpecifier _ UserSpecFits (match_user_call hO u) items v hv hi hg

/-- `find_item` over the user list of a `RunAs` with the closure of `match_user u`. -/
theorem find_item_runas_users_spec (hO : InstOracle uInst eqInst gInst O) (u : U)
    (ra : sudo_rs.sudoers.ast.RunAs) (v : sudo_rs.sudoers.FoundAliases) (hv : FoundFits v)
    (hi : ItemsFit ra.users.val) (hg : ItemsGood UserSpecFits ra.users.val) :
    sudo_rs.sudoers.find_item (matchUserFn uInst) (alloc.vec.Vec.deref ra.users) u v ⦃ b =>
      b = (SudoersSpec.findItem (SudoersSpec.matchUser O u) (absFound v)
        (SudoersSpec.withUnit (absRunAs ra).users)).isSome ⦄ := by
  have := find_item_match_user_spec hO u (alloc.vec.Vec.deref ra.users) v hv
    (by simpa using hi) (by simpa using hg)
  simpa [absRunAs] using this

/-- `find_item` over a runas group list with the closure of `match_group g`. -/
theorem find_item_match_group_spec (hO : InstOracle uInst eqInst gInst O) (g : G)
    (items : Slice (RSpec sudo_rs.sudoers.ast.Identifier)) (v : sudo_rs.sudoers.FoundAliases)
    (hv : FoundFits v) (hi : ItemsFit items.val) (hg : ItemsGood IdentFits items.val) :
    sudo_rs.sudoers.find_item (matchGroupFn gInst) items g v ⦃ b =>
      b = (SudoersSpec.findItem (SudoersSpec.matchGroup O g) (absFound v)
        (SudoersSpec.withUnit (absSpecList absIdentifier items.val))).isSome ⦄ :=
  find_item_spec _ g absIdentifier _ IdentFits (match_group_call hO g) items v hv hi hg

/-- `find_item` over the group list of a `RunAs` with the closure of `match_group g`. -/
theorem find_item_runas_groups_spec (hO : InstOracle uInst eqInst gInst O) (g : G)
    (ra : sudo_rs.sudoers.ast.RunAs) (v : sudo_rs.sudoers.FoundAliases) (hv : FoundFits v)
    (hi : ItemsFit ra.groups.val) (hg : ItemsGood IdentFits ra.groups.val) :
    sudo_rs.sudoers.find_item (matchGroupFn gInst) (alloc.vec.Vec.deref ra.groups) g v ⦃ b =>
      b = (SudoersSpec.findItem (SudoersSpec.matchGroup O g) (absFound v)
        (SudoersSpec.withUnit (absRunAs ra).groups)).isSome ⦄ := by
  have := find_item_match_group_spec hO g (alloc.vec.Vec.deref ra.groups) v hv
    (by simpa using hi) (by simpa using hg)
  simpa [absRunAs] using this

/-- `find_item` over a host list with the closure of `match_token(host)`. -/
theorem find_item_match_token_spec (hH : O.SudoRsHosts) (host : String) (text : Str)
    (ht : text.val = sudo_rs.stringBytes host)
    (items : Slice (RSpec sudo_rs.sudoers.tokens.Hostname)) (v : sudo_rs.sudoers.FoundAliases)
    (hv : FoundFits v) (hi : ItemsFit items.val) (hg : ItemsGood Fits items.val) :
    sudo_rs.sudoers.find_item (matchTokenFn) items text v ⦃ b =>
      b = (SudoersSpec.findItem (SudoersSpec.matchHost O host) (absFound v)
        (SudoersSpec.withUnit (absSpecList id items.val))).isSome ⦄ :=
  find_item_spec _ text id _ Fits (match_token_call hH host text ht) items v hv hi hg

/-- `item_verdict` of one command entry with the closure of `match_command(path, args)`. -/
theorem item_verdict_match_command_spec (hG : GlobOracle A O) (path : std.path.Path)
    (args : Slice std.ffi.os_str.OsString)
    (item : RSpec (glob.Pattern × sudo_rs.sudoers.tokens.Args))
    (v : sudo_rs.sudoers.FoundAliases) (hv : FoundFits v)
    (hi : ∀ n, aliasName item = some n → Fits n) :
    sudo_rs.sudoers.item_verdict (matchCommandFn) item (path, matchCommandOptions, args) v
      ⦃ o => o = itemVerdict (SudoersSpec.matchCommand O (A.path path) (args.val.map A.os))
        (absFound v) (absSpec (absCommand A) item) ⦄ :=
  item_verdict_spec _ _ (absCommand A) _ (fun _ => True)
    (fun x _ => match_command_call hG path args x) item v hv hi (fun _ _ => trivial)

/-- `find_item` over a command list with the closure of `match_command(path, args)`. -/
theorem find_item_match_command_spec (hG : GlobOracle A O) (path : std.path.Path)
    (args : Slice std.ffi.os_str.OsString)
    (items : Slice (RSpec (glob.Pattern × sudo_rs.sudoers.tokens.Args)))
    (v : sudo_rs.sudoers.FoundAliases) (hv : FoundFits v) (hi : ItemsFit items.val) :
    sudo_rs.sudoers.find_item (matchCommandFn) items (path, matchCommandOptions, args) v ⦃ b =>
      b = (SudoersSpec.findItem (SudoersSpec.matchCommand O (A.path path) (args.val.map A.os))
        (absFound v) (SudoersSpec.withUnit (absSpecList (absCommand A) items.val))).isSome ⦄ :=
  find_item_spec _ _ (absCommand A) _ (fun _ => True)
    (fun x _ => match_command_call hG path args x) items v hv hi (fun _ _ _ _ => trivial)

/-- `get_aliases` of a user-specifier table (`aliases.user`, `aliases.runas`) with the closure
of `match_user u`. -/
theorem get_aliases_match_user_spec (hO : InstOracle uInst eqInst gInst O) (u : U)
    (table : sudo_rs.sudoers.VecOrd (RDef sudo_rs.sudoers.ast.UserSpecifier))
    (hwf : TableWF table) (hfit : TableFits table) (hgood : TableGood UserSpecFits table) :
    sudo_rs.sudoers.get_aliases (matchUserFn uInst) table u ⦃ r =>
      absFound r = SudoersSpec.getAliases (absTable absUserSpecifier table)
        (SudoersSpec.matchUser O u) ∧ FoundFits r ⦄ :=
  get_aliases_spec _ u absUserSpecifier _ UserSpecFits (match_user_call hO u) table hwf hfit
    hgood

/-- `get_aliases` of the runas table with the closure of `match_group_alias g`. -/
theorem get_aliases_match_group_alias_spec (hO : InstOracle uInst eqInst gInst O) (g : G)
    (table : sudo_rs.sudoers.VecOrd (RDef sudo_rs.sudoers.ast.UserSpecifier))
    (hwf : TableWF table) (hfit : TableFits table) (hgood : TableGood UserSpecFits table) :
    sudo_rs.sudoers.get_aliases (matchGroupAliasFn gInst) table g ⦃ r =>
      absFound r = SudoersSpec.getAliases (absTable absUserSpecifier table)
        (SudoersSpec.matchGroupAlias O g) ∧ FoundFits r ⦄ :=
  get_aliases_spec _ g absUserSpecifier _ UserSpecFits (match_group_alias_call hO g) table hwf
    hfit hgood

/-- `get_aliases` of the host table with the closure of `match_token(host)`. -/
theorem get_aliases_match_token_spec (hH : O.SudoRsHosts) (host : String) (text : Str)
    (ht : text.val = sudo_rs.stringBytes host)
    (table : sudo_rs.sudoers.VecOrd (RDef sudo_rs.sudoers.tokens.Hostname))
    (hwf : TableWF table) (hfit : TableFits table) (hgood : TableGood Fits table) :
    sudo_rs.sudoers.get_aliases (matchTokenFn) table text ⦃ r =>
      absFound r = SudoersSpec.getAliases (absTable id table) (SudoersSpec.matchHost O host) ∧
        FoundFits r ⦄ :=
  get_aliases_spec _ text id _ Fits (match_token_call hH host text ht) table hwf hfit hgood

/-- `get_aliases` of the command table with the closure of `match_command(path, args)`. -/
theorem get_aliases_match_command_spec (hG : GlobOracle A O) (path : std.path.Path)
    (args : Slice std.ffi.os_str.OsString)
    (table : sudo_rs.sudoers.VecOrd (RDef (glob.Pattern × sudo_rs.sudoers.tokens.Args)))
    (hwf : TableWF table) (hfit : TableFits table) :
    sudo_rs.sudoers.get_aliases (matchCommandFn) table (path, matchCommandOptions, args) ⦃ r =>
      absFound r = SudoersSpec.getAliases (absTable (absCommand A) table)
        (SudoersSpec.matchCommand O (A.path path) (args.val.map A.os)) ∧ FoundFits r ⦄ :=
  get_aliases_spec _ _ (absCommand A) _ (fun _ => True)
    (fun x _ => match_command_call hG path args x) table hwf hfit (fun _ _ _ _ _ _ => trivial)

end Instances

end SudoRsProofs

/-! ## Axiom audit: only `propext`, `Classical.choice`, `Quot.sound`. -/

#print axioms SudoRsProofs.in_group_spec
#print axioms SudoRsProofs.in_group_eq
#print axioms SudoRsProofs.match_identifier_eq
#print axioms SudoRsProofs.match_user_call
#print axioms SudoRsProofs.match_user_spec
#print axioms SudoRsProofs.match_group_call
#print axioms SudoRsProofs.match_group_spec
#print axioms SudoRsProofs.match_group_alias_call
#print axioms SudoRsProofs.match_group_alias_spec
#print axioms SudoRsProofs.system_hostname_deref_spec
#print axioms SudoRsProofs.tokens_hostname_deref_eq
#print axioms SudoRsProofs.match_token_call
#print axioms SudoRsProofs.match_token_spec
#print axioms SudoRsProofs.match_command_call
#print axioms SudoRsProofs.match_command_spec
#print axioms SudoRsProofs.find_item_match_user_spec
#print axioms SudoRsProofs.find_item_runas_users_spec
#print axioms SudoRsProofs.find_item_match_group_spec
#print axioms SudoRsProofs.find_item_runas_groups_spec
#print axioms SudoRsProofs.find_item_match_token_spec
#print axioms SudoRsProofs.item_verdict_match_command_spec
#print axioms SudoRsProofs.find_item_match_command_spec
#print axioms SudoRsProofs.get_aliases_match_user_spec
#print axioms SudoRsProofs.get_aliases_match_group_alias_spec
#print axioms SudoRsProofs.get_aliases_match_token_spec
#print axioms SudoRsProofs.get_aliases_match_command_spec
