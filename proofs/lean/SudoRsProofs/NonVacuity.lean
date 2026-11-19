import SudoRsProofs.ListValidate

/-! Two synthetic requests for the same policy and host. Identity comes from a finite
fixture, not NSS. The command path and the glob interface remain abstract: this is a
conditional witness for the refinement theorem, not a proof of the external matcher. -/

open Aeneas Aeneas.Std Result
open sudo_rs

namespace SudoRsProofs.NonVacuity

private def gid : U32 := 1#u32
private def uid (u : Bool) : U32 := if u then 1#u32 else 2#u32

private def groupInst : system.interface.UnixGroup Unit where
  as_gid _ := ok gid
  try_as_name _ := ok none

private def userInst : system.interface.UnixUser Bool Unit where
  UnixGroupInst := groupInst
  has_name _ _ := ok false
  has_uid u n := ok (uid u == n)
  is_root _ := ok false
  in_group_by_name _ _ := ok false
  in_group_by_gid _ n := ok (gid == n)
  group _ := ok ()

private def eqInst : core.cmp.PartialEq Bool Bool where
  eq u v := ok (u == v)
  ne u v := ok (!(u == v))

/-- The glob predicate is a parameter and is not queried by the fixture's literal `ALL`. -/
def oracle (g : String → String → Bool) : SudoersSpec.Oracle Bool Unit where
  hasName _ _ := false
  hasUid u n := (uid u).val == n
  isRoot _ := false
  inGroupByName _ _ := false
  inGroupByGid _ n := gid.val == n
  userEq := (· == ·)
  asGid _ := gid.val
  tryAsName _ := none
  globMatches := g
  hostMatches := (· == ·)

private theorem instOracle (g : String → String → Bool) :
    InstOracle userInst eqInst groupInst (oracle g) where
  has_name _ _ _ _ := rfl
  has_uid _ _ := by simp [userInst, oracle, UScalar.eq_equiv]
  is_root _ := rfl
  in_group_by_name _ _ := rfl
  in_group_by_gid _ _ := by simp [userInst, oracle, UScalar.eq_equiv]
  eq _ _ := rfl
  ne _ _ := rfl
  as_gid _ := by simp [groupInst, oracle]
  try_as_name _ := by
    simp [groupInst, oracle]
    rfl

private theorem fitsUsize {n : Nat} (h : n ≤ 4294967295) : n ≤ Usize.max :=
  h.trans Usize.cMax_bound_concrete.1

private def emptyTable (T : Type) : sudoers.VecOrd (RDef T) := ⟨.new _, .new _⟩

private def aliases : sudoers.AliasTable where
  user := ⟨.from [0#usize] (fitsUsize (by decide)), .from [⟨"MEMBERS", .from
    [.Allow .All, .Forbid (.Only (.User (.ID 2#u32)))] (fitsUsize (by decide))⟩]
      (fitsUsize (by decide))⟩
  host := emptyTable _
  cmnd := emptyTable _
  runas := emptyTable _

private def entry : REntry :=
  (some ⟨.from [.Allow .All] (fitsUsize (by decide)), .new _⟩,
   ⟨.from [.Passwd, .Nosetenv] (fitsUsize (by decide)), .Allow .All⟩)

private def rule : sudoers.ast.PermissionSpec where
  users := .from [.Allow (.Alias "MEMBERS")] (fitsUsize (by decide))
  permissions := .from [(.from [.Allow .All] (fitsUsize (by decide)),
    .from [entry] (fitsUsize (by decide)))] (fitsUsize (by decide))

private def rules : Slice sudoers.ast.PermissionSpec := .from [rule] (fitsUsize (by decide))
private def host : system.Hostname := ⟨"fixture"⟩
private def request (path : std.path.Path) : sudoers.Request Bool Unit Unit :=
  ⟨false, (), path, .from [] (by decide)⟩

private theorem hostFits : Fits host.inner := by
  change 7 ≤ Usize.max
  exact fitsUsize (by decide)

private theorem aliasFits : Fits "MEMBERS" := by
  change 7 ≤ Usize.max
  exact fitsUsize (by decide)

private theorem policyOK : PolicyOK rules aliases := by
  simp only [PolicyOK, AliasTableOK, TableWF, TableFits, TableGood, RuleOK, SegOK, LineOK,
    RunAsOK, CmdOK, ItemsFit, ItemsGood, aliases, emptyTable, rules, rule, entry,
    lineMods, csMods, csCmd, alloc.vec.Vec.from_val, Slice.from_val, List.forall_mem_cons]
  simp [aliasName, onlyItem, UserSpecFits, IdentFits, aliasFits,
    fitsUsize (n := 2) (by decide)]
  refine ⟨by decide, ?_, ?_⟩
  · intro d hd
    obtain rfl := List.eq_of_mem_singleton hd
    simp [aliasFits]
  · intro d hd
    obtain rfl := List.eq_of_mem_singleton hd
    simp

private def expectedTag : SudoersSpec.Tag := { authenticate := .passwd, env := .nosetenv }

private def specPolicy : SudoersSpec.Policy where
  rules := [⟨[.allow (.alias "MEMBERS")],
    [([.allow .all], [(some ⟨[.allow .all], []⟩, ⟨[.passwd, .nosetenv], .allow .all⟩)])]⟩]
  aliases := { user := [⟨"MEMBERS", [.allow .all, .forbid (.only (.user (.id 2)))]⟩] }

private def specRequest (invokingUser : Bool) (command : String) : SudoersSpec.Request Bool Unit :=
  ⟨invokingUser, host.inner, false, (), command, []⟩

private theorem spec_allows (g : String → String → Bool) (command : String) :
    SudoersSpec.authorize (oracle g) specPolicy (specRequest true command) = some expectedTag :=
  rfl

private theorem spec_denies (g : String → String → Bool) (command : String) :
    SudoersSpec.authorize (oracle g) specPolicy (specRequest false command) = none :=
  rfl

/-- The allow witness checks the returned authentication and environment tags as well as the grant. -/
theorem permits_member (g : String → String → Bool) (A : GlobAbs)
    (hG : GlobOracle A (oracle g)) (path : std.path.Path) :
    ∃ t, sudoers.permission_flags userInst eqInst groupInst rules aliases true host (request path) =
         ok (some t) ∧ absTag t = expectedTag := by
  obtain ⟨r, hr, habs⟩ := permission_flags_eq (instOracle g) hG (fun _ _ => rfl)
    rules aliases policyOK true host hostFits (request path)
  change r.map absTag = SudoersSpec.authorize (oracle g) specPolicy
    (specRequest true (A.path path)) at habs
  rw [spec_allows] at habs
  cases r <;> simp_all

/-- The other user is excluded by the negated member of the alias. -/
theorem denies_excluded_member (g : String → String → Bool) (A : GlobAbs)
    (hG : GlobOracle A (oracle g)) (path : std.path.Path) :
    sudoers.permission_flags userInst eqInst groupInst rules aliases false host (request path) =
      ok none := by
  obtain ⟨r, hr, habs⟩ := permission_flags_eq (instOracle g) hG (fun _ _ => rfl)
    rules aliases policyOK false host hostFits (request path)
  change r.map absTag = SudoersSpec.authorize (oracle g) specPolicy
    (specRequest false (A.path path)) at habs
  rw [spec_denies] at habs
  cases r <;> simp_all

/-- Fail-closed negative control: doing nothing but denying is not a refinement. -/
theorem deny_only_not_refinement (g : String → String → Bool) :
    ∃ (p : SudoersSpec.Policy) (r : SudoersSpec.Request Bool Unit),
      (none : Option SudoersSpec.Tag) ≠ SudoersSpec.authorize (oracle g) p r := by
  exact ⟨specPolicy, specRequest true "/fixture", by simp [spec_allows]⟩

/-! `sudo -v` and `sudo -l` (own entries) on the same fixture. Neither reaches the glob matcher,
`UnixUser::group` or `Path::new`, so these witnesses are unconditional. -/

/-- Command abstraction for the fixture: no command pattern of the fixture is read. -/
private def noGlob : GlobAbs := ⟨fun _ => "", fun _ => "", fun _ => ""⟩

private def listRequest (u : Bool) : sudoers.ListRequest Bool Unit Unit := ⟨u, true, ()⟩

/-- `sudo -v` by the member: granted with the line's tag, which needs a password. -/
theorem validate_member :
    ∃ t, sudoers.validate_flags userInst rules aliases true host = ok (some t) ∧
      absTag t = expectedTag := by
  obtain ⟨r, hr, habs⟩ := validate_flags_eq (A := noGlob) (instOracle fun _ _ => false)
    (fun _ _ => rfl) rules aliases policyOK true host hostFits
  change r.map absTag = SudoersSpec.validateFlags (oracle fun _ _ => false) specPolicy true
    host.inner at habs
  have : SudoersSpec.validateFlags (oracle fun _ _ => false) specPolicy true host.inner =
    some expectedTag := rfl
  rw [this] at habs
  cases r <;> simp_all

/-- `sudo -v` by the excluded user: refused. -/
theorem validate_excluded :
    sudoers.validate_flags userInst rules aliases false host = ok none := by
  obtain ⟨r, hr, habs⟩ := validate_flags_eq (A := noGlob) (instOracle fun _ _ => false)
    (fun _ _ => rfl) rules aliases policyOK false host hostFits
  change r.map absTag = SudoersSpec.validateFlags (oracle fun _ _ => false) specPolicy false
    host.inner at habs
  have : SudoersSpec.validateFlags (oracle fun _ _ => false) specPolicy false host.inner =
    none := rfl
  rw [this] at habs
  cases r <;> simp_all

/-- `sudo -l` by the member for its own entries (target: itself with its group): granted
without a password. -/
theorem list_self_member :
    ∃ t, sudoers.list_flags userInst eqInst userInst.UnixGroupInst rules aliases true host
      (listRequest true) =
      ok (some t) ∧ absTag t = { expectedTag with authenticate := .nopasswd } := by
  obtain ⟨r, hr, habs⟩ := exists_eq_ok_of_spec (list_flags_self_spec (A := noGlob)
    (instOracle fun _ _ => false) (fun _ _ => rfl) (fun _ => ()) rules aliases policyOK true host
    hostFits (listRequest true) rfl)
  change r.map absTag = SudoersSpec.listFlags (oracle fun _ _ => false) (fun _ => ()) specPolicy
    ⟨true, host.inner, true, true, ()⟩ at habs
  have : SudoersSpec.listFlags (oracle fun _ _ => false) (fun _ => ()) specPolicy
      ⟨true, host.inner, true, true, ()⟩ = some { expectedTag with authenticate := .nopasswd } :=
    rfl
  rw [this] at habs
  cases r <;> simp_all

end SudoRsProofs.NonVacuity
