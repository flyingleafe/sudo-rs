import SudoersSpec.Examples

/-!
# `sudo -v` and `sudo -l`: the flags of `validate_flags` and `list_flags`

`Sudoers::check_validate_permission` (`sudo -v`) and `Sudoers::check_list_permission`
(`sudo -l`, `sudo -l -U other`) apply `Defaults` (not modelled) and then turn the tag computed by
`mod.rs` `validate_flags` / `list_flags` into an `Authorization`. This file specifies those two
tag computations over the vocabulary of `Authorize.lean`:

* `validateFlags`: among the tags of all command entries of the lines that apply to the invoking
  user on this host (`entryTags`, i.e. `matching_user_specs` flattened), the last one that needs
  a password, else the last one (`Iterator::max_by_key(needs_passwd)`); root needs no password.
* `listFlags`, own entries: the same with the opposite preference
  (`max_by_key(!needs_passwd)`), and the password exception of `Sudoers::check`.
* `listFlags`, another user's entries: `authorize` on the request to run the pseudo-command
  `list` as that user with that user's primary group (`UnixUser::group`, a parameter `grp`
  here), and root may always.

Form (b) follows the Rust (`maxByKey` is the `fold` of `Iterator::max_by_key`); the theorems
state the declarative content (form (a)): `maxByKey_eq` (last maximal element),
`applicableEntries` (which entries count), and the password rules.
-/

namespace SudoersSpec

/-! ## `Iterator::max_by_key` with a `Bool` key -/

section MaxByKey

variable {α : Type}

/-- One step of `Iterator::max_by_key` (`false < true`): Rust folds with
`cmp::max_by(best, x, ..)`, which keeps `best` only if its key is strictly greater. -/
def maxByKeyStep (key : α → Bool) (best : Option α) (x : α) : Option α :=
  match best with
  | some b => if key b && !key x then some b else some x
  | none => some x

/-- `Iterator::max_by_key` with a `Bool` key. -/
def maxByKey (key : α → Bool) (l : List α) : Option α :=
  l.foldl (maxByKeyStep key) none

theorem maxByKey_append_singleton (key : α → Bool) (l : List α) (x : α) :
    maxByKey key (l ++ [x]) = maxByKeyStep key (maxByKey key l) x := by
  simp [maxByKey, List.foldl_append]

theorem getLast?_filter_of_any (key : α → Bool) (l : List α) (h : l.any key = true) :
    ∃ b, (l.filter key).getLast? = some b ∧ key b = true := by
  obtain ⟨y, hy, hky⟩ := List.any_eq_true.1 h
  have hne : l.filter key ≠ [] := List.ne_nil_of_mem (List.mem_filter.2 ⟨hy, hky⟩)
  obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 (List.getLast?_isSome.2 hne)
  exact ⟨b, hb, (List.mem_filter.1 (List.mem_of_getLast? hb)).2⟩

/-- **`max_by_key` returns the last maximal element**: the last element whose key is `true`
if there is one, otherwise the last element. -/
theorem maxByKey_eq (key : α → Bool) (l : List α) :
    maxByKey key l = if l.any key then (l.filter key).getLast? else l.getLast? := by
  suffices H : ∀ l' : List α, maxByKey key l'.reverse =
      if l'.reverse.any key then (l'.reverse.filter key).getLast? else l'.reverse.getLast? by
    simpa using H l.reverse
  intro l'
  induction l' with
  | nil => rfl
  | cons x l ih =>
    rw [List.reverse_cons]
    generalize l.reverse = l at ih ⊢
    rw [maxByKey_append_singleton, ih]
    cases hx : key x
    · cases ha : l.any key
      · have hl : ∀ b, l.getLast? = some b → key b = false := by
          intro b hb
          have := List.any_eq_false.1 ha b (List.mem_of_getLast? hb)
          simpa using this
        cases hlast : l.getLast? with
        | none => simp [maxByKeyStep, hx, ha]
        | some b => simp [maxByKeyStep, hx, ha, hl b hlast]
      · obtain ⟨b, hb, hkb⟩ := getLast?_filter_of_any key l ha
        simp [maxByKeyStep, hx, ha, hb, hkb, List.filter_append]
    · have hstep : ∀ o, maxByKeyStep key o x = some x := by
        intro o; cases o <;> simp [maxByKeyStep, hx]
      rw [hstep]
      simp [hx, List.filter_append]

theorem maxByKey_eq_none_iff (key : α → Bool) (l : List α) : maxByKey key l = none ↔ l = [] := by
  rw [maxByKey_eq]
  constructor
  · intro h
    split at h
    · rename_i ha
      obtain ⟨b, hb, -⟩ := getLast?_filter_of_any key l ha
      simp [hb] at h
    · exact List.getLast?_eq_none_iff.1 h
  · rintro rfl; rfl

theorem maxByKey_mem (key : α → Bool) (l : List α) (x : α) (h : maxByKey key l = some x) :
    x ∈ l := by
  rw [maxByKey_eq] at h
  split at h
  · exact (List.mem_filter.1 (List.mem_of_getLast? h)).1
  · exact List.mem_of_getLast? h

/-- The key of the result is `true` iff some element has key `true`. -/
theorem maxByKey_key (key : α → Bool) (l : List α) (x : α) (h : maxByKey key l = some x) :
    key x = l.any key := by
  rw [maxByKey_eq] at h
  split at h
  · rename_i ha
    rw [ha]
    exact (List.mem_filter.1 (List.mem_of_getLast? h)).2
  · rename_i ha
    have ha : l.any key = false := by simpa using ha
    rw [ha]
    simpa using List.any_eq_false.1 ha x (List.mem_of_getLast? h)

end MaxByKey

variable {User Group : Type} (O : Oracle User Group)

/-! ## The applicable command entries -/

/-- The tags of the command entries of the lines that apply to `u` on `host`, in the order of
`Sudoers::matching_user_specs` (`matching_user_specs(..).flatten().map(|(_, (tag, _))| tag)`). -/
def entryTags (p : Policy) (u : User) (host : Hostname) : List Tag :=
  (matchingUserSpecs O p u host).flatten.map (·.2.1)

/-- The user list of a line accepts `u` (as `userListMatches`, without a request). -/
def userApplies (p : Policy) (u : User) (users : SpecList UserSpecifier) : Bool :=
  (findItemSpec (matchUser O u) (getAliases p.aliases.user (matchUser O u)) (withUnit users)).isSome

/-- A host list accepts `host` (as `hostListMatches`, without a request). -/
def hostApplies (p : Policy) (host : Hostname) (hosts : SpecList Hostname) : Bool :=
  (findItemSpec (matchHost O host) (getAliases p.aliases.host (matchHost O host))
    (withUnit hosts)).isSome

/-- Declaratively: every command entry, in file order, of every `Host_List = Cmnd_Spec_List`
group whose line applies to `u` and whose host list applies to `host`, with runas and tags
distributed along the group. Neither the runas spec nor the command (nor its negation) is
consulted. -/
def applicableEntries (p : Policy) (u : User) (host : Hostname) : List MatchedCommand :=
  p.rules.flatMap fun rule =>
    if userApplies O p u rule.users then
      rule.permissions.flatMap fun seg =>
        if hostApplies O p host seg.1 then distributeTagsSpec seg.2 else []
    else []

/-- The candidates of a request are the applicable entries of its invoking user and host. -/
theorem candidatesSpec_eq_applicableEntries (p : Policy) (r : Request User Group) :
    candidatesSpec O p r = applicableEntries O p r.invokingUser r.host := rfl

theorem entryTags_eq (p : Policy) (u : User) (host : Hostname) :
    entryTags O p u host = (applicableEntries O p u host).map (·.2.1) := by
  simp only [entryTags, matchingUserSpecs, applicableEntries, userApplies, hostApplies,
    flatten_filterMap_map, ← findItem_eq_spec, ← distributeTags_eq_spec]
  congr 1
  induction p.rules with
  | nil => rfl
  | cons rule rules ih =>
    simp only [List.flatMap_cons, List.flatMap_append, ih]
    split <;> simp

theorem distributeTagsSpec_eq_nil_iff (l : List (Option RunAs × CommandSpec)) :
    distributeTagsSpec l = [] ↔ l = [] := by
  simp [distributeTagsSpec]

/-- No applicable entry: every applicable host group of every applicable line is empty. -/
theorem applicableEntries_eq_nil_iff (p : Policy) (u : User) (host : Hostname) :
    applicableEntries O p u host = [] ↔
      ∀ rule ∈ p.rules, userApplies O p u rule.users = true →
        ∀ seg ∈ rule.permissions, hostApplies O p host seg.1 = true → seg.2 = [] := by
  simp only [applicableEntries, List.flatMap_eq_nil_iff]
  constructor
  · intro h rule hr hu seg hs hh
    have := h rule hr
    simp only [hu, ite_true, List.flatMap_eq_nil_iff] at this
    have := this seg hs
    simpa [hh, distributeTagsSpec_eq_nil_iff] using this
  · intro h rule hr
    split
    · rename_i hu
      simp only [List.flatMap_eq_nil_iff]
      intro seg hs
      split
      · rename_i hh
        exact (distributeTagsSpec_eq_nil_iff _).2 (h rule hr hu seg hs hh)
      · rfl
    · rfl

/-! ## The NOPASSWD exception -/

/-- Set `authenticate := NOPASSWD` if `skip` (the `if let Some(..) = &mut flags` blocks). -/
def withNopasswd (skip : Bool) (t : Tag) : Tag :=
  if skip then { t with authenticate := .nopasswd } else t

@[simp] theorem withNopasswd_needsPasswd (skip : Bool) (t : Tag) :
    (withNopasswd skip t).needsPasswd = (!skip && t.needsPasswd) := by
  cases skip <;> rfl

/-! ## `sudo -v` -/

/-- `mod.rs` `validate_flags`. -/
def validateFlags (p : Policy) (u : User) (host : Hostname) : Option Tag :=
  (maxByKey Tag.needsPasswd (entryTags O p u host)).map (withNopasswd (O.isRoot u))

/-- **`sudo -v`, declaratively**: the last applicable entry that needs a password, or else the
last applicable entry; for root with NOPASSWD. -/
theorem validateFlags_eq (p : Policy) (u : User) (host : Hostname) :
    validateFlags O p u host =
      (let ts := (applicableEntries O p u host).map (·.2.1)
       if ts.any Tag.needsPasswd then (ts.filter Tag.needsPasswd).getLast? else ts.getLast?).map
        (withNopasswd (O.isRoot u)) := by
  rw [validateFlags, maxByKey_eq, entryTags_eq]

/-- **`sudo -v` is refused iff no command entry applies**: no applicable host group of an
applicable line has an entry. Runas specs, commands and negation play no role. -/
theorem validateFlags_eq_none_iff (p : Policy) (u : User) (host : Hostname) :
    validateFlags O p u host = none ↔
      ∀ rule ∈ p.rules, userApplies O p u rule.users = true →
        ∀ seg ∈ rule.permissions, hostApplies O p host seg.1 = true → seg.2 = [] := by
  rw [validateFlags, Option.map_eq_none_iff, maxByKey_eq_none_iff, entryTags_eq,
    List.map_eq_nil_iff, applicableEntries_eq_nil_iff]

/-- **Password rule of `sudo -v`**: a password is needed iff the invoking user is not root and
some applicable entry needs one (i.e. without a password only if all entries are NOPASSWD). -/
theorem validateFlags_needsPasswd (p : Policy) (u : User) (host : Hostname) (t : Tag)
    (ht : validateFlags O p u host = some t) :
    t.needsPasswd = true ↔
      O.isRoot u = false ∧ ∃ e ∈ applicableEntries O p u host, e.2.1.needsPasswd = true := by
  obtain ⟨t', ht', rfl⟩ := Option.map_eq_some_iff.1 ht
  have hk := maxByKey_key _ _ _ ht'
  rw [withNopasswd_needsPasswd, hk, entryTags_eq]
  cases O.isRoot u <;> simp [List.any_map]

/-- The granted tag is that of an applicable entry (up to the root exception). -/
theorem validateFlags_of_entry (p : Policy) (u : User) (host : Hostname) (t : Tag)
    (ht : validateFlags O p u host = some t) :
    ∃ e ∈ applicableEntries O p u host, t = withNopasswd (O.isRoot u) e.2.1 := by
  obtain ⟨t', ht', rfl⟩ := Option.map_eq_some_iff.1 ht
  have hm := maxByKey_mem _ _ _ ht'
  rw [entryTags_eq, List.mem_map] at hm
  obtain ⟨e, he, rfl⟩ := hm
  exact ⟨e, he, rfl⟩

/-! ## `sudo -l` -/

/-- `mod.rs` `ListRequest`, with the invoking user and the host folded in. -/
structure ListRequest (User Group : Type) where
  /-- `invoking_user`. -/
  invokingUser : User
  /-- `hostname`. -/
  host : Hostname
  /-- `request.inspected_user`: the user whose entries are listed (`-U`, else the invoker). -/
  inspectedUser : User
  /-- `request.target_user` (`-u`). -/
  targetUser : User
  /-- `request.target_group` (`-g`). -/
  targetGroup : Group

/-- The request `list_flags` decides for another user's entries: run the pseudo-command `list`
without arguments as the inspected user with their primary group `grp inspectedUser`
(`UnixUser::group`). -/
def listCommandRequest (grp : User → Group) (lr : ListRequest User Group) : Request User Group where
  invokingUser := lr.invokingUser
  host := lr.host
  targetUser := lr.inspectedUser
  targetGroup := grp lr.inspectedUser
  command := "list"
  arguments := []

/-- `skip_passwd` for listing one's own entries: as in `Sudoers::check`, root, or the target is
the invoking user with one of their groups. -/
def listSkipPasswd (lr : ListRequest User Group) : Bool :=
  O.isRoot lr.invokingUser ||
    (O.userEq lr.targetUser lr.invokingUser && inGroup O lr.invokingUser lr.targetGroup)

/-- `mod.rs` `list_flags`; `grp` is `UnixUser::group`. -/
def listFlags (grp : User → Group) (p : Policy) (lr : ListRequest User Group) : Option Tag :=
  if !O.userEq lr.inspectedUser lr.invokingUser then
    ((authorize O p (listCommandRequest grp lr)).or
        (if O.isRoot lr.invokingUser then some {} else none)).map
      (withNopasswd (O.isRoot lr.invokingUser))
  else
    (maxByKey (fun t => !t.needsPasswd) (entryTags O p lr.invokingUser lr.host)).map
      (withNopasswd (listSkipPasswd O lr))

/-- **Listing another user's entries is the decision for the pseudo-command `list`** run as
that user with their primary group; if that is denied, root may still, with the default tag
and NOPASSWD. -/
theorem listFlags_other (grp : User → Group) (p : Policy) (lr : ListRequest User Group)
    (h : O.userEq lr.inspectedUser lr.invokingUser = false) :
    listFlags O grp p lr =
      match authorize O p (listCommandRequest grp lr) with
      | some t => some t
      | none => if O.isRoot lr.invokingUser then some { authenticate := .nopasswd } else none := by
  have hs : skipPasswd O (listCommandRequest grp lr) = O.isRoot lr.invokingUser := by
    simp [skipPasswd, listCommandRequest, h]
  simp only [listFlags, h, Bool.not_false, ite_true, authorize, hs]
  cases checkPermission O p (listCommandRequest grp lr) with
  | none => cases O.isRoot lr.invokingUser <;> rfl
  | some t => cases O.isRoot lr.invokingUser <;> rfl

/-- Not root: exactly `authorize` on the `list` request. -/
theorem listFlags_other_of_not_root (grp : User → Group) (p : Policy)
    (lr : ListRequest User Group) (h : O.userEq lr.inspectedUser lr.invokingUser = false)
    (hr : O.isRoot lr.invokingUser = false) :
    listFlags O grp p lr = authorize O p (listCommandRequest grp lr) := by
  rw [listFlags_other O grp p lr h, hr]
  cases authorize O p (listCommandRequest grp lr) <;> rfl

/-- Root may always list another user's entries, without a password, even where `list` is
explicitly forbidden. -/
theorem listFlags_other_root (grp : User → Group) (p : Policy) (lr : ListRequest User Group)
    (h : O.userEq lr.inspectedUser lr.invokingUser = false)
    (hr : O.isRoot lr.invokingUser = true) :
    ∃ t, listFlags O grp p lr = some t ∧ t.authenticate = .nopasswd := by
  rw [listFlags_other O grp p lr h, hr]
  cases ha : authorize O p (listCommandRequest grp lr) with
  | none => exact ⟨_, rfl, rfl⟩
  | some t =>
    refine ⟨t, rfl, authorize_nopasswd O p _ t (Or.inl ?_) ha⟩
    exact hr

/-- **Listing one's own entries is refused iff no command entry applies** (as for `sudo -v`):
neither the runas spec, nor the command, nor `-u`/`-g` matter. -/
theorem listFlags_self_eq_none_iff (grp : User → Group) (p : Policy)
    (lr : ListRequest User Group) (h : O.userEq lr.inspectedUser lr.invokingUser = true) :
    listFlags O grp p lr = none ↔
      ∀ rule ∈ p.rules, userApplies O p lr.invokingUser rule.users = true →
        ∀ seg ∈ rule.permissions, hostApplies O p lr.host seg.1 = true → seg.2 = [] := by
  simp only [listFlags, h, Bool.not_true, Bool.false_eq_true, ite_false]
  rw [Option.map_eq_none_iff, maxByKey_eq_none_iff, entryTags_eq, List.map_eq_nil_iff,
    applicableEntries_eq_nil_iff]

/-- **Password rule of `sudo -l` for one's own entries**: a password is needed iff `skip_passwd`
does not hold and every applicable entry needs one (i.e. one NOPASSWD entry suffices). -/
theorem listFlags_self_needsPasswd (grp : User → Group) (p : Policy)
    (lr : ListRequest User Group) (h : O.userEq lr.inspectedUser lr.invokingUser = true) (t : Tag)
    (ht : listFlags O grp p lr = some t) :
    t.needsPasswd = true ↔
      listSkipPasswd O lr = false ∧
        ∀ e ∈ applicableEntries O p lr.invokingUser lr.host, e.2.1.needsPasswd = true := by
  simp only [listFlags, h, Bool.not_true, Bool.false_eq_true, ite_false] at ht
  obtain ⟨t', ht', rfl⟩ := Option.map_eq_some_iff.1 ht
  have hk := maxByKey_key _ _ _ ht'
  rw [withNopasswd_needsPasswd]
  have hk' : t'.needsPasswd = !(entryTags O p lr.invokingUser lr.host).any (fun t => !t.needsPasswd) := by
    rw [← hk]; simp
  rw [hk', entryTags_eq]
  cases listSkipPasswd O lr <;> simp [List.any_map]

/-- The granted tag of one's own listing is that of an applicable entry (up to the exception). -/
theorem listFlags_self_of_entry (grp : User → Group) (p : Policy)
    (lr : ListRequest User Group) (h : O.userEq lr.inspectedUser lr.invokingUser = true) (t : Tag)
    (ht : listFlags O grp p lr = some t) :
    ∃ e ∈ applicableEntries O p lr.invokingUser lr.host, t = withNopasswd (listSkipPasswd O lr) e.2.1 := by
  simp only [listFlags, h, Bool.not_true, Bool.false_eq_true, ite_false] at ht
  obtain ⟨t', ht', rfl⟩ := Option.map_eq_some_iff.1 ht
  have hm := maxByKey_mem _ _ _ ht'
  rw [entryTags_eq, List.mem_map] at hm
  obtain ⟨e, he, rfl⟩ := hm
  exact ⟨e, he, rfl⟩

/-! ## Examples (oracle of the Rust unit tests, `UnixUser::group` of `Named` is the identity) -/

namespace Examples

/-- `list_flags` for `invoking` listing `inspected`'s entries with target `target:group`. -/
def list (p : Policy) (invoking inspected target group host : String) : Option Tag :=
  listFlags named id p ⟨invoking, host, inspected, target, group⟩

def validate (p : Policy) (invoking host : String) : Option Tag :=
  validateFlags named p invoking host

-- `alice ALL = list`: without a Runas_Spec the `list` privilege only covers root's entries
#guard !allows (list (pol [line [u "alice"] [ent none [] (c "list")]]) "alice" "bob" "root" "root" "server")
#guard allows (list (pol [line [u "alice"] [ent none [] (c "list")]]) "alice" "root" "root" "root" "server")
-- `alice ALL = (bob) list` / `(ALL) ALL`
#guard auth (list (pol [line [u "alice"] [ent (some ⟨[u "bob"], []⟩) [] (c "list")]]) "alice" "bob" "root" "root" "server") = some .none
#guard allows (list (pol [line [u "alice"] [ent (some ⟨[all], []⟩) [] all]]) "alice" "bob" "root" "root" "server")
-- `alice ALL = (root) ALL`: running anything as root does not allow `-U bob`
#guard !allows (list (pol [line [u "alice"] [ent (some ⟨[u "root"], []⟩) [] all]]) "alice" "bob" "root" "root" "server")
-- root may list anyone, even with `root ALL = (bob) !list`
#guard list (pol [line [u "root"] [ent (some ⟨[u "bob"], []⟩) [] (.forbid (.only ⟨"list", .prefix []⟩))]]) "root" "bob" "root" "root" "server" = some { authenticate := .nopasswd }
-- root without entries of its own may not list them
#guard !allows (list (pol []) "root" "root" "root" "root" "server")
-- own entries: one NOPASSWD entry suffices for `sudo -l`, one PASSWD entry forces it for `sudo -v`
#guard auth (list (pol [line [u "alice"] [ent none [] (c "/bin/a"), ent none [.nopasswd] (c "/bin/b")]]) "alice" "alice" "root" "root" "server") = some .nopasswd
#guard auth (validate (pol [line [u "alice"] [ent none [.nopasswd] (c "/bin/a"), ent none [.passwd] (c "/bin/b")]]) "alice" "server") = some .passwd
-- `alice ALL = !ALL` still lets alice run `sudo -v` and `sudo -l` (with a password)
#guard auth (validate (pol [line [u "alice"] [ent none [] notAll]]) "alice" "server") = some .none
#guard auth (list (pol [line [u "alice"] [ent none [] notAll]]) "alice" "alice" "root" "root" "server") = some .none

end Examples

end SudoersSpec
