import SudoersSpec.ListValidate
import SudoersSpec.Analysis.Collect

/-!
# The Defaults of `sudo -v` and `sudo -l`

`Sudoers::check_validate_permission` and `Sudoers::check_list_permission`
(`src/sudoers/mod.rs`) apply Defaults to the settings the policy object holds and then turn the
tag of `validate_flags` / `list_flags` (`SudoersSpec.validateFlags` / `SudoersSpec.listFlags`,
including the NOPASSWD exceptions) into `Authorization<()>` with `Settings::to_auth`; there are
no `Restrictions`. Here `Authorization<()>` is `Option Authentication`: `none` is `Forbidden`,
`some a` is `Allowed(a, ())`.

Which Defaults apply, transcribed from the code:

* `sudo -v` (`validateSettings`): the first (non-command) pass only, with the **invoking** user
  and **no** target user (`specify_host_user_runas(hostname, invoking_user, None)`): generic,
  host and user scopes in file order. A `Defaults>…` line never applies
  (`nonCommandModifiers_none_runAs`); `Defaults!…` lines are not consulted
  (`validateSettings_command`).
* `sudo -l -U other`, inspected user ≠ invoking user (`listSettings_other`): both passes, as
  `Sudoers::check` for the pseudo-command `list` without arguments run as the **inspected** user
  (`settingsInForce` on `listCommandRequest`): first pass with the invoking user and the inspected
  user as runas target, then the command pass for `list`.
* `sudo -l` for one's own entries (`listSettings_self`): no pass at all; the settings in force
  are those the policy object holds (`initial`).

Both passes consume their customiser vectors (`Collected.nonCommand` / `.command` stand for what
is left in them). In `run_list` (`src/sudo/pipeline/list.rs`), `Context::from_list_opts` calls
`Sudoers::search_path` (`src/sudoers/policy.rs`) before `check_list_permission`; its first
statement is the first pass with the invoking user and the target user of `-u`.
`listPipelineSettings` composes the two (the order of calls is code reading; `search_path` and
the pipeline are not extracted): the first pass of `check_list_permission` then finds nothing.
-/

namespace SudoersSpec.Analysis

variable {User Group : Type} (O : Oracle User Group)

/-! ## The settings in force -/

/-- **The Defaults in force for `sudo -v`**: the first pass with the invoking user `u` and no
target user. -/
def validateSettings (aliases : AliasTable) (c : Collected) (u : User) (host : Hostname)
    (initial : Settings.Settings) : Settings.Settings :=
  applyModifiers (nonCommandModifiers O aliases host u none c.nonCommand) initial

/-- **The Defaults in force for `sudo -l`**: for another user's entries those of `check` on the
request to run `list` as that user; for one's own entries none are applied. -/
def listSettings (aliases : AliasTable) (c : Collected) (grp : User → Group)
    (lr : ListRequest User Group) (initial : Settings.Settings) : Settings.Settings :=
  if !O.userEq lr.inspectedUser lr.invokingUser then
    settingsInForce O aliases c (listCommandRequest grp lr) initial
  else initial

/-- `run_list`: `search_path` runs the first pass with the target user of `-u`, then
`check_list_permission` runs on the policy whose first-pass customisers are consumed. -/
def listPipelineSettings (aliases : AliasTable) (c : Collected) (grp : User → Group)
    (lr : ListRequest User Group) (initial : Settings.Settings) : Settings.Settings :=
  listSettings O aliases { c with nonCommand := [] } grp lr
    (applyModifiers
      (nonCommandModifiers O aliases lr.host lr.invokingUser (some lr.targetUser) c.nonCommand)
      initial)

/-! ## The results (`Authorization<()>`) -/

/-- `check_validate_permission`: `to_auth` of the settings in force and the `validate_flags` tag. -/
def validateAuthorization (p : Policy) (c : Collected) (u : User) (host : Hostname)
    (initial : Settings.Settings) : Option Authentication :=
  (validateFlags O p u host).map (toAuth (validateSettings O p.aliases c u host initial).toDefaults)

/-- `check_list_permission`: `to_auth` of the settings in force and the `list_flags` tag. -/
def listAuthorization (grp : User → Group) (p : Policy) (c : Collected)
    (lr : ListRequest User Group) (initial : Settings.Settings) : Option Authentication :=
  (listFlags O grp p lr).map (toAuth (listSettings O p.aliases c grp lr initial).toDefaults)

/-- `run_list` up to authentication: `search_path`, then `check_list_permission`. -/
def listPipelineAuthorization (grp : User → Group) (p : Policy) (c : Collected)
    (lr : ListRequest User Group) (initial : Settings.Settings) : Option Authentication :=
  (listFlags O grp p lr).map (toAuth (listPipelineSettings O p.aliases c grp lr initial).toDefaults)

/-! ## Which scopes apply -/

/-- **`sudo -v`: a `Defaults>…` line never applies**, whatever its user list. -/
theorem nonCommandModifiers_none_runAs (aliases : AliasTable) (host : Hostname) (u : User)
    (xs : SpecList UserSpecifier) (mods : List Settings.SettingsModifier)
    (rest : List (NonCommandScope × List Settings.SettingsModifier)) :
    nonCommandModifiers O aliases host u none ((.runAs xs, mods) :: rest) =
      nonCommandModifiers O aliases host u none rest := by
  first
    | rfl
    | simp [nonCommandModifiers]

/-- **`sudo -v` does not consult command-scoped Defaults.** -/
theorem validateSettings_command (aliases : AliasTable) (c : Collected) (u : User)
    (host : Hostname) (initial : Settings.Settings)
    (cmds : List (SpecList Command × List Settings.SettingsModifier)) :
    validateSettings O aliases { c with command := cmds } u host initial =
      validateSettings O aliases c u host initial := rfl

/-- **`sudo -l` for one's own entries applies no Defaults.** -/
theorem listSettings_self (aliases : AliasTable) (c : Collected) (grp : User → Group)
    (lr : ListRequest User Group) (initial : Settings.Settings)
    (h : O.userEq lr.inspectedUser lr.invokingUser = true) :
    listSettings O aliases c grp lr initial = initial := by
  first
    | (unfold listSettings; rw [h]; all_goals rfl)
    | simp [listSettings, h]

/-- **`sudo -l -U other` applies the Defaults of `check` for `list` run as the inspected user**:
the first pass with the invoking user and the inspected user as runas target, then the command
pass for `list` without arguments. -/
theorem listSettings_other (aliases : AliasTable) (c : Collected) (grp : User → Group)
    (lr : ListRequest User Group) (initial : Settings.Settings)
    (h : O.userEq lr.inspectedUser lr.invokingUser = false) :
    listSettings O aliases c grp lr initial =
      applyModifiers (commandModifiers O aliases "list" [] c.command)
        (applyModifiers
          (nonCommandModifiers O aliases lr.host lr.invokingUser (some lr.inspectedUser)
            c.nonCommand)
          initial) := by
  first
    | (unfold listSettings; rw [h]; all_goals rfl)
    | simp [listSettings, h, settingsInForce, listCommandRequest]

/-- **`run_list`, own entries**: the first pass of `search_path`, with the target user of `-u`
as runas target. -/
theorem listPipelineSettings_self (aliases : AliasTable) (c : Collected) (grp : User → Group)
    (lr : ListRequest User Group) (initial : Settings.Settings)
    (h : O.userEq lr.inspectedUser lr.invokingUser = true) :
    listPipelineSettings O aliases c grp lr initial =
      applyModifiers
        (nonCommandModifiers O aliases lr.host lr.invokingUser (some lr.targetUser) c.nonCommand)
        initial := by
  unfold listPipelineSettings
  exact listSettings_self O aliases _ grp lr _ h

/-- **`run_list`, another user's entries**: the first pass of `search_path` (runas target: the
user of `-u`, not the inspected user), then the command pass for `list`; the first pass of
`check_list_permission` finds no customiser left. -/
theorem listPipelineSettings_other (aliases : AliasTable) (c : Collected) (grp : User → Group)
    (lr : ListRequest User Group) (initial : Settings.Settings)
    (h : O.userEq lr.inspectedUser lr.invokingUser = false) :
    listPipelineSettings O aliases c grp lr initial =
      applyModifiers (commandModifiers O aliases "list" [] c.command)
        (applyModifiers
          (nonCommandModifiers O aliases lr.host lr.invokingUser (some lr.targetUser)
            c.nonCommand)
          initial) := by
  unfold listPipelineSettings
  rw [listSettings_other O aliases _ grp lr _ h]
  all_goals rfl

/-! ## Decision and authentication -/

/-- **No Defaults value turns a `sudo -v` denial into a permission or back.** -/
theorem validateAuthorization_eq_none_iff (p : Policy) (c : Collected) (u : User)
    (host : Hostname) (initial : Settings.Settings) :
    validateAuthorization O p c u host initial = none ↔ validateFlags O p u host = none := by
  simp [validateAuthorization]

/-- **`sudo -v` authenticates iff the effective tag (`validate_flags`) needs a password**, and
the other fields are `toAuth` of the settings in force. -/
theorem validateAuthorization_eq_some (p : Policy) (c : Collected) (u : User) (host : Hostname)
    (initial : Settings.Settings) (a : Authentication)
    (h : validateAuthorization O p c u host initial = some a) :
    ∃ t, validateFlags O p u host = some t ∧
      a = toAuth (validateSettings O p.aliases c u host initial).toDefaults t ∧
      a.mustAuthenticate = t.needsPasswd := by
  unfold validateAuthorization at h
  obtain ⟨t, ht, rfl⟩ := Option.map_eq_some_iff.1 h
  exact ⟨t, ht, rfl, rfl⟩

/-- **No Defaults value turns a `sudo -l` denial into a permission or back.** -/
theorem listAuthorization_eq_none_iff (grp : User → Group) (p : Policy) (c : Collected)
    (lr : ListRequest User Group) (initial : Settings.Settings) :
    listAuthorization O grp p c lr initial = none ↔ listFlags O grp p lr = none := by
  simp [listAuthorization]

/-- **`sudo -l` authenticates iff the effective tag (`list_flags`, after the NOPASSWD
exceptions) needs a password**, and the other fields are `toAuth` of the settings in force. -/
theorem listAuthorization_eq_some (grp : User → Group) (p : Policy) (c : Collected)
    (lr : ListRequest User Group) (initial : Settings.Settings) (a : Authentication)
    (h : listAuthorization O grp p c lr initial = some a) :
    ∃ t, listFlags O grp p lr = some t ∧
      a = toAuth (listSettings O p.aliases c grp lr initial).toDefaults t ∧
      a.mustAuthenticate = t.needsPasswd := by
  unfold listAuthorization at h
  obtain ⟨t, ht, rfl⟩ := Option.map_eq_some_iff.1 h
  exact ⟨t, ht, rfl, rfl⟩

/-! ## Examples (oracle of the Rust unit tests; `UnixUser::group` of `Named` is the identity)

Executable tests (`#guard`), not kernel proofs. Synthetic names, no system lookups. Policy:
`alice ALL = (bob) list, NOPASSWD: /bin/b`. Defaults: `Defaults:alice passwd_tries=7`,
`Defaults>bob rootpw`, and for the command `list` the modifier `timestamp_timeout 60`. -/

namespace Examples

open SudoersSpec.Examples (named pol line ent u c)

private def p : Policy :=
  pol [line [u "alice"] [ent (some ⟨[u "bob"], []⟩) [] (c "list"), ent none [.nopasswd] (c "/bin/b")]]

private def defs : Collected :=
  { nonCommand := [(.user [u "alice"], [.passwd_tries 7]), (.runAs [u "bob"], [.rootpw true])]
    command := [([c "list"], [.timestamp_timeout 60])] }

private def validate : Option Authentication :=
  validateAuthorization named p defs "alice" "server" Settings.Settings.default

/-- `sudo -l` (inspected `alice`) or `sudo -l -U bob`, both with `-u root -g root`. -/
private def list (inspected : String) : Option Authentication :=
  listAuthorization named id p defs ⟨"alice", "server", inspected, "root", "root"⟩
    Settings.Settings.default

/-- The same through `run_list`, with the `-u`/`-g` target given. -/
private def pipeline (inspected target : String) : Option Authentication :=
  listPipelineAuthorization named id p defs ⟨"alice", "server", inspected, target, target⟩
    Settings.Settings.default

-- `sudo -v`: the user scope applies, the runas and the command scope do not
#guard validate.map (·.allowedAttempts) = some 7
#guard validate.map (·.credential) = some .invokingUser
#guard validate.map (·.priorValidity) = some (.ofSecs (15 * 60))
-- `sudo -v`: one PASSWD entry forces a password
#guard validate.map (·.mustAuthenticate) = some true

-- `sudo -l -U bob`: user scope, runas scope for the inspected user, command scope for `list`
#guard (list "bob").map (·.allowedAttempts) = some 7
#guard (list "bob").map (·.credential) = some .root
#guard (list "bob").map (·.priorValidity) = some (.ofSecs 60)
#guard (list "bob").map (·.mustAuthenticate) = some true

-- `sudo -l` (own entries): no scope applies, not even the user scope; one NOPASSWD entry suffices
#guard (list "alice").map (·.allowedAttempts) = some 3
#guard (list "alice").map (·.credential) = some .invokingUser
#guard (list "alice").map (·.priorValidity) = some (.ofSecs (15 * 60))
#guard (list "alice").map (·.mustAuthenticate) = some false

-- `run_list`, own entries with `-u bob`: `search_path` applies the runas scope of the `-u` target
#guard (pipeline "alice" "bob").map (·.credential) = some .root
#guard (pipeline "alice" "bob").map (·.allowedAttempts) = some 7
#guard (pipeline "alice" "root").map (·.credential) = some .invokingUser

-- `run_list`, `-U bob` with `-u root`: the runas scope of the inspected user is not applied
-- (the first pass already ran for `root`); the command scope for `list` is
#guard (pipeline "bob" "root").map (·.credential) = some .invokingUser
#guard (pipeline "bob" "root").map (·.priorValidity) = some (.ofSecs 60)
#guard (pipeline "bob" "bob").map (·.credential) = some .root

end Examples

end SudoersSpec.Analysis
