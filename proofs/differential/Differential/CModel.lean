import Differential.Case

/-!
# Explaining C sudo disagreements: the spec with C sudo's rules switched in

To attribute every spec-vs-C disagreement to a cause, `decide` is the spec decision
(`SudoersSpec.authorize`, built from the same spec functions) in which two components can
be replaced by transcriptions of the C sudo 1.9.18 code:

* `cRunas`: whether a command entry's runas spec permits the request, as C's
  `runaslist_matches` (`plugins/sudoers/match.c` 294-331) with `runas_userlist_matches`
  (151-214) and `runas_grouplist_matches` (222-284) decides it, instead of sudo-rs's
  `runas_allowed` (`check_permission`, `src/sudoers/mod.rs`);
* `cArgs`: argument matching as C's `command_args_match` (`match_command.c` 80-112) does it
  with `fnmatch(3)`, instead of `Args::Prefix` / `Args::Exact`.

Everything else (user and host lists, aliases, command paths, last match wins, tag
accumulation and the implicit SETENV of `ALL`) is the spec's: on this fragment the C code
computes the same (`userlist_matches`, `hostlist_matches`, `cmndlist_matches` are "last
specified member wins" with recursive alias evaluation; `propagate_cmndspec` in `gram.y`
accumulates tags like `distribute_tags`). That claim is checked, not assumed: `run.sh`
reports how often `decide {cRunas, cArgs}` agrees with `testsudoers`.

With both switches off, `decide` is the spec decision (`decide_off`).
-/

namespace Differential.CModel

open SudoersSpec

structure Toggles where
  cRunas : Bool := false
  cArgs : Bool := false
  deriving DecidableEq, Repr

/-- C's `ALLOW` / `DENY` / `UNSPEC` as `some true` / `some false` / `none`. -/
abbrev Tri := Option Bool

/-- The member evaluated last in a reversed scan that stops at the first specified result:
the last specified member in file order. -/
def lastSpecified (l : List α) (f : α → Tri) : Tri :=
  l.foldl (fun acc x => (f x).or acc) none

/-- The result of a member that matched, honouring its `!`. -/
def hit (s : Qualified α) : Tri := some (match s with | .allow _ => true | .forbid _ => false)

/-- `rc` of an alias reference, flipped by its `!` (`match.c` 181-189, 240-248). -/
def viaAlias (s : Qualified α) (rc : Tri) : Tri :=
  match s with | .allow _ => rc | .forbid _ => rc.map (!·)

/-- The runas part of the request as C sudo sees it (`testsudoers.c` 331-342). -/
structure Ctx where
  db : Db
  invoker : UserEnt
  /-- `ctx->runas.pw`: `-u`, else the invoking user if `-g` was given, else `root`. -/
  runasPw : UserEnt
  /-- `ctx->runas.gr`: only with `-g`. -/
  runasGr : Option GroupEnt
  userSpecified : Bool
  groupSpecified : Bool

/-- `userpw_matches` (`match.c` 554-580) for `name` and `#uid`, `usergr_matches` (620-670)
via `user_in_group` (`pwutil.c` 1114-) for `%group` and `%#gid`. -/
def userMember (ctx : Ctx) (pw : UserEnt) : UserSpecifier → Bool
  | .user (.name n) => pw.name == n
  | .user (.id n) => pw.uid == n
  | .group (.name g) => match ctx.db.groupNamed g with
    | some gr => (ctx.db.gidsOf pw).contains gr.gid
    | none => false
  | .group (.id g) => (ctx.db.gidsOf pw).contains g
  | .nonunixGroup _ => false

/-- `runas_userlist_matches` (`match.c` 151-214) over a list of members; `fuel` bounds the
alias nesting (the generated tables are acyclic). -/
def runasUserList (ctx : Ctx) (t : List (Def UserSpecifier)) :
    Nat → List (Spec UserSpecifier) → Tri
  | 0, _ => none
  | fuel + 1, l => lastSpecified l fun s =>
    match s.who with
    | .all => hit s
    | .alias n => match t.find? (·.name == n) with
      | some d => viaAlias s (runasUserList ctx t fuel d.items)
      | none => if ctx.runasPw.name == n then hit s else none
    | .only u => if userMember ctx ctx.runasPw u then hit s else none

/-- The `MYSELF` member of an empty runas user list (`match.c` 198-207). -/
def myself (ctx : Ctx) : Tri :=
  if (!ctx.userSpecified && ctx.groupSpecified) || ctx.invoker.name == ctx.runasPw.name then
    some true else none

/-- `group_matches` (`match.c` 587-613) for a plain member of a group list. -/
def groupMember (gr : GroupEnt) : UserSpecifier → Bool
  | .user (.name n) => gr.name == n
  | .user (.id n) => gr.gid == n
  | _ => false

/-- `runas_grouplist_matches` (`match.c` 222-284). `l = none` is a NULL group list. Members of
a group list are `Identifier`s, members of a `Runas_Alias` are `UserSpecifier`s; both are
handled as `UserSpecifier` (an identifier `i` is `.user i`), and `%group` members of an alias
are of type `USERGROUP`, which the switch ignores. -/
def runasGroupList (ctx : Ctx) (gr : GroupEnt) (t : List (Def UserSpecifier)) (userMatched : Tri) :
    Nat → Option (List (Spec UserSpecifier)) → Tri
  | 0, _ => none
  | fuel + 1, l =>
    let explicit := match l with
      | none => none
      | some l => lastSpecified l fun s =>
        match s.who with
        | .all => hit s
        | .alias n => match t.find? (·.name == n) with
          | some d => viaAlias s (runasGroupList ctx gr t userMatched fuel (some d.items))
          | none => if gr.name == n then hit s else none
        | .only u => if groupMember gr u then hit s else none
    -- 263-282: not explicitly matched, but the runas user matched: its own groups qualify
    if explicit.isNone && userMatched == some true then
      if ctx.runasPw.gid == gr.gid || (ctx.db.gidsOf ctx.runasPw).contains gr.gid then some true
      else none
    else explicit

def toUserSpec : Spec Identifier → Spec UserSpecifier
  | .allow m => .allow (match m with | .all => .all | .alias n => .alias n | .only i => .only (.user i))
  | .forbid m => .forbid (match m with | .all => .all | .alias n => .alias n | .only i => .only (.user i))

/-- `runaslist_matches` (`match.c` 294-331) for the runas spec in effect for an entry (the C
parser propagates runas lists exactly like `distribute_tags`, `gram.y` propagate_cmndspec).
No runas spec: the user list is `runas_default` (`root`, matched by name) and the group list is
NULL. `(users)`: no group list. `()` and `(: groups)`: the user list is `MYSELF`
(`gram.y` 670-750). -/
def runasMatches (ctx : Ctx) (t : List (Def UserSpecifier)) (r : Option RunAs) : Tri :=
  let fuel := t.length + 1
  let userMatched : Tri := match r with
    | none => if ctx.runasPw.name == "root" then some true else none
    | some ra => if ra.users.isEmpty then myself ctx else runasUserList ctx t fuel ra.users
  let groups : Option (List (Spec UserSpecifier)) := match r with
    | some ra => if ra.groups.isEmpty then none else some (ra.groups.map toUserSpec)
    | none => none
  let (userMatched, groupMatched) : Tri × Tri :=
    match ctx.groupSpecified, ctx.runasGr with
    | true, some gr =>
      let gm := runasGroupList ctx gr t userMatched fuel groups
      let um := if gm == some true && userMatched.isNone && ctx.invoker.name == ctx.runasPw.name
        then some true else userMatched
      (um, gm)
    | _, _ => (userMatched, none)
  if userMatched == some false || groupMatched == some false then some false
  else if userMatched == groupMatched || ctx.runasGr.isNone then userMatched
  else none

/-- `command_args_match` (`match_command.c` 80-112) on the generated argument patterns: no
arguments in sudoers allow anything, `""` allows none, otherwise `fnmatch` of the pattern
against the space-joined arguments. The generated words contain no metacharacters and no
spaces, so `a b` matches exactly `a b`, and `a b *` matches `a b ` followed by anything, i.e.
at least one further argument. -/
def cArgsMatch (args : List String) : Args → Bool
  | .prefix [] => true
  | .exact [] => args.isEmpty
  | .exact as => args == as
  | .prefix as => as.isPrefixOf args && as.length < args.length

def ctxOf (c : Case) (r : Request UserEnt GroupEnt) : Ctx :=
  { db := c.db, invoker := r.invokingUser,
    runasPw := match c.cli.runasUser, c.cli.runasGroup with
      | some _, _ => r.targetUser
      | none, some _ => r.invokingUser
      | none, none => (c.db.userNamed "root").getD r.targetUser,
    runasGr := if c.cli.runasGroup.isSome then some r.targetGroup else none,
    userSpecified := c.cli.runasUser.isSome, groupSpecified := c.cli.runasGroup.isSome }

/-- The decision with the chosen C components switched in; `none` if the request does not
resolve. -/
def decide (tg : Toggles) (c : Case) : Option (Option Tag) := do
  let r ← c.request
  let O := oracleOf c.db
  let p := c.policy
  let cmd : Command → Bool := fun cm =>
    O.globMatches cm.pattern r.command &&
      (if tg.cArgs then cArgsMatch r.arguments cm.args else argsMatch r.arguments cm.args)
  let ctx := ctxOf c r
  let runasOk (ra : Option RunAs) : Bool :=
    if tg.cRunas then runasMatches ctx p.aliases.runas ra == some true
    else (runasCheck O r (runasUserAliases O p r) (runasGroupAliases O p r) ra).isSome
  let allowed := (matchingUserSpecs O p r.invokingUser r.host).flatten.filterMap fun e =>
    if runasOk e.1 then some e.2 else none
  let t := findItem cmd (getAliases p.aliases.cmnd cmd) (allowed.map Prod.swap)
  return t.map fun t => if skipPasswd O r then { t with authenticate := .nopasswd } else t

theorem ite_isSome (o : Option γ) (b : β) :
    (if o.isSome = true then some b else none) = o.map (fun _ => b) := by
  cases o <;> rfl

/-- With both switches off, `decide` is the spec decision. -/
theorem decide_off (c : Case) : decide {} c = c.decision := by
  simp only [decide, Case.decision, Bool.false_eq_true, ite_false, ite_isSome]
  cases c.request <;> rfl

end Differential.CModel
