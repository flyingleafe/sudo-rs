import Differential.Case

/-!
# Explaining C sudo disagreements: the spec with C sudo's rules switched in

To attribute every spec-vs-C disagreement to a cause, `decide` is the spec decision
(`SudoersSpec.authorize`, built from the same spec functions) in which three components can
be replaced by transcriptions of the C sudo 1.9.18 code:

* `cRunas`: whether a command entry's runas spec permits the request, as C's
  `runaslist_matches` (`plugins/sudoers/match.c` 294-331) with `runas_userlist_matches`
  (151-214) and `runas_grouplist_matches` (222-284) decides it, instead of sudo-rs's
  `runas_allowed` (`check_permission`, `src/sudoers/mod.rs`);
* `cArgs`: argument matching as C's `command_args_match` (`match_command.c` 80-112) does it
  with `fnmatch(3)`, instead of `Args::Prefix` / `Args::Exact`;
* `cAliases`: what an alias reference means, as C evaluates it: `alias_get` (`alias.c`) looks
  the alias up when it is referenced, and its members are evaluated recursively; for a name
  that `alias_get` does not return (undefined, or already being evaluated: `ELOOP`), the
  `ALIAS` cases of `user_matches`, `host_matches`, `runas_userlist_matches` and
  `runas_grouplist_matches` fall through to `WORD`, and `cmnd_matches` matches nothing.
  `cValue` transcribes this; it replaces the `get_aliases` tables of the spec.

Everything else (user and host lists, command paths, last match wins, tag accumulation and the
implicit SETENV of `ALL`) is the spec's: on this fragment the C code computes the same
(`userlist_matches`, `hostlist_matches`, `cmndlist_matches` are "last specified member wins";
`propagate_cmndspec` in `gram.y` accumulates tags like `distribute_tags`). That claim is
checked, not assumed: `run.sh` reports how often `decide` with all switches agrees with
`testsudoers`.

With all switches off, `decide` is the spec decision (`decide_off`).
-/

namespace Differential.CModel

open SudoersSpec

structure Toggles where
  cRunas : Bool := false
  cArgs : Bool := false
  cAliases : Bool := false
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

/-- `alias_get`: the definition of `n`, unless it is undefined or on the stack of aliases
being evaluated (`a->used`, `ELOOP`). The first definition of a name (C rejects duplicates). -/
def aliasGet (t : List (Def α)) (stack : List String) (n : String) : Option (Def α) :=
  if stack.contains n then none else t.find? (·.name == n)

/-- C's evaluation of a member list with aliases (`userlist_matches`, `hostlist_matches`,
`cmndlist_matches`): `member` matches a plain member, `lit` matches the name of an alias that
`alias_get` does not return. `fuel` bounds the nesting (the stack grows by a new name each
level, so `t.length + 2` is enough). -/
def cList (t : List (Def α)) (member : α → Bool) (lit : String → Bool) :
    Nat → List String → SpecList α → Tri
  | 0, _, _ => none
  | fuel + 1, stack, l => lastSpecified l fun s =>
    match s.who with
    | .all => hit s
    | .only x => if member x then hit s else none
    | .alias n => match aliasGet t stack n with
      | some d => viaAlias s (cList t member lit fuel (n :: stack) d.items)
      | none => if lit n then hit s else none

/-- The value C gives a reference to alias `n` from a rule, as an entry of a spec alias table
(`FoundAliases`): `some true` allow, `some false` deny, `none` unspecified. -/
def cValue (t : List (Def α)) (member : α → Bool) (lit : String → Bool) : FoundAliases :=
  fun n => cList t member lit (t.length + 2) [] [.allow (.alias n)]

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

/-- `runas_userlist_matches` (`match.c` 151-214) over a list of members. -/
def runasUserList (ctx : Ctx) (t : List (Def UserSpecifier)) :
    Nat → List String → List (Spec UserSpecifier) → Tri
  | 0, _, _ => none
  | fuel + 1, stack, l => lastSpecified l fun s =>
    match s.who with
    | .all => hit s
    | .alias n => match aliasGet t stack n with
      | some d => viaAlias s (runasUserList ctx t fuel (n :: stack) d.items)
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
are of type `USERGROUP`, which the switch ignores. An alias is evaluated by a recursive call,
so the fallback to the runas user's own groups (263-282) also applies inside an alias body. -/
def runasGroupList (ctx : Ctx) (gr : GroupEnt) (t : List (Def UserSpecifier)) (userMatched : Tri) :
    Nat → List String → Option (List (Spec UserSpecifier)) → Tri
  | 0, _, _ => none
  | fuel + 1, stack, l =>
    let explicit := match l with
      | none => none
      | some l => lastSpecified l fun s =>
        match s.who with
        | .all => hit s
        | .alias n => match aliasGet t stack n with
          | some d => viaAlias s (runasGroupList ctx gr t userMatched fuel (n :: stack) (some d.items))
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
  let userMatched : Tri := match r with
    | none => if ctx.runasPw.name == "root" then some true else none
    | some ra => if ra.users.isEmpty then myself ctx
      else runasUserList ctx t (t.length + 2) [] ra.users
  let groups : Option (List (Spec UserSpecifier)) := match r with
    | some ra => if ra.groups.isEmpty then none else some (ra.groups.map toUserSpec)
    | none => none
  let (userMatched, groupMatched) : Tri × Tri :=
    match ctx.groupSpecified, ctx.runasGr with
    | true, some gr =>
      let gm := runasGroupList ctx gr t userMatched (t.length + 2) [] groups
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

/-- The command entries of the lines and host groups that apply, with C's alias semantics for
the user and host lists. -/
def cCandidates (O : Oracle UserEnt GroupEnt) (c : Case) (r : Request UserEnt GroupEnt) :
    List MatchedCommand :=
  let w := c.written
  let UT := cValue w.user (matchUser O r.invokingUser) (· == r.invokingUser.name)
  let HT := cValue w.host (matchHost O r.host) (· == r.host)
  c.rules.flatMap fun rule =>
    if (findItem (matchUser O r.invokingUser) UT (withUnit rule.users)).isSome then
      rule.permissions.flatMap fun seg =>
        if (findItem (matchHost O r.host) HT (withUnit seg.1)).isSome then distributeTags seg.2
        else []
    else []

/-- The decision with the chosen C components switched in; `none` if the request does not
resolve. -/
def decide (tg : Toggles) (c : Case) : Option (Option Tag) := do
  let r ← c.request
  let O := oracleOf c.db
  let p := c.policy
  let w := c.written
  let cmd : Command → Bool := fun cm =>
    O.globMatches cm.pattern r.command &&
      (if tg.cArgs then cArgsMatch r.arguments cm.args else argsMatch r.arguments cm.args)
  let ctx := ctxOf c r
  let RU := if tg.cAliases then cValue w.runas (matchUser O r.targetUser) (· == r.targetUser.name)
    else runasUserAliases O p r
  let RG := if tg.cAliases then
      cValue w.runas (matchGroupAlias O r.targetGroup) (· == r.targetGroup.name)
    else runasGroupAliases O p r
  let runasOk (ra : Option RunAs) : Bool :=
    if tg.cRunas then runasMatches ctx w.runas ra == some true
    else (runasCheck O r RU RG ra).isSome
  let cands := if tg.cAliases then cCandidates O c r
    else (matchingUserSpecs O p r.invokingUser r.host).flatten
  let allowed := cands.filterMap fun e =>
    if runasOk e.1 then some e.2 else none
  let CT := if tg.cAliases then cValue w.cmnd cmd (fun _ => false)
    else getAliases p.aliases.cmnd cmd
  let t := findItem cmd CT (allowed.map Prod.swap)
  return t.map fun t => if skipPasswd O r then { t with authenticate := .nopasswd } else t

theorem ite_isSome (o : Option γ) (b : β) :
    (if o.isSome = true then some b else none) = o.map (fun _ => b) := by
  cases o <;> rfl

/-- With all switches off, `decide` is the spec decision. -/
theorem decide_off (c : Case) : decide {} c = c.decision := by
  simp only [decide, Case.decision, Bool.false_eq_true, ite_false, ite_isSome]
  cases c.request <;> rfl

end Differential.CModel
