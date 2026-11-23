import Differential.Generate
import Differential.Engine
import Differential.Inline
import Differential.Minimize

/-!
# Properties of the real sudo-rs decision, as predicates over cases

Each property is stated twice:

* as a Lean proposition over an `EngineFn`, the function from a probe (policy text and
  request) to the result line the engine gives. `EngineFn` abstracts the real sudo-rs code:
  `Sudoers::read` followed by `Sudoers::check` (or `Sudoers::matching_entries` for
  `sudo -l`), as the harness `src/sudoers/test/differential.rs` runs them. The proposition is
  what is tested; it is not proved;
* as an executable check of one instance (`Prop'.check`), which the search (`PropRun.lean`)
  evaluates on generated instances with the results of the real code.

The instances are drawn by the generator of the differential test (`Generate.lean`), with the
alias hazards, and then transformed as the property says. Preconditions are computed in Lean;
where one needs a semantic notion ("the last line decides the request"), it is computed with
the spec (`SudoersSpec`), never the conclusion.
-/

namespace Differential.Props

open SudoersSpec Gen Engine
open SudoersSpec.Analysis (aliasRefsOf)

/-- The engine under test: the result line for a probe. -/
abbrev EngineFn := Probe → String

instance : Inhabited PermissionSpec := ⟨⟨[], []⟩⟩

/-- The verdict the engine gives (without diagnostics). -/
def verdict (E : EngineFn) (p : Probe) : String := verdictOf (E p)

/-- A line of policy text: a user specification, an alias definition, or any text. -/
inductive Line where
  | rule (r : PermissionSpec)
  | defn (d : AnyDef)
  | raw (s : String)
  deriving Inhabited

def Line.text : Line → String
  | .rule r => SudoersSpec.Grammar.PermissionPrint.permissionSpec r
  | .defn d => Print.anyDef d
  | .raw s => s

/-- `lines` with `x` inserted before position `k`. -/
def insertAt (lines : List String) (k : Nat) (xs : List String) : List String :=
  lines.take k ++ xs ++ lines.drop k

/-- The probe of a case with other policy text. -/
def _root_.Differential.Case.withLines (c : Case) (lines : List String) : Probe :=
  { c.probe with sudoers := lines }

/-- The probe of a case with other `-u`/`-g` words. -/
def _root_.Differential.Case.withFlags (c : Case) (flags : List String) : Probe :=
  { c.probe with flags := flags }

/-! ## (a) Lines for other users are irrelevant -/

/-- The user list of a line names only others: every item is a plain, non-negated user or
group specifier (`name`, `#uid`, `%group`, `%#gid`) that does not match the invoking user in
the case's database, and no name is spelled like an alias. -/
def lineForOthers (c : Case) (l : PermissionSpec) : Bool :=
  match c.db.userNamed c.invoker with
  | none => false
  | some inv => l.users.all fun s => match s with
    | .allow (.only u) =>
      !matchUser (oracleOf c.db) inv u &&
        (match u with
          | .user (.name n) => Generate.policyUserNames.contains n
          | .nonunixGroup _ => false
          | _ => true)
    | _ => false

/-- **(a)** Inserting a line for other users anywhere in the text never changes the invoking
user's decision. -/
def OtherUsersLineIrrelevant (E : EngineFn) : Prop :=
  ∀ (c : Case) (k : Nat) (l : PermissionSpec), lineForOthers c l = true →
    verdict E (c.withLines (insertAt c.sudoersLines k [SudoersSpec.Grammar.PermissionPrint.permissionSpec l])) =
      verdict E c.probe

/-! ## (b) Appending a line without a command-side `!` never revokes -/

/-- Does a `Cmnd_Alias` named `n` (any of its definitions) contain a `!`, directly or through
the aliases it refers to? `true` when `fuel` runs out (conservative). -/
def cmndAliasHasForbid (t : List (Def Command)) : Nat → String → Bool
  | 0, _ => true
  | fuel + 1, n => (t.filter (·.name == n)).any fun d => d.items.any fun s =>
    match s with
    | .forbid _ => true
    | .allow (.alias m) => cmndAliasHasForbid t fuel m
    | .allow _ => false

/-- The appended line has no command-side `!`: a rule has no negated command and refers to no
`Cmnd_Alias` containing `!` (in the tables of the extended policy); a `Cmnd_Alias`
definition contains no `!` and refers to no such alias. Definitions of the other kinds have no
command side. -/
def noCommandForbid (c : Case) (l : Line) : Bool :=
  let defs := match l with | .defn d => c.defs ++ [d] | _ => c.defs
  let t := (writtenTables defs).cmnd
  let fuel := t.length + 1
  let ok (s : Spec Command) : Bool := match s with
    | .forbid _ => false
    | .allow (.alias n) => !cmndAliasHasForbid t fuel n
    | .allow _ => true
  match l with
  | .rule r => r.permissions.all (·.2.all fun e => ok e.2.cmd)
  | .defn (.cmnd d) => d.items.all ok
  | .defn _ => true
  | .raw _ => false

/-- **(b)** Appending a line with no command-side `!` (and no `Cmnd_Alias` containing `!`)
never turns an allowed request into a refused one. -/
def AppendNeverRevokes (E : EngineFn) : Prop :=
  ∀ (c : Case) (l : Line), noCommandForbid c l = true →
    allows (verdict E c.probe) = true →
    allows (verdict E (c.withLines (c.sudoersLines ++ [l.text]))) = true

/-! ## (c) Unmentioned users, hosts and commands are never allowed -/

/-- Every item of the user lists of the rules and of the `User_Alias` bodies. -/
def userItems (c : Case) : List (Spec UserSpecifier) :=
  c.rules.flatMap (·.users) ++ (c.written.user.flatMap (·.items))

def hostItems (c : Case) : List (Spec Hostname) :=
  c.rules.flatMap (·.permissions.flatMap (·.1)) ++ (c.written.host.flatMap (·.items))

def commandItems (c : Case) : List (Spec Command) :=
  c.rules.flatMap (·.permissions.flatMap (·.2.map (·.2.cmd))) ++ (c.written.cmnd.flatMap (·.items))

/-- The user lists mention the invoking user: `ALL`, an item matching them (name, `#uid`, a
group they are in by name or `#gid`), or an alias reference spelled like their name. -/
def userMentioned (c : Case) : Bool :=
  match c.db.userNamed c.invoker with
  | none => true
  | some inv => (userItems c).any fun s => match s.who with
    | .all => true
    | .only u => matchUser (oracleOf c.db) inv u
    | .alias n => n == inv.name

def hostMentioned (c : Case) : Bool :=
  (hostItems c).any fun s => match s.who with
    | .all => true
    | .only h => h == c.host
    | .alias n => n == c.host

def commandMentioned (c : Case) : Bool :=
  (commandItems c).any fun s => match s.who with
    | .all => true
    | .only cm => cm.pattern == c.command
    | .alias _ => false

/-- **(c)** A request whose invoking user, host or command the policy never mentions (in user
lists and `User_Alias` bodies, host lists and `Host_Alias` bodies, command lists and
`Cmnd_Alias` bodies respectively, with `ALL` counting as a mention) is refused. -/
def UnmentionedNeverAllowed (E : EngineFn) : Prop :=
  ∀ c : Case, (userMentioned c && hostMentioned c && commandMentioned c) = false →
    allows (verdict E c.probe) = false

/-! ## (d) Textual alias expansion preserves every decision -/

/-- **(d)** For a policy whose alias tables produce no diagnostic, expanding every alias
reference textually (`Case.inlined`: bodies inlined, negations flipped, definitions deleted)
gives the same verdict, tags included, for every request. -/
def AliasExpansionPreserves (E : EngineFn) : Prop :=
  ∀ c : Case, c.diagnostics = [] → verdict E c.inlined.probe = verdict E c.probe

/-! ## (e) Lines before a deciding last line are irrelevant -/

/-- With the spec: the last rule contains an entry that applies to the invoking user and host,
whose runas spec permits the request and whose command spec takes part (so it decides). -/
def lastLineDecides (c : Case) : Bool :=
  match c.request, c.rules.getLast? with
  | some r, some last =>
    let O := oracleOf c.db
    let pl : Policy := { c.policy with rules := [last] }
    (allowedSpec O pl r).any (cmdParticipates O pl r)
  | _, _ => false

/-- Alias names a case defines or refers to. -/
def namesUsed (c : Case) : List String :=
  c.defs.map (·.name) ++ c.rules.flatMap fun r => aliasRefsOf r.users ++
    r.permissions.flatMap fun g => aliasRefsOf g.1 ++ g.2.flatMap fun e =>
      aliasRefsOf [e.2.cmd] ++ (match e.1 with
        | some ra => aliasRefsOf ra.users ++ aliasRefsOf ra.groups
        | none => [])

/-- The prepended lines define only names the case neither defines nor refers to, and none
ends in a backslash (which would continue onto the next line). -/
def freshPrefix (c : Case) (xs : List Line) : Bool :=
  xs.all fun
    | .defn d => !(namesUsed c).contains d.name
    | .raw s => !s.endsWith "\\"
    | .rule _ => true

/-- **(e)** If the last line decides the request, inserting any lines before it (rules for
anyone, definitions of fresh aliases, lines that do not parse) changes nothing. -/
def PrependIrrelevant (E : EngineFn) : Prop :=
  ∀ (c : Case) (k : Nat) (xs : List Line), lastLineDecides c = true →
    freshPrefix c xs = true → k < c.sudoersLines.length →
    verdict E (c.withLines (insertAt c.sudoersLines k (xs.map Line.text))) = verdict E c.probe

/-! ## (f) `sudo -l` is faithful -/

/-- The listing of a case: the entries `sudo -l` prints for the invoking user on the host. -/
def _root_.Differential.Case.listProbe (c : Case) : Probe := { c.probe with mode := "list" }

/-- The entries of a `list` result line. -/
def listedEntries (result : String) : List String :=
  match (verdictOf result).splitOn "list " with
  | ["", rest] => (rest.splitOn "\t").filter (!·.isEmpty)
  | _ => []

/-- The listing read back as a policy: the `Runas_Alias` definitions of the case (the listing
names runas aliases without expanding them), then one line per entry for the invoking user,
written as `#uid` (an upper-case name would read as an alias), on every host. -/
def relisted (c : Case) (entries : List String) : List String :=
  let uid := (c.db.userNamed c.invoker).map (·.uid) |>.getD 0
  (c.defs.filterMap fun | .runas d => some (Print.anyDef (.runas d)) | _ => none) ++
    entries.map fun e => s!"#{uid} ALL = {e.trimAscii}"

/-- A request of the invoking user on the host: `-u`/`-g`, command, arguments. -/
structure Req where
  cli : Cli
  command : String
  args : List String
  deriving Inhabited

def Req.on (q : Req) (c : Case) (lines : List String) : Probe :=
  { c.probe with flags := q.cli.flags, command := q.command :: q.args, sudoers := lines }

/-- **(f)** The entries `sudo -l` prints for a user on a host, read back as a policy, decide
every request of that user on that host like the full policy: allow or deny, and whether a
password is asked. -/
def ListingFaithful (E : EngineFn) : Prop :=
  ∀ (c : Case) (q : Req),
    authOutcome (verdict E (q.on c (relisted c (listedEntries (E c.listProbe))))) =
      authOutcome (verdict E (q.on c c.sudoersLines))

/-! ## (g) Spellings of uid 0 -/

/-- Spellings of the runas user that `NameOrId::parse` may read as uid 0, and some that it
must reject. -/
def uidSpellings : List String :=
  ["#0", "#00", "#+0", "#000", "#+00", "#0000000000", "#-0", "#0x0", "#4294967296", "#"]

def gidSpellings : List String := ["#0", "#00", "#+0", "#-0"]

/-- The first passwd entry with uid 0 is `root` (what `getpwuid(0)` returns). -/
def rootFirst (c : Case) : Bool :=
  (c.db.users.find? (·.uid == 0)).map (·.name) == some "root"

/-- Replace `-u`'s or `-g`'s argument. -/
def setFlag : List String → String → String → List String
  | x :: w :: rest, f, v => if x == f then f :: v :: rest else x :: w :: setFlag rest f v
  | flags, f, v => flags ++ [f, v]

/-- **(g)** Under a policy with `(ALL, !root)`, `-u '#0'` and every other spelling of uid 0
behaves like `-u root` (or is refused as an unknown user), and likewise `-g '#0'` like
`-g root`, provided `getpwuid(0)` is `root`. -/
def UidSpellingsLikeRoot (E : EngineFn) : Prop :=
  ∀ (c : Case), rootFirst c = true →
    (∀ s ∈ uidSpellings,
      let v := verdict E (c.withFlags (setFlag c.cli.flags "-u" s))
      v = verdict E (c.withFlags (setFlag c.cli.flags "-u" "root")) ∨ v.startsWith "error") ∧
    (∀ s ∈ gidSpellings,
      let v := verdict E (c.withFlags (setFlag c.cli.flags "-g" s))
      v = verdict E (c.withFlags (setFlag c.cli.flags "-g" "root")) ∨ v.startsWith "error")

/-! ## Executable checks -/

/-- The outcome of one instance. -/
inductive Outcome where
  /-- The precondition does not hold. -/
  | vacuous
  | holds
  /-- Outside the precondition, but of interest: recorded under `cls`, with whether the
  conclusion failed. -/
  | outside (cls : String) (failed : Bool)
  | violated (cls : String)
  deriving Inhabited, BEq

/-- A property with its search: instances, their probes in one or two rounds, the check, a
shrinker, and a short description. -/
structure Prop' (I : Type) where
  name : String
  statement : String
  gen : Nat → Gen I
  stage1 : I → List Probe
  stage2 : I → List String → List Probe := fun _ _ => []
  check : I → List String → List String → Outcome
  shrink : I → List I
  describe : I → String

def showCase (c : Case) : String :=
  "\n".intercalate (c.sudoersLines.map ("  | " ++ ·)) ++
    s!"\n  request: {c.invoker}@{c.host} {" ".intercalate c.cli.flags} " ++
    " ".intercalate (c.command :: c.args)

/-- `ALL` replaced by a plain item, so that a mention test can succeed. -/
def noAll (plain : α) (l : SpecList α) : SpecList α :=
  l.map fun s => match s with
    | .allow .all => .allow (.only plain)
    | .forbid .all => .forbid (.only plain)
    | s => s

def hazardsGen : Gen Generate.Hazards := Generate.hazards

/-- Positive plain user specifiers that do not match the invoking user. -/
def othersOf (c : Case) : List UserSpecifier :=
  let cands : List UserSpecifier :=
    Generate.policyUserNames.map (.user ∘ .name) ++ Generate.uids.map (.user ∘ .id) ++
      Generate.groupNames.map (.group ∘ .name) ++ Generate.gids.map (.group ∘ .id)
  match c.db.userNamed c.invoker with
  | some inv => cands.filter (!matchUser (oracleOf c.db) inv ·)
  | none => cands

def tableOf (c : Case) : AliasTable := c.written

instance : Inhabited UserSpecifier := ⟨.user (.name "nobody")⟩

def propA : Prop' (Case × Nat × PermissionSpec) where
  name := "a-other-users-line"
  statement := "inserting a line for other users never changes the invoker's decision"
  gen i := do
    let c ← Generate.case_ i
    let h ← hazardsGen
    let r ← Generate.rule h (tableOf c)
    let others := othersOf c
    let users ← listOf 1 3 (pick others)
    let k ← below (c.sudoersLines.length + 1)
    return (c, k, { r with users := users.map (.allow ∘ .only) })
  stage1 := fun (c, k, l) =>
    [c.probe, c.withLines (insertAt c.sudoersLines k [SudoersSpec.Grammar.PermissionPrint.permissionSpec l])]
  check := fun (c, _, l) rs _ =>
    if !lineForOthers c l then .vacuous
    else match rs with
      | [b, v] => if verdictOf b == verdictOf v then .holds else .violated "other"
      | _ => .violated "missing"
  shrink := fun (c, k, l) =>
    (Minimize.shrinks c).map (·, k, l) ++ (Minimize.shrinkRule l).map (c, k, ·) ++
      (if k > 0 then [(c, k - 1, l)] else [])
  describe := fun (c, k, l) =>
    showCase c ++ s!"\n  inserted before line {k}: {SudoersSpec.Grammar.PermissionPrint.permissionSpec l}"

/-- Turn negated commands into plain ones. -/
def positive (r : PermissionSpec) : PermissionSpec :=
  { r with permissions := r.permissions.map fun (hs, es) =>
      (hs, es.map fun (ra, cs) => (ra, { cs with cmd := match cs.cmd with
        | .forbid x => .allow x
        | s => s })) }

def defLine (c : Case) : Gen AnyDef := do
  let w := c.written
  let pickName (pfx : String) (existing : List String) : Gen String := do
    pick (existing ++ [pfx ++ "7", pfx ++ "9"] ++ (if pfx == "UA" then ["UA1"] else []))
  match ← below 4 with
  | 0 => return .user ⟨← pickName "UA" (w.user.map (·.name)),
      ← listOf 1 3 (Generate.item Generate.userSpecifier (w.user.map (·.name)))⟩
  | 1 => return .runas ⟨← pickName "RA" (w.runas.map (·.name)),
      ← listOf 1 3 (Generate.item Generate.userSpecifier (w.runas.map (·.name)))⟩
  | 2 => return .host ⟨← pickName "HA" (w.host.map (·.name)),
      ← listOf 1 3 (Generate.item Generate.plainHost (w.host.map (·.name)))⟩
  | _ => return .cmnd ⟨← pickName "CA" (w.cmnd.map (·.name)),
      ← listOf 1 3 (Generate.item Generate.command (w.cmnd.map (·.name)))⟩

/-- Classes of (b) violations, by the appended line: a definition of a name the policy defines
(`definition-duplicate`), of a name it refers to without defining it (`P1`), of another name, a
rule. -/
def classB (c : Case) : Line → String
  | .defn d =>
    if (c.defs.map (·.name)).contains d.name then "definition-duplicate"
    else if (namesUsed c).contains d.name then "P1"
    else "definition-other"
  | .rule _ => "rule"
  | .raw _ => "raw"

def propB : Prop' (Case × Line) where
  name := "b-append-never-revokes"
  statement := "appending a line without command-side ! never revokes"
  gen i := do
    let c ← Generate.case_ i
    let h ← hazardsGen
    let l ← if ← chance 1 2 then do
        let r ← Generate.rule h (tableOf c)
        pure (Line.rule (if ← chance 3 4 then positive r else r))
      else Line.defn <$> defLine c
    return (c, l)
  stage1 := fun (c, l) => [c.probe, c.withLines (c.sudoersLines ++ [l.text])]
  check := fun (c, l) rs _ =>
    if !noCommandForbid c l then .vacuous
    else match rs with
      | [b, v] =>
        if !allows (verdictOf b) then .vacuous
        else if allows (verdictOf v) then .holds else .violated (classB c l)
      | _ => .violated "missing"
  shrink := fun (c, l) =>
    (Minimize.shrinks c).map (·, l) ++
    (match l with
      | .rule r => (Minimize.shrinkRule r).map fun r => (c, .rule r)
      | .defn d => (Minimize.shrinkAnyDef d).map fun d => (c, .defn d)
      | .raw _ => [])
  describe := fun (c, l) => showCase c ++ s!"\n  appended: {l.text}"

def mapUserDefs (f : SpecList UserSpecifier → SpecList UserSpecifier) : AnyDef → AnyDef
  | .user d => .user { d with items := f d.items }
  | d => d

def mapHostDefs (f : SpecList Hostname → SpecList Hostname) : AnyDef → AnyDef
  | .host d => .host { d with items := f d.items }
  | d => d

def mapCmndDefs (f : SpecList Command → SpecList Command) : AnyDef → AnyDef
  | .cmnd d => .cmnd { d with items := f d.items }
  | d => d

def mapGroups (f : SpecList Hostname → SpecList Hostname)
    (g : List (Option RunAs × CommandSpec) → List (Option RunAs × CommandSpec))
    (r : PermissionSpec) : PermissionSpec :=
  { r with permissions := r.permissions.map fun (hs, es) => (f hs, g es) }

/-- A command path that no generated policy mentions (and that does not exist). -/
def unmentionedPath : String := "/opt/sudo-differential-unmentioned/x"

/-- Remove `ALL` from user, host or command positions (`kind` 0, 1, 2), then make the
invoking user, host or command one the policy is unlikely to mention. -/
def unmention (c : Case) (kind : Nat) : Gen Case := do
  match kind with
  | 0 =>
    let eve : UserSpecifier := .user (.name "eve")
    let c : Case := { c with
      rules := c.rules.map fun r => { r with users := noAll eve r.users },
      defs := c.defs.map (mapUserDefs (noAll eve)) }
    let cands := c.db.users.map (·.name) |>.filter fun n => !userMentioned { c with invoker := n }
    if cands.isEmpty then return c
    return { c with invoker := ← pick cands }
  | 1 =>
    let c : Case := { c with
      rules := c.rules.map (mapGroups (noAll "h3") id),
      defs := c.defs.map (mapHostDefs (noAll "h3")) }
    return { c with host := ← pick ["h4", "h5"] }
  | _ =>
    let plain : Command := ⟨"/bin/ls", .prefix []⟩
    let fix (es : List (Option RunAs × CommandSpec)) : List (Option RunAs × CommandSpec) :=
      es.map fun (ra, cs) => (ra, { cs with cmd := (noAll plain [cs.cmd]).headD cs.cmd })
    let c : Case := { c with
      rules := c.rules.map (mapGroups id fix),
      defs := c.defs.map (mapCmndDefs (noAll plain)) }
    return { c with command := unmentionedPath, args := ← listOf 0 1 (pick Generate.argPool) }

def propC : Prop' Case where
  name := "c-unmentioned-never-allowed"
  statement := "a user, host or command the policy never mentions is never allowed"
  gen i := do unmention (← Generate.case_ i) (i % 3)
  stage1 := fun c => [c.probe]
  check := fun c rs _ =>
    if userMentioned c && hostMentioned c && commandMentioned c then .vacuous
    else match rs with
      | [b] => if allows (verdictOf b) then
          .violated (if !userMentioned c then "user" else if !hostMentioned c then "host" else "command")
        else .holds
      | _ => .violated "missing"
  shrink := Minimize.shrinks
  describe := showCase

/-- Does a `Cmnd_Alias` body (as written) contain `ALL`? -/
def cmndAliasWithAll (c : Case) : Bool :=
  c.written.cmnd.any (·.items.any (·.who == .all))

/-- Does the expansion put a `%group` member of a `Runas_Alias` into a runas group list (where
the grammar has no `%group`)? -/
def percentInGroupList (c : Case) : Bool :=
  c.rules.any (·.permissions.any (·.2.any fun e => match e.1 with
    | some ra => ra.groups.any fun s => match s.who with
      | .only (.name n) => n.startsWith "%"
      | _ => false
    | none => false))

/-- The fields of a verdict that differ. -/
def verdictDiff (a b : String) : String :=
  let fa := a.splitOn " "
  let fb := b.splitOn " "
  if fa.length != fb.length || fa.head? != fb.head? then "allow-deny"
  else "-".intercalate ((fa.zip fb).filterMap fun (x, y) =>
    if x == y then none else some ((x.splitOn "=").headD x))

def propD : Prop' Case where
  name := "d-alias-expansion"
  statement := "textual alias expansion preserves every decision"
  gen i := Generate.case_ i
  stage1 := fun c => [c.probe, c.inlined.probe]
  check := fun c rs _ =>
    if !c.diagnostics.isEmpty then .vacuous
    else match rs with
      | [b, v] =>
        if verdictOf b == verdictOf v then .holds
        else
          let d := verdictDiff (verdictOf b) (verdictOf v)
          if !(diagnosticsOf v).isEmpty then
            if percentInGroupList c.inlined then .violated s!"group-list-gets-percent-member/{d}"
            else .violated s!"expansion-does-not-parse/{d}"
          else if d == "env" && cmndAliasWithAll c then .violated "cmnd-alias-all-setenv"
          else .violated s!"other/{d}"
      | _ => .violated "missing"
  shrink := Minimize.shrinks
  describe := fun c => showCase c ++ "\n  expanded:\n" ++
    "\n".intercalate (c.inlined.sudoersLines.map ("  | " ++ ·))

/-- Lines that do not parse (or only partly), none ending in a backslash. -/
def garbagePool : List String :=
  [ "alice ALL = (root", "bob ALL = INTERCEPT: ALL", "carol ALL = NOTBEFORE=20200101 /bin/ls",
    "Cmnd_Alias = /bin/ls", "User_Alias ua = bob", "alice ALL = sha224:abc /bin/ls",
    "alice ALL = /bin/ls ^x", "%", "\"", "alice ALL = ALL ) junk", "dave ALL = (ALL) ALL !/bin/ls",
    "Host_Alias ALL = h1", "bob h1 = TIMEOUT=10 /bin/cat", "alice ALL = /bin/l[s",
    "@include /nonexistent/sudoers", "#include /nonexistent/sudoers", "Defaults", "alice",
    "ALL ALL = ROLE=x /bin/ls", "eve ALL = CHROOT=/ ALL", "(" ]

def prefixLine (c : Case) : Gen Line := do
  let h ← hazardsGen
  match ← weighted [(4, 0), (2, 1), (1, 2), (3, 3)] with
  | 0 => Line.rule <$> Generate.rule h (tableOf c)
  | 1 =>
    let d ← defLine c
    let fresh : AnyDef := match d with
      | .user d => .user { d with name := "UA5" } | .runas d => .runas { d with name := "RA5" }
      | .host d => .host { d with name := "HA5" } | .cmnd d => .cmnd { d with name := "CA5" }
    return .defn fresh
  | 2 => Line.defn <$> defLine c
  | _ => Line.raw <$> pick garbagePool

def propE : Prop' (Case × Nat × List Line) where
  name := "e-prefix-irrelevant"
  statement := "lines inserted before a last line that decides the request change nothing"
  gen i := do
    let c ← Generate.case_ i
    -- a request aimed at the last line, so that it often decides
    let c ← match c.rules.getLast? with
      | some last => do
        let (invoker, host, cli, command, args) ← Generate.request [last] c.written
        pure { c with invoker, host, cli, command, args }
      | none => pure c
    let xs ← listOf 1 4 (prefixLine c)
    let k ← below c.sudoersLines.length
    return (c, k, xs)
  stage1 := fun (c, k, xs) =>
    let k := min k (c.sudoersLines.length - 1)
    [c.probe, c.withLines (insertAt c.sudoersLines k (xs.map Line.text))]
  check := fun (c, _, xs) rs _ =>
    if !lastLineDecides c then .vacuous
    else match rs with
      | [b, v] =>
        let same := verdictOf b == verdictOf v
        if !freshPrefix c xs then .outside "redefines-an-alias-of-the-policy" (!same)
        else if same then .holds else .violated "other"
      | _ => .violated "missing"
  shrink := fun (c, k, xs) =>
    (Minimize.shrinks c).map (·, k, xs) ++ (Minimize.drops xs).map (c, k, ·) ++
      (Minimize.shrinkEach xs fun
        | .rule r => (Minimize.shrinkRule r).map .rule
        | .defn d => (Minimize.shrinkAnyDef d).map .defn
        | .raw _ => []).map (c, k, ·)
  describe := fun (c, k, xs) => showCase c ++ s!"\n  inserted before line {k}:\n" ++
    "\n".intercalate (xs.map (fun x => "  + " ++ x.text))

def reqGen (c : Case) : Gen Req := do
  let (_, _, cli, command, args) ← Generate.request c.rules c.written
  return { cli, command, args }

/-- Diagnostics other than the alias-table ones (which the copied `Runas_Alias` definitions of
a relisted policy repeat): parse errors. -/
def parseDiagnostics (result : String) : List String :=
  (diagnosticsOf result).filter fun d =>
    !(d.startsWith "recursive alias" || d.startsWith "multiple occurrences" ||
      d.startsWith "undefined alias")

/-- Classes of (f) violations: the listing does not parse back (`P3` if it contains `???`);
the target user is a uid-0 account other than `root` (spec README finding 4); the invoking
user's name is spelled like an alias (`P2`). -/
def classF (c : Case) (listing : String) (q : Req) (base relist : String) : String :=
  let target := q.cli.runasUser.getD (if q.cli.runasGroup.isSome then c.invoker else "root")
  let uid0 := (c.db.userNamed target).any (·.uid == 0) && target != "root"
  if !(parseDiagnostics relist).isEmpty then
    if (verdictOf listing).contains "???" then "P3" else "listing-does-not-parse"
  else if uid0 then "uid-0-account-without-runas-spec"
  else if Generate.capsUsers.contains c.invoker then "P2"
  else s!"other/{authOutcome (verdictOf base)}-vs-{authOutcome (verdictOf relist)}"

/-- Compare the base and relisted verdicts of each request, in order. -/
def checkPairs (c : Case) (listing : String) : List Req → List String → Outcome
  | q :: qs, b :: v :: rest =>
    if authOutcome (verdictOf b) == authOutcome (verdictOf v) then checkPairs c listing qs rest
    else .violated (classF c listing q b v)
  | [], _ => .holds
  | _, _ => .violated "missing"

def propF : Prop' (Case × List Req) where
  name := "f-listing-faithful"
  statement := "the entries sudo -l prints, read back as a policy, decide like the policy"
  gen i := do
    let c ← Generate.case_ i
    return (c, ← listOf 6 6 (reqGen c))
  stage1 := fun (c, _) => [c.listProbe]
  stage2 := fun (c, qs) r1 =>
    let listed := relisted c (listedEntries (r1.headD ""))
    qs.flatMap fun q => [q.on c c.sudoersLines, q.on c listed]
  check := fun (c, qs) r1 r2 =>
    if c.db.userNamed c.invoker |>.isNone then .vacuous else checkPairs c (r1.headD "") qs r2
  shrink := fun (c, qs) =>
    (Minimize.shrinks c).map (·, qs) ++ (Minimize.drops qs).map (c, ·)
  describe := fun (c, qs) => showCase c ++ "\n  requests:\n" ++
    "\n".intercalate (qs.map fun q =>
      s!"  - {" ".intercalate q.cli.flags} {" ".intercalate (q.command :: q.args)}")

/-- A policy with a `(ALL, !root)` line (or `!#0`) for the invoking user, and sometimes the
uid-0 account `toor` before `root` in the passwd file. -/
def uidCase (i : Nat) : Gen Case := do
  let c ← Generate.case_ i
  let notRoot : Spec UserSpecifier := if ← chance 1 2 then .forbid (.only (.user (.name "root")))
    else .forbid (.only (.user (.id 0)))
  let groups : SpecList Identifier := if ← chance 1 2 then [] else [.allow .all]
  let ra : RunAs := ⟨[.allow .all, notRoot], groups⟩
  let cmd : Command := ⟨c.command, .prefix []⟩
  let entry : Option RunAs × CommandSpec := (some ra, ⟨[], .allow (.only cmd)⟩)
  let users ← if ← chance 1 4 then
      pure (c.db.users.filter (·.name == "toor") ++ c.db.users.filter (·.name != "toor"))
    else pure c.db.users
  -- a plain user name; upper-case invokers would read as aliases
  let c := if Generate.capsUsers.contains c.invoker then { c with invoker := "alice" } else c
  let line : PermissionSpec :=
    ⟨[.allow (.only (.user (.name c.invoker)))], [([.allow .all], [entry])]⟩
  return { c with rules := c.rules ++ [line], db := { c.db with users } }

def propG : Prop' Case where
  name := "g-uid-spellings"
  statement := "-u '#0' and other spellings of uid 0 behave like -u root under (ALL, !root)"
  gen i := uidCase i
  stage1 := fun c =>
    (("root" :: uidSpellings).map fun s => c.withFlags (setFlag c.cli.flags "-u" s)) ++
    (("root" :: gidSpellings).map fun s => c.withFlags (setFlag c.cli.flags "-g" s))
  check := fun c rs _ =>
    let nu := uidSpellings.length + 1
    let us := rs.take nu
    let gs := rs.drop nu
    let ok (l : List String) := match l with
      | r :: rest => rest.all fun v => verdictOf v == verdictOf r || (verdictOf v).startsWith "error"
      | [] => false
    let fine := ok us && ok gs
    if !rootFirst c then .outside "uid-0-account-before-root-in-passwd" (!fine)
    else if fine then .holds
    else .violated (if ok us then "group-spelling" else "user-spelling")
  shrink := Minimize.shrinks
  describe := fun c => showCase c ++ "\n  passwd order: " ++ ", ".intercalate (c.db.users.map (·.name))

end Differential.Props
