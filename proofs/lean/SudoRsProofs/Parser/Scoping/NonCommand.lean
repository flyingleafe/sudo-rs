import SudoRsProofs.Parser.Analysis.Abs
import SudoRsProofs.Parser.Scoping.Modifiers
import SudoRsProofs.Matchers

/-!
# The first Defaults pass: `specify_host_user_runas`

`src/sudoers/mod.rs`: `specify_host_user_runas` takes the non-command customisers out of the
policy (`mem::replace` with an empty vector, so they are single-use), builds the host, invoking
user and (if requested) target user matchers and alias verdicts, and folds the matching
customisers' modifiers over `settings` with `apply_settings`. It leaves the command customisers,
the rules and the alias tables unchanged.

The reference is `SudoersSpec.Analysis.nonCommandModifiers`: Generic always matches, Host/User
test the corresponding matcher against the signed alias verdicts, RunAs needs a target user (and
tests no group). Every list uses `findItem`; the loop consumes the entries in file order.
-/

open Aeneas Aeneas.Std Result
open sudo_rs sudo_rs.sudoers
open SudoersSpec.Analysis (NonCommandScope nonCommandModifiers applyModifiers)

namespace SudoRsProofs.Parser.Scoping

set_option allowUnsafeReducibility true in
attribute [local reducible] alloc.vec.into_iter.IntoIter

local notation "matchUserFn" uInst =>
  sudo_rs.sudoers.match_user.closure.Insts.CoreOpsFunctionFnTupleShared1UserSpecifierBool uInst
local notation "matchTokenFn" =>
  sudo_rs.sudoers.match_token.closure.Insts.CoreOpsFunctionFnTupleShared1TBool
    sudo_rs.sudoers.tokens.Hostname.Insts.CoreOpsDerefDerefString

variable {U G UG : Type} {uInst : sudo_rs.system.interface.UnixUser U UG}
  {eqInst : core.cmp.PartialEq U U} {gInst : sudo_rs.system.interface.UnixGroup G}
  {O : SudoersSpec.Oracle U G}

/-! ## Well-formedness of the customiser table -/

/-- Every scope list of the first pass has names that fit and matcher domains where the closure
is pure and total. -/
def NonCommandScopeFits : ast.ConfigScope → Prop
  | .Host xs => ItemsFit xs.val ∧ ItemsGood Fits xs.val
  | .User xs => ItemsFit xs.val ∧ ItemsGood UserSpecFits xs.val
  | .RunAs xs => ItemsFit xs.val ∧ ItemsGood UserSpecFits xs.val
  | _ => True

/-- Entries of the first pass: no command scope (such an entry would panic), fit lists, and
modifiers produced by the Defaults constructors (so the authorization ranges survive). -/
def NonCommandEntriesOK (entries : List (ast.ConfigScope × alloc.vec.Vec defaults.SettingsModifier)) :
    Prop :=
  (∀ e ∈ entries, (Analysis.absNonCommandScope e.1).isSome) ∧
  (∀ e ∈ entries, NonCommandScopeFits e.1) ∧
  (∀ e ∈ entries, ∀ m ∈ e.2.val, Defaults.Produced m)

/-! ## The reference fold, one entry at a time -/

/-- The reference `keep` test of `nonCommandModifiers`, named so a step can be stated. -/
def nonCommandKeep (aliases : SudoersSpec.AliasTable) (host : SudoersSpec.Hostname)
    (invoker : U) (target : Option U) : NonCommandScope → Bool
  | .generic => true
  | .host xs =>
    (SudoersSpec.findItem (SudoersSpec.matchHost O host)
      (SudoersSpec.getAliases aliases.host (SudoersSpec.matchHost O host))
      (SudoersSpec.withUnit xs)).isSome
  | .user xs =>
    (SudoersSpec.findItem (SudoersSpec.matchUser O invoker)
      (SudoersSpec.getAliases aliases.user (SudoersSpec.matchUser O invoker))
      (SudoersSpec.withUnit xs)).isSome
  | .runAs xs =>
    match target with
    | some u =>
      (SudoersSpec.findItem (SudoersSpec.matchUser O u)
        (SudoersSpec.getAliases aliases.runas (SudoersSpec.matchUser O u))
        (SudoersSpec.withUnit xs)).isSome
    | none => false

theorem nonCommandModifiers_cons (aliases : SudoersSpec.AliasTable)
    (host : SudoersSpec.Hostname) (invoker : U) (target : Option U)
    (scope : NonCommandScope) (mods : List SudoersSpec.Settings.SettingsModifier)
    (rest : List (NonCommandScope × List SudoersSpec.Settings.SettingsModifier)) :
    nonCommandModifiers O aliases host invoker target ((scope, mods) :: rest) =
      (if nonCommandKeep (O := O) aliases host invoker target scope then mods else []) ++
        nonCommandModifiers O aliases host invoker target rest := by
  simp only [nonCommandModifiers, nonCommandKeep, List.flatMap_cons]
  cases target <;> rfl

theorem absNonCommand_cons (scope : ast.ConfigScope)
    (mods : alloc.vec.Vec defaults.SettingsModifier)
    (rest : alloc.vec.Vec (ast.ConfigScope × alloc.vec.Vec defaults.SettingsModifier))
    (h : ((scope, mods) :: rest.val).length ≤ Usize.max) :
    Analysis.absNonCommand (alloc.vec.Vec.from ((scope, mods) :: rest.val) h) =
      match Analysis.absNonCommandScope scope with
      | none => Analysis.absNonCommand rest
      | some s => (s, mods.val.map Defaults.absModifier) :: Analysis.absNonCommand rest := by
  simp only [Analysis.absNonCommand, alloc.vec.Vec.from_val, List.filterMap_cons]
  cases Analysis.absNonCommandScope scope <;> simp_all

/-! ## The loop -/

@[simp] theorem specify_host_user_runas_loop_false
    (settings : defaults.Settings) (text : Str) (host_aliases : FoundAliases) (t : U)
    (user_aliases : FoundAliases)
    (runas : Option (sudoers.match_user.closure U UG × FoundAliases))
    (customisers : alloc.vec.into_iter.IntoIter (ast.ConfigScope ×
      alloc.vec.Vec defaults.SettingsModifier)) :
    sudoers.Sudoers.specify_host_user_runas_loop uInst settings text host_aliases t
      user_aliases runas customisers false = ok settings := by
  rw [sudoers.Sudoers.specify_host_user_runas_loop]
  simp

/-- The `true` run of the first pass, by induction on the entries. The hypotheses fix the two
matcher closures (`text` for the host, `userClosure`/runas closure for the users), their alias
verdicts, and the target user; the conclusion is the reference fold of the matching entries. -/
theorem specify_host_user_runas_loop_eq
    (hO : InstOracle uInst eqInst gInst O) (hH : O.SudoRsHosts)
    (entries : List (ast.ConfigScope × alloc.vec.Vec defaults.SettingsModifier)) :
    ∀ (settings : defaults.Settings) (text : Str) (host : String)
      (htext : text.val = sudo_rs.stringBytes host)
      (amUser : U)
      (hostAliases userAliases : FoundAliases) (aliases : SudoersSpec.AliasTable)
      (hhostA : absFound hostAliases = SudoersSpec.getAliases aliases.host (SudoersSpec.matchHost O host))
      (huserA : absFound userAliases = SudoersSpec.getAliases aliases.user (SudoersSpec.matchUser O amUser))
      (target : Option U) (runas : Option (sudoers.match_user.closure U UG × FoundAliases))
      (hrunas_none : target = none → runas = none)
      (hrunas_some : ∀ u, target = some u → ∃ names, runas = some (u, names) ∧
        absFound names = SudoersSpec.getAliases aliases.runas (SudoersSpec.matchUser O u))
      (hhfit : FoundFits hostAliases) (hufit : FoundFits userAliases)
      (hrfit : ∀ c names, runas = some (c, names) → FoundFits names)
      (it : alloc.vec.into_iter.IntoIter (ast.ConfigScope ×
        alloc.vec.Vec defaults.SettingsModifier)) (h : it.val = entries)
      (hok : NonCommandEntriesOK entries) (hs : SettingsInRange settings),
      ∃ s', sudoers.Sudoers.specify_host_user_runas_loop uInst settings text hostAliases amUser
          userAliases runas it true = ok s' ∧
        Defaults.absSettings s' = applyModifiers
          (nonCommandModifiers O aliases host amUser target (Analysis.absNonCommand it))
          (Defaults.absSettings settings) ∧
        SettingsInRange s' := by
  induction entries with
  | nil =>
    intro settings text host htext amUser hostAliases userAliases aliases
      hhostA huserA target runas hrn hrs hhfit hufit hrfit it h hok hs
    have hstep : sudoers.Sudoers.specify_host_user_runas_loop uInst settings text hostAliases
        amUser userAliases runas it true = ok settings := by
      rw [sudoers.Sudoers.specify_host_user_runas_loop]
      simp [Defaults.next_nil it h]
    refine ⟨settings, hstep, ?_, hs⟩
    simp [Analysis.absNonCommand, nonCommandModifiers, h]
  | cons e entries ih =>
    intro settings text host htext amUser hostAliases userAliases aliases
      hhostA huserA target runas hrn hrs hhfit hufit hrfit it h hok hs
    rcases e with ⟨scope, mods⟩
    obtain ⟨it', hit', hnext⟩ := Defaults.next_cons it (scope, mods) entries h
    have hlen : ((scope, mods) :: it'.val).length ≤ Usize.max := by
      have hp := alloc.vec.Vec.property it
      rw [h, ← hit'] at hp
      simpa using hp
    have hit : it = alloc.vec.Vec.from ((scope, mods) :: it'.val) hlen := by
      apply alloc.vec.Vec.ext
      simp [alloc.vec.Vec.from_val, h, hit']
    have hnonOnly : (Analysis.absNonCommandScope scope).isSome := hok.1 (scope, mods) (by simp)
    have hfit : NonCommandScopeFits scope := hok.2.1 (scope, mods) (by simp)
    have hmods : ∀ m ∈ mods.val, Defaults.Produced m :=
      fun m hm => hok.2.2 (scope, mods) (by simp) m hm
    have hok' : NonCommandEntriesOK entries :=
      ⟨fun x hx => hok.1 x (List.mem_cons_of_mem _ hx),
       fun x hx => hok.2.1 x (List.mem_cons_of_mem _ hx),
       fun x hx m hm => hok.2.2 x (List.mem_cons_of_mem _ hx) m hm⟩
    cases scope with
    | Generic =>
      obtain ⟨s1, happly, habs1, hrange1⟩ := apply_settings_eq mods settings hs hmods
      have hstep : sudoers.Sudoers.specify_host_user_runas_loop uInst settings text hostAliases
          amUser userAliases runas it true =
          sudoers.Sudoers.specify_host_user_runas_loop uInst s1 text hostAliases amUser
            userAliases runas it' true := by
        rw [sudoers.Sudoers.specify_host_user_runas_loop]
        simp only [ite_true]
        simp [hnext, happly]
      obtain ⟨s', hloop, habs', hrange'⟩ := ih s1 text host htext amUser
        hostAliases userAliases aliases hhostA huserA target runas hrn hrs hhfit hufit hrfit
        it' hit' hok' hrange1
      refine ⟨s', by rw [hstep]; exact hloop, ?_, hrange'⟩
      rw [habs', habs1, hit, absNonCommand_cons]
      simp only [Analysis.absNonCommandScope]
      rw [nonCommandModifiers_cons]
      simp [nonCommandKeep, applyModifiers_append]
    | Host xs =>
      have hx : ItemsFit xs.val ∧ ItemsGood Fits xs.val := hfit
      obtain ⟨matched, hmatch, hfind⟩ :
          ∃ b, sudoers.find_item (matchTokenFn) (alloc.vec.Vec.deref xs) text hostAliases = ok b ∧
            b = (SudoersSpec.findItem (SudoersSpec.matchHost O host) (absFound hostAliases)
              (SudoersSpec.withUnit (absSpecList id xs.val))).isSome := by
        obtain ⟨b, hb, hb'⟩ := exists_eq_ok_of_spec
          (find_item_match_token_spec hH host text htext (alloc.vec.Vec.deref xs)
            hostAliases hhfit (by simpa using hx.1) (by simpa using hx.2))
        exact ⟨b, by simpa using hb, by simpa [SudoRsProofs.Vec.deref_val] using hb'⟩
      have hfind' : (SudoersSpec.findItem (SudoersSpec.matchHost O host)
          (SudoersSpec.getAliases aliases.host (SudoersSpec.matchHost O host))
          (SudoersSpec.withUnit (absSpecList id xs.val))).isSome = matched := by
        rw [← hhostA]
        exact hfind.symm
      cases hm : matched with
      | false =>
        have hstep : sudoers.Sudoers.specify_host_user_runas_loop uInst settings text hostAliases
            amUser userAliases runas it true =
            sudoers.Sudoers.specify_host_user_runas_loop uInst settings text hostAliases amUser
              userAliases runas it' true := by
          rw [sudoers.Sudoers.specify_host_user_runas_loop]
          simp only [ite_true]
          simp [hnext, hm, hmatch]
        obtain ⟨s', hloop, habs', hrange'⟩ := ih settings text host htext amUser
          hostAliases userAliases aliases hhostA huserA target runas hrn hrs hhfit hufit hrfit
          it' hit' hok' hs
        refine ⟨s', by rw [hstep]; exact hloop, ?_, hrange'⟩
        rw [habs', hit, absNonCommand_cons]
        simp only [Analysis.absNonCommandScope]
        rw [nonCommandModifiers_cons]
        simp [nonCommandKeep, hfind', hm, applyModifiers_append]
      | true =>
        obtain ⟨s1, happly, habs1, hrange1⟩ := apply_settings_eq mods settings hs hmods
        have hstep : sudoers.Sudoers.specify_host_user_runas_loop uInst settings text hostAliases
            amUser userAliases runas it true =
            sudoers.Sudoers.specify_host_user_runas_loop uInst s1 text hostAliases amUser
              userAliases runas it' true := by
          rw [sudoers.Sudoers.specify_host_user_runas_loop]
          simp only [ite_true]
          simp [hnext, hm, hmatch, happly]
        obtain ⟨s', hloop, habs', hrange'⟩ := ih s1 text host htext amUser
          hostAliases userAliases aliases hhostA huserA target runas hrn hrs hhfit hufit hrfit
          it' hit' hok' hrange1
        refine ⟨s', by rw [hstep]; exact hloop, ?_, hrange'⟩
        rw [habs', habs1, hit, absNonCommand_cons]
        simp only [Analysis.absNonCommandScope]
        rw [nonCommandModifiers_cons]
        simp [nonCommandKeep, hfind', hm, applyModifiers_append]
    | User xs =>
      have hx : ItemsFit xs.val ∧ ItemsGood UserSpecFits xs.val := hfit
      obtain ⟨matched, hmatch, hfind⟩ :
          ∃ b, sudoers.find_item (matchUserFn uInst) (alloc.vec.Vec.deref xs) amUser userAliases =
            ok b ∧ b = (SudoersSpec.findItem (SudoersSpec.matchUser O amUser)
              (absFound userAliases)
              (SudoersSpec.withUnit (absSpecList absUserSpecifier xs.val))).isSome := by
        obtain ⟨b, hb, hb'⟩ := exists_eq_ok_of_spec
          (find_item_match_user_spec hO amUser (alloc.vec.Vec.deref xs) userAliases hufit
            (by simpa using hx.1) (by simpa using hx.2))
        exact ⟨b, by simpa using hb, by simpa [SudoRsProofs.Vec.deref_val] using hb'⟩
      have hfind' : (SudoersSpec.findItem (SudoersSpec.matchUser O amUser)
          (SudoersSpec.getAliases aliases.user (SudoersSpec.matchUser O amUser))
          (SudoersSpec.withUnit (absSpecList absUserSpecifier xs.val))).isSome = matched := by
        rw [← huserA]
        exact hfind.symm
      cases hm : matched with
      | false =>
        have hstep : sudoers.Sudoers.specify_host_user_runas_loop uInst settings text hostAliases
            amUser userAliases runas it true =
            sudoers.Sudoers.specify_host_user_runas_loop uInst settings text hostAliases amUser
              userAliases runas it' true := by
          rw [sudoers.Sudoers.specify_host_user_runas_loop]
          simp only [ite_true]
          simp [hnext, hm, hmatch]
        obtain ⟨s', hloop, habs', hrange'⟩ := ih settings text host htext amUser
          hostAliases userAliases aliases hhostA huserA target runas hrn hrs hhfit hufit hrfit
          it' hit' hok' hs
        refine ⟨s', by rw [hstep]; exact hloop, ?_, hrange'⟩
        rw [habs', hit, absNonCommand_cons]
        simp only [Analysis.absNonCommandScope]
        rw [nonCommandModifiers_cons]
        simp [nonCommandKeep, hfind', hm, applyModifiers_append]
      | true =>
        obtain ⟨s1, happly, habs1, hrange1⟩ := apply_settings_eq mods settings hs hmods
        have hstep : sudoers.Sudoers.specify_host_user_runas_loop uInst settings text hostAliases
            amUser userAliases runas it true =
            sudoers.Sudoers.specify_host_user_runas_loop uInst s1 text hostAliases amUser
              userAliases runas it' true := by
          rw [sudoers.Sudoers.specify_host_user_runas_loop]
          simp only [ite_true]
          simp [hnext, hm, hmatch, happly]
        obtain ⟨s', hloop, habs', hrange'⟩ := ih s1 text host htext amUser
          hostAliases userAliases aliases hhostA huserA target runas hrn hrs hhfit hufit hrfit
          it' hit' hok' hrange1
        refine ⟨s', by rw [hstep]; exact hloop, ?_, hrange'⟩
        rw [habs', habs1, hit, absNonCommand_cons]
        simp only [Analysis.absNonCommandScope]
        rw [nonCommandModifiers_cons]
        simp [nonCommandKeep, hfind', hm, applyModifiers_append]
    | RunAs xs =>
      have hx : ItemsFit xs.val ∧ ItemsGood UserSpecFits xs.val := hfit
      cases ht : target with
      | none =>
        have hrnone : runas = none := hrn ht
        have hstep : sudoers.Sudoers.specify_host_user_runas_loop uInst settings text hostAliases
            amUser userAliases runas it true =
            sudoers.Sudoers.specify_host_user_runas_loop uInst settings text hostAliases amUser
              userAliases runas it' true := by
          rw [sudoers.Sudoers.specify_host_user_runas_loop]
          simp only [ite_true]
          simp [hnext, ht, hrnone]
        obtain ⟨s', hloop, habs', hrange'⟩ := ih settings text host htext amUser
          hostAliases userAliases aliases hhostA huserA target runas hrn hrs hhfit hufit hrfit
          it' hit' hok' hs
        refine ⟨s', by rw [hstep]; exact hloop, ?_, hrange'⟩
        rw [habs', hit, absNonCommand_cons]
        simp only [Analysis.absNonCommandScope]
        rw [nonCommandModifiers_cons]
        simp [nonCommandKeep, ht, applyModifiers_append]
      | some u =>
        obtain ⟨names, hrunas, hnamesA⟩ := hrs u ht
        have hnamesFit : FoundFits names := hrfit u names hrunas
        obtain ⟨matched, hmatch, hfind⟩ :
            ∃ b, sudoers.find_item (matchUserFn uInst) (alloc.vec.Vec.deref xs) u names = ok b ∧
              b = (SudoersSpec.findItem (SudoersSpec.matchUser O u) (absFound names)
                (SudoersSpec.withUnit (absSpecList absUserSpecifier xs.val))).isSome := by
          obtain ⟨b, hb, hb'⟩ := exists_eq_ok_of_spec
            (find_item_match_user_spec hO u (alloc.vec.Vec.deref xs) names hnamesFit
              (by simpa using hx.1) (by simpa using hx.2))
          exact ⟨b, by simpa using hb, by simpa [SudoRsProofs.Vec.deref_val] using hb'⟩
        have hfind' : (SudoersSpec.findItem (SudoersSpec.matchUser O u)
            (SudoersSpec.getAliases aliases.runas (SudoersSpec.matchUser O u))
            (SudoersSpec.withUnit (absSpecList absUserSpecifier xs.val))).isSome = matched := by
          rw [← hnamesA]
          exact hfind.symm
        cases hm : matched with
        | false =>
          have hstep : sudoers.Sudoers.specify_host_user_runas_loop uInst settings text hostAliases
              amUser userAliases runas it true =
              sudoers.Sudoers.specify_host_user_runas_loop uInst settings text hostAliases amUser
                userAliases runas it' true := by
            rw [sudoers.Sudoers.specify_host_user_runas_loop]
            simp only [ite_true]
            simp [hnext, ht, hrunas, hm, hmatch]
          obtain ⟨s', hloop, habs', hrange'⟩ := ih settings text host htext amUser
            hostAliases userAliases aliases hhostA huserA target runas hrn hrs hhfit hufit hrfit
            it' hit' hok' hs
          refine ⟨s', by rw [hstep]; exact hloop, ?_, hrange'⟩
          rw [habs', hit, absNonCommand_cons]
          simp only [Analysis.absNonCommandScope]
          rw [nonCommandModifiers_cons]
          simp [nonCommandKeep, ht, hfind', hm, applyModifiers_append]
        | true =>
          obtain ⟨s1, happly, habs1, hrange1⟩ := apply_settings_eq mods settings hs hmods
          have hstep : sudoers.Sudoers.specify_host_user_runas_loop uInst settings text hostAliases
              amUser userAliases runas it true =
              sudoers.Sudoers.specify_host_user_runas_loop uInst s1 text hostAliases amUser
                userAliases runas it' true := by
            rw [sudoers.Sudoers.specify_host_user_runas_loop]
            simp only [ite_true]
            simp [hnext, ht, hrunas, hm, hmatch, happly]
          obtain ⟨s', hloop, habs', hrange'⟩ := ih s1 text host htext amUser
            hostAliases userAliases aliases hhostA huserA target runas hrn hrs hhfit hufit hrfit
            it' hit' hok' hrange1
          refine ⟨s', by rw [hstep]; exact hloop, ?_, hrange'⟩
          rw [habs', habs1, hit, absNonCommand_cons]
          simp only [Analysis.absNonCommandScope]
          rw [nonCommandModifiers_cons]
          simp [nonCommandKeep, ht, hfind', hm, applyModifiers_append]
    | Command xs =>
      exact absurd hnonOnly (by simp [Analysis.absNonCommandScope])

end SudoRsProofs.Parser.Scoping
