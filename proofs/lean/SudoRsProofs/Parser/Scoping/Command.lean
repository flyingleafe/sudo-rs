import SudoRsProofs.Parser.Scoping.NonCommand

/-!
# The second Defaults pass: `specify_command`

`src/sudoers/mod.rs`: `specify_command` takes the command customisers out of the policy
(`mem::replace` with an empty vector), builds `match_command` for the request's path and
arguments, resolves the command aliases, and folds the matching entries' modifiers over
`settings`. It leaves the non-command customisers, the rules and the alias tables unchanged.

The reference is `SudoersSpec.Analysis.commandModifiers`: each command scope is tested with
`findItem` against the signed command alias verdicts in sanitizer order.
-/

open Aeneas Aeneas.Std Result
open sudo_rs sudo_rs.sudoers
open SudoersSpec.Analysis (commandModifiers applyModifiers)

namespace SudoRsProofs.Parser.Scoping

local notation "matchCommandFn" =>
  sudo_rs.sudoers.match_command.closure.Insts.CoreOpsFunctionFnTupleShared2PairPatternArgsBool

variable {U G UG : Type} {uInst : sudo_rs.system.interface.UnixUser U UG}
  {eqInst : core.cmp.PartialEq U U} {gInst : sudo_rs.system.interface.UnixGroup G}
  {O : SudoersSpec.Oracle U G} {A : GlobAbs}

/-- Entries of the second pass: command alias names fit, and modifiers are `Produced`. -/
def CommandEntriesOK (entries : List (alloc.vec.Vec (RSpec RCommand) ×
    alloc.vec.Vec defaults.SettingsModifier)) : Prop :=
  (∀ e ∈ entries, ItemsFit e.1.val) ∧
  (∀ e ∈ entries, ∀ m ∈ e.2.val, Defaults.Produced m)

theorem commandModifiers_cons (aliases : SudoersSpec.AliasTable) (path : String)
    (args : List String) (scope : SudoersSpec.SpecList SudoersSpec.Command)
    (mods : List SudoersSpec.Settings.SettingsModifier)
    (rest : List (SudoersSpec.SpecList SudoersSpec.Command ×
      List SudoersSpec.Settings.SettingsModifier)) :
    commandModifiers O aliases path args ((scope, mods) :: rest) =
      (if (SudoersSpec.findItem (SudoersSpec.matchCommand O path args)
          (SudoersSpec.getAliases aliases.cmnd (SudoersSpec.matchCommand O path args))
          (SudoersSpec.withUnit scope)).isSome then mods else []) ++
        commandModifiers O aliases path args rest := by
  simp only [commandModifiers, List.flatMap_cons]

theorem absCommandCustomisers_cons (scope : alloc.vec.Vec (RSpec RCommand))
    (mods : alloc.vec.Vec defaults.SettingsModifier)
    (rest : alloc.vec.Vec (alloc.vec.Vec (RSpec RCommand) ×
      alloc.vec.Vec defaults.SettingsModifier))
    (h : ((scope, mods) :: rest.val).length ≤ Usize.max) :
    Analysis.absCommandCustomisers A (alloc.vec.Vec.from ((scope, mods) :: rest.val) h) =
      (absSpecList (absCommand A) scope.val, mods.val.map Defaults.absModifier) ::
        Analysis.absCommandCustomisers A rest := by
  simp only [Analysis.absCommandCustomisers, alloc.vec.Vec.from_val, List.map_cons]

@[simp] theorem specify_command_loop_false (settings : defaults.Settings)
    (p : std.path.Path) (mo : glob.MatchOptions) (args : Slice std.ffi.os_str.OsString)
    (cmnd_aliases : FoundAliases)
    (customisers : alloc.vec.into_iter.IntoIter ((alloc.vec.Vec (RSpec RCommand)) ×
      alloc.vec.Vec defaults.SettingsModifier)) :
    sudoers.Sudoers.specify_command_loop settings p mo args cmnd_aliases customisers false =
      ok settings := by
  rw [sudoers.Sudoers.specify_command_loop]
  simp

theorem specify_command_loop_eq (hG : GlobOracle A O)
    (entries : List (alloc.vec.Vec (RSpec RCommand) × alloc.vec.Vec defaults.SettingsModifier)) :
    ∀ (settings : defaults.Settings) (p : std.path.Path) (args : Slice std.ffi.os_str.OsString)
      (cmnd_aliases : FoundAliases) (aliases : SudoersSpec.AliasTable)
      (hcmndA : absFound cmnd_aliases =
        SudoersSpec.getAliases aliases.cmnd
          (SudoersSpec.matchCommand O (A.path p) (args.val.map A.os)))
      (hfit : FoundFits cmnd_aliases)
      (it : alloc.vec.into_iter.IntoIter (alloc.vec.Vec (RSpec RCommand) ×
        alloc.vec.Vec defaults.SettingsModifier)) (h : it.val = entries)
      (hok : CommandEntriesOK entries) (hs : SettingsInRange settings),
      ∃ s', sudoers.Sudoers.specify_command_loop settings p matchCommandOptions args
          cmnd_aliases it true = ok s' ∧
        Defaults.absSettings s' = applyModifiers
          (commandModifiers O aliases (A.path p) (args.val.map A.os)
            (Analysis.absCommandCustomisers A it))
          (Defaults.absSettings settings) ∧
        SettingsInRange s' := by
  induction entries with
  | nil =>
    intro settings p args cmnd_aliases aliases hcmndA hfit it h hok hs
    have hstep : sudoers.Sudoers.specify_command_loop settings p matchCommandOptions args
        cmnd_aliases it true = ok settings := by
      rw [sudoers.Sudoers.specify_command_loop]
      simp [Defaults.next_nil it h]
    refine ⟨settings, hstep, ?_, hs⟩
    simp [Analysis.absCommandCustomisers, commandModifiers, h]
  | cons e entries ih =>
    intro settings p args cmnd_aliases aliases hcmndA hfit it h hok hs
    rcases e with ⟨scope, mods⟩
    obtain ⟨it', hit', hnext⟩ := Defaults.next_cons it (scope, mods) entries h
    have hlen : ((scope, mods) :: it'.val).length ≤ Usize.max := by
      have hp := alloc.vec.Vec.property it
      rw [h, ← hit'] at hp
      simpa using hp
    have hit : it = alloc.vec.Vec.from ((scope, mods) :: it'.val) hlen := by
      apply alloc.vec.Vec.ext
      simp [alloc.vec.Vec.from_val, h, hit']
    have hfitScope : ItemsFit scope.val := hok.1 (scope, mods) (by simp)
    have hmods : ∀ m ∈ mods.val, Defaults.Produced m :=
      fun m hm => hok.2 (scope, mods) (by simp) m hm
    have hok' : CommandEntriesOK entries :=
      ⟨fun x hx => hok.1 x (List.mem_cons_of_mem _ hx),
       fun x hx m hm => hok.2 x (List.mem_cons_of_mem _ hx) m hm⟩
    obtain ⟨matched, hmatch, hfind⟩ :
        ∃ b, sudoers.find_item (matchCommandFn) (alloc.vec.Vec.deref scope)
          (p, matchCommandOptions, args) cmnd_aliases = ok b ∧
          b = (SudoersSpec.findItem (SudoersSpec.matchCommand O (A.path p) (args.val.map A.os))
            (absFound cmnd_aliases)
            (SudoersSpec.withUnit (absSpecList (absCommand A) scope.val))).isSome := by
      obtain ⟨b, hb, hb'⟩ := exists_eq_ok_of_spec
        (find_item_match_command_spec (A := A) hG p args (alloc.vec.Vec.deref scope)
          cmnd_aliases hfit (by simpa using hfitScope))
      exact ⟨b, by simpa using hb, by simpa [SudoRsProofs.Vec.deref_val] using hb'⟩
    have hfind' : (SudoersSpec.findItem (SudoersSpec.matchCommand O (A.path p)
        (args.val.map A.os))
        (SudoersSpec.getAliases aliases.cmnd
          (SudoersSpec.matchCommand O (A.path p) (args.val.map A.os)))
        (SudoersSpec.withUnit (absSpecList (absCommand A) scope.val))).isSome = matched := by
      rw [← hcmndA]
      exact hfind.symm
    cases hm : matched with
    | false =>
      have hstep : sudoers.Sudoers.specify_command_loop settings p matchCommandOptions args
          cmnd_aliases it true =
          sudoers.Sudoers.specify_command_loop settings p matchCommandOptions args cmnd_aliases
            it' true := by
        rw [sudoers.Sudoers.specify_command_loop]
        simp only [ite_true]
        simp [hnext, hm, hmatch]
      obtain ⟨s', hloop, habs', hrange'⟩ := ih settings p args cmnd_aliases aliases hcmndA
        hfit it' hit' hok' hs
      refine ⟨s', by rw [hstep]; exact hloop, ?_, hrange'⟩
      rw [habs', hit, absCommandCustomisers_cons (A := A) scope mods it' hlen]
      rw [commandModifiers_cons]
      simp [hfind', hm, applyModifiers_append]
    | true =>
      obtain ⟨s1, happly, habs1, hrange1⟩ := apply_settings_eq mods settings hs hmods
      have hstep : sudoers.Sudoers.specify_command_loop settings p matchCommandOptions args
          cmnd_aliases it true =
          sudoers.Sudoers.specify_command_loop s1 p matchCommandOptions args cmnd_aliases
            it' true := by
        rw [sudoers.Sudoers.specify_command_loop]
        simp only [ite_true]
        simp [hnext, hm, hmatch, happly]
      obtain ⟨s', hloop, habs', hrange'⟩ := ih s1 p args cmnd_aliases aliases hcmndA hfit
        it' hit' hok' hrange1
      refine ⟨s', by rw [hstep]; exact hloop, ?_, hrange'⟩
      rw [habs', habs1, hit, absCommandCustomisers_cons (A := A) scope mods it' hlen]
      rw [commandModifiers_cons]
      simp [hfind', hm, applyModifiers_append]

end SudoRsProofs.Parser.Scoping
