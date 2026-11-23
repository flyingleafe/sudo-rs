import SudoersSpec.Analysis.Collect

/-!
# What equality of settings means

The native environment tables are sets. The spec's list representation is not canonical:
two tables may have the same members in a different order. All other settings, and all other
parts of an authorization, continue to be compared with ordinary equality.
-/

namespace SudoersSpec.Settings

/-- Remove exactly the three set representatives, retaining every scalar and option. -/
def withoutSets (s : Settings) : Settings := { s with env_keep := [], env_check := [], env_delete := [] }

structure Equiv (s t : Settings) : Prop where
  other : withoutSets s = withoutSets t
  keep : StrSet.Equiv s.env_keep t.env_keep
  check : StrSet.Equiv s.env_check t.env_check
  delete : StrSet.Equiv s.env_delete t.env_delete

private theorem withoutSets_apply (s : Settings) (m : SettingsModifier) :
    withoutSets (m.apply s) = withoutSets (m.apply (withoutSets s)) := by cases m <;> rfl

/-- Assigning a scalar cannot observe iteration order, and a list update respects membership. -/
theorem Equiv.apply {s t : Settings} (h : Equiv s t) (m : SettingsModifier) :
    Equiv (m.apply s) (m.apply t) where
  other := (withoutSets_apply s m).trans ((congrArg (fun x => withoutSets (m.apply x)) h.other).trans
    (withoutSets_apply t m).symm)
  keep := by cases m <;> first | exact h.keep | exact applyList_equiv h.keep _
  check := by cases m <;> first | exact h.check | exact applyList_equiv h.check _
  delete := by cases m <;> first | exact h.delete | exact applyList_equiv h.delete _

theorem Equiv.applyModifiers {s t : Settings} (h : Equiv s t) (ms : List SettingsModifier) :
    Equiv (Analysis.applyModifiers ms s) (Analysis.applyModifiers ms t) := by
  induction ms generalizing s t with
  | nil => exact h
  | cons m _ ih => exact ih (h.apply m)

theorem Equiv.settingsInForce {s t : Settings} (h : Equiv s t) (O : Oracle U G)
    (aliases : AliasTable) (c : Analysis.Collected) (req : Request U G) :
    Equiv (Analysis.settingsInForce O aliases c req s) (Analysis.settingsInForce O aliases c req t) :=
  (h.applyModifiers _).applyModifiers _

/-- A set is observed only through its membership predicate. Unlike canonicalizing by
sorting, this needs neither an ordering of strings nor a no-duplicates invariant. -/
def membership (s : StrSet) : String → Prop := fun x => x ∈ s

private theorem membership_eq {a b : StrSet} (h : StrSet.Equiv a b) : membership a = membership b :=
  funext fun x => propext (h x)

/-- Preserve the authorization constructor, authentication and all scalar restrictions; only
change the representation of the native sets. -/
def observeAuthorization : Authorization StrSet → Authorization (String → Prop)
  | .forbidden => .forbidden
  | .allowed auth r => .allowed auth { r with envKeep := membership r.envKeep, envCheck := membership r.envCheck }

private def observedDefaults (s : Settings) : Defaults (String → Prop) :=
  { (withoutSets s).toDefaults with envKeep := membership s.env_keep, envCheck := membership s.env_check }

private theorem observe_eq (s : Settings) (flags : Option Tag) :
    observeAuthorization (authorization s.toDefaults flags) = authorization (observedDefaults s) flags := by
  cases flags <;> rfl

theorem authorization_congr {s t : Settings} (h : Equiv s t) (flags : Option Tag) :
    observeAuthorization (authorization s.toDefaults flags) =
      observeAuthorization (authorization t.toDefaults flags) := by
  rw [observe_eq, observe_eq]
  congr 1
  unfold observedDefaults
  rw [h.other, membership_eq h.keep, membership_eq h.check]

@[simp] theorem observeAuthorization_forbidden_iff (a : Authorization StrSet) :
    observeAuthorization a = .forbidden ↔ a = .forbidden := by cases a <;> simp [observeAuthorization]

end SudoersSpec.Settings
