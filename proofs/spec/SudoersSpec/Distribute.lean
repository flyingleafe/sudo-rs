import SudoersSpec.Ast

/-!
# Distribution of runas specs and tags along a `Cmnd_Spec_List`

`distributeTags` is `mod.rs` `distribute_tags`, an `Iterator::scan` written as structural
recursion with the scan state as arguments (form (b)). `distributeTagsSpec` describes every
entry by the prefix of the list ending at it (form (a)): the runas spec in effect is the most
recent explicit one, the tag is the default tag updated by every modifier seen so far, and a
literal `ALL` additionally gets the implicit `SETENV` unless `NOSETENV` is in effect.
-/

namespace SudoersSpec

/-- One `Cmnd_Spec` after distribution: the runas spec in effect, the accumulated tag, and the
command spec (`mod.rs` `MatchedCommand`). -/
abbrev MatchedCommand := Option RunAs × (Tag × Spec Command)

/-- Apply a list of modifiers in order. -/
def applyMods (mods : List Modifier) (t : Tag) : Tag :=
  mods.foldl (fun t f => f.apply t) t

/-- "ALL" has an implicit "SETENV" that doesn't distribute (`mod.rs` lines 542-549). -/
def implicitSetenv (cmd : Spec Command) (tag : Tag) : Tag :=
  match cmd with
  | .allow .all => if tag.env = .nosetenv then tag else { tag with env := .setenv }
  | _ => tag

/-- The body of the `scan` closure, with its state `(last_runas, tag)` as arguments. -/
def distributeTagsGo : Option RunAs → Tag → List (Option RunAs × CommandSpec) →
    List MatchedCommand
  | _, _, [] => []
  | lastRunas, tag, (runas, ⟨mods, cmd⟩) :: rest =>
    let lastRunas := runas.or lastRunas
    let tag := applyMods mods tag
    (lastRunas, (implicitSetenv cmd tag, cmd)) :: distributeTagsGo lastRunas tag rest

/-- `mod.rs` `distribute_tags`. -/
def distributeTags (runasCmds : List (Option RunAs × CommandSpec)) : List MatchedCommand :=
  distributeTagsGo none {} runasCmds

/-- The runas spec in effect after a prefix of the line: the most recent explicit one. -/
def runasInEffect (pre : List (Option RunAs × CommandSpec)) : Option RunAs :=
  (pre.filterMap (·.1)).getLast?

/-- The tag in effect after a prefix of the line: every modifier seen so far, in order. -/
def tagInEffect (pre : List (Option RunAs × CommandSpec)) : Tag :=
  applyMods (pre.flatMap (·.2.mods)) {}

/-- Declarative `distribute_tags`: entry `i` is determined by the prefix ending at `i`. -/
def distributeTagsSpec (l : List (Option RunAs × CommandSpec)) : List MatchedCommand :=
  l.mapIdx fun i e =>
    let pre := l.take (i + 1)
    (runasInEffect pre, (implicitSetenv e.2.cmd (tagInEffect pre), e.2.cmd))

theorem runasInEffect_cons (e : Option RunAs × CommandSpec) (pre : List _) :
    runasInEffect (e :: pre) = (runasInEffect pre).or e.1 := by
  obtain ⟨r, c⟩ := e
  cases r <;> simp [runasInEffect, List.getLast?_cons] <;>
    cases (pre.filterMap (·.1)).getLast? <;> rfl

theorem applyMods_append (a b : List Modifier) (t : Tag) :
    applyMods (a ++ b) t = applyMods b (applyMods a t) := by
  simp [applyMods, List.foldl_append]

theorem distributeTagsGo_eq (r₀ : Option RunAs) (t₀ : Tag) (l : List (Option RunAs × CommandSpec)) :
    distributeTagsGo r₀ t₀ l =
      l.mapIdx fun i e =>
        let pre := l.take (i + 1)
        ((runasInEffect pre).or r₀,
          (implicitSetenv e.2.cmd (applyMods (pre.flatMap (·.2.mods)) t₀), e.2.cmd)) := by
  induction l generalizing r₀ t₀ with
  | nil => rfl
  | cons e l ih =>
    obtain ⟨r, ⟨mods, cmd⟩⟩ := e
    rw [distributeTagsGo, List.mapIdx_cons, ih]
    simp only [List.take_succ_cons, List.take_zero, runasInEffect_cons, List.flatMap_cons,
      applyMods_append, Option.or_assoc]
    rfl

/-- **(a) = (b)** for `distribute_tags`. -/
theorem distributeTags_eq_spec (l : List (Option RunAs × CommandSpec)) :
    distributeTags l = distributeTagsSpec l := by
  rw [distributeTags, distributeTagsGo_eq, distributeTagsSpec]
  congr 1
  funext i e
  simp only [Option.or_none]
  rfl

/-- Every literal `ALL` entry carries `SETENV` (implicitly) or `NOSETENV` (explicitly). -/
theorem distributeTagsSpec_allow_all_env (l : List (Option RunAs × CommandSpec))
    (e : MatchedCommand) (he : e ∈ distributeTagsSpec l) (hall : e.2.2 = .allow .all) :
    e.2.1.env = .setenv ∨ e.2.1.env = .nosetenv := by
  simp only [distributeTagsSpec, List.mem_mapIdx] at he
  obtain ⟨i, hi, rfl⟩ := he
  simp only at hall ⊢
  rw [hall, implicitSetenv]
  split <;> simp_all

end SudoersSpec
