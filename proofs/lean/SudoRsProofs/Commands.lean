import SudoRsProofs.Tags

/-!
# `command_verdict` and `check_commands`

`check_commands(result, runas_cmds, verdict)` distributes the tags of one `Cmnd_Spec_List` and
folds over its entries: the verdict closure decides, per entry, whether the entry takes part
(`Some`) and with which judgement. The closure is generic here (`V` at the spec level); the
`check_permission` closure is instantiated in `Permission.lean`.
-/

open Aeneas Aeneas.Std Result

namespace SudoRsProofs

/-- A spec-level verdict: given the runas spec in effect and the command spec of an entry,
`some true` (grant), `some false` (deny) or `none` (does not take part). -/
abbrev SpecVerdict := Option SudoersSpec.RunAs → SudoersSpec.Spec SudoersSpec.Command → Option Bool

/-- One iteration of `check_commands`. -/
def commandsStep (V : SpecVerdict) (r : Option SudoersSpec.Tag) (e : SudoersSpec.MatchedCommand) :
    Option SudoersSpec.Tag :=
  match V e.1 e.2.2 with
  | none => r
  | some true => some e.2.1
  | some false => none

/-- `check_commands` at the spec level, on the distributed entries of a line. -/
def checkCommandsSpec (V : SpecVerdict) (es : List SudoersSpec.MatchedCommand)
    (r : Option SudoersSpec.Tag) : Option SudoersSpec.Tag :=
  es.foldl (commandsStep V) r

variable {Verdict : Type _}

/-- **`command_verdict`**: the verdict closure applied to the runas spec at position
`last_runas` (if any) and the command of entry `i`. -/
@[step]
theorem command_verdict_spec
    (inst : core.ops.function.Fn Verdict (Option sudo_rs.sudoers.ast.RunAs × RSpec RCommand)
      (Option Bool)) (verdict : Verdict)
    (fr : sudo_rs.sudoers.ast.RunAs → SudoersSpec.RunAs) (fc : RCommand → SudoersSpec.Command)
    (V : SpecVerdict) (GoodR : sudo_rs.sudoers.ast.RunAs → Prop) (GoodC : RSpec RCommand → Prop)
    (hv : ∀ ra cmd, (∀ r, ra = some r → GoodR r) → GoodC cmd →
      inst.call verdict (ra, cmd) = ok (V (ra.map fr) (absSpec fc cmd)))
    (l : Slice REntry) (hl : ∀ e ∈ l.val, (∀ r, e.1 = some r → GoodR r) ∧ GoodC (csCmd e.2))
    (i : Usize) (hi : i.val < l.val.length) (lr : Option Usize)
    (hlr : ∀ j, lr = some j → j.val < l.val.length) :
    sudo_rs.sudoers.command_verdict inst l i lr verdict
      ⦃ o => o = V (resolveRunas fr l.val lr) (absSpec fc (csCmd l.val[i.val].2)) ⦄ := by
  unfold sudo_rs.sudoers.command_verdict
  have hgi := hl _ (List.getElem_mem hi)
  -- the runas spec in effect
  apply WP.spec_bind (Pₘ := fun ra => ra = lr.bind (fun j => (l.val[j.val]?).bind (·.1)))
  · cases lr with
    | none => simp
    | some j =>
      have hj := hlr j rfl
      dsimp only
      apply WP.spec_bind (Slice.index_usize_spec l j hj)
      rintro ⟨o, cs⟩ ho
      simp only [uncurry, core.option.Option.as_ref, WP.spec_ok]
      simp [List.getElem?_eq_getElem hj, ← ho]
  intro ra hra'
  apply WP.spec_bind (Slice.index_usize_spec l i hi)
  rintro ⟨o, ⟨mods, cmd⟩⟩ hq
  simp only [uncurry]
  have hgr : ∀ r, ra = some r → GoodR r := by
    intro r hr
    rw [hra'] at hr
    obtain ⟨j, hj, hjr⟩ := Option.bind_eq_some_iff.mp hr
    obtain ⟨e, he, her⟩ := Option.bind_eq_some_iff.mp hjr
    exact (hl e (List.mem_of_getElem? he)).1 r her
  have hgc : GoodC cmd := by
    have := hgi.2
    rw [← hq] at this
    exact this
  rw [hv ra cmd hgr hgc, WP.spec_ok, resolveRunas, ← hra', ← hq]
  rfl

theorem check_commands_loop_spec
    (inst : core.ops.function.Fn Verdict (Option sudo_rs.sudoers.ast.RunAs × RSpec RCommand)
      (Option Bool)) (verdict : Verdict)
    (fr : sudo_rs.sudoers.ast.RunAs → SudoersSpec.RunAs) (fc : RCommand → SudoersSpec.Command)
    (V : SpecVerdict) (GoodR : sudo_rs.sudoers.ast.RunAs → Prop) (GoodC : RSpec RCommand → Prop)
    (hv : ∀ ra cmd, (∀ r, ra = some r → GoodR r) → GoodC cmd →
      inst.call verdict (ra, cmd) = ok (V (ra.map fr) (absSpec fc cmd)))
    (l : Slice REntry) (hl : ∀ e ∈ l.val, (∀ r, e.1 = some r → GoodR r) ∧ GoodC (csCmd e.2))
    (tags : alloc.vec.Vec (Option Usize × sudo_rs.sudoers.ast.Tag))
    (hlen : tags.val.length = l.val.length)
    (hpos : ∀ k (hk : k < tags.val.length), ∀ j, (tags.val[k]).1 = some j → j.val < l.val.length)
    (result : Option sudo_rs.sudoers.ast.Tag) (i : Usize) :
    sudo_rs.sudoers.check_commands_loop inst result l verdict tags i ⦃ r =>
      r.map absTag = checkCommandsSpec V
        (List.zipWith (resolveEntry fr fc l.val) (l.val.drop i.val) (tags.val.drop i.val))
        (result.map absTag) ⦄ := by
  unfold sudo_rs.sudoers.check_commands_loop
  dsimp only
  split
  · have hlt : i.val < tags.val.length := by scalar_tac
    have hlt' : i.val < l.val.length := by omega
    simp only [alloc.vec.Vec.index_slice_index]
    apply WP.spec_bind (alloc.vec.Vec.index_usize_spec tags i hlt)
    rintro ⟨lr, tag⟩ hq
    simp only [uncurry]
    have hlr : ∀ j, lr = some j → j.val < l.val.length := by
      intro j hj
      exact hpos i.val hlt j (by rw [← hq]; exact hj)
    step with command_verdict_spec inst verdict fr fc V GoodR GoodC hv l hl i hlt' lr hlr
      as ⟨o, ho⟩
    have hstep : ∀ r1 : Option sudo_rs.sudoers.ast.Tag,
        r1.map absTag = commandsStep V (result.map absTag)
          (resolveEntry fr fc l.val l.val[i.val] (lr, tag)) →
        (do
          let i2 ← i + 1#usize
          sudo_rs.sudoers.check_commands_loop inst r1 l verdict tags i2) ⦃ r =>
        r.map absTag = checkCommandsSpec V
          (List.zipWith (resolveEntry fr fc l.val) (l.val.drop i.val) (tags.val.drop i.val))
          (result.map absTag) ⦄ := by
      intro r1 hr1
      step as ⟨i2, hi2⟩
      step with check_commands_loop_spec inst verdict fr fc V GoodR GoodC hv l hl tags hlen hpos
        r1 i2 as ⟨r, hr⟩
      rw [hr, hi2, List.drop_eq_getElem_cons hlt', List.drop_eq_getElem_cons hlt, ← hq,
        List.zipWith_cons_cons]
      simp only [checkCommandsSpec, List.foldl_cons]
      rw [← hr1]
    rcases o with _ | _ | _
    · simp only [Aeneas.Std.bind_ok]
      exact hstep result (by simp only [commandsStep, resolveEntry, ← ho])
    · simp only [Bool.false_eq_true, ite_false, Aeneas.Std.bind_ok]
      exact hstep none (by simp only [commandsStep, resolveEntry, ← ho]; rfl)
    · simp only [ite_true]
      step as ⟨t, ht⟩
      exact hstep (some t) (by simp only [commandsStep, resolveEntry, ← ho, ht]; rfl)
  · have : tags.val.length ≤ i.val := by scalar_tac
    simp [List.drop_eq_nil_of_le this, checkCommandsSpec]
termination_by tags.val.length - i.val
decreasing_by all_goals scalar_decr_tac

/-- **`check_commands` folds the verdict over the distributed entries** of the line: with the
closure behaving as the spec verdict `V` on good runas specs and commands, the result is
`checkCommandsSpec V (SudoersSpec.distributeTags line) result`. -/
@[step]
theorem check_commands_spec
    (inst : core.ops.function.Fn Verdict (Option sudo_rs.sudoers.ast.RunAs × RSpec RCommand)
      (Option Bool)) (verdict : Verdict)
    (fr : sudo_rs.sudoers.ast.RunAs → SudoersSpec.RunAs) (fc : RCommand → SudoersSpec.Command)
    (V : SpecVerdict) (GoodR : sudo_rs.sudoers.ast.RunAs → Prop) (GoodC : RSpec RCommand → Prop)
    (hv : ∀ ra cmd, (∀ r, ra = some r → GoodR r) → GoodC cmd →
      inst.call verdict (ra, cmd) = ok (V (ra.map fr) (absSpec fc cmd)))
    (l : Slice REntry) (hl : ∀ e ∈ l.val, (∀ r, e.1 = some r → GoodR r) ∧ GoodC (csCmd e.2))
    (hwf : LineWF l.val) (hig : (lineMods l.val).length ≤ Usize.max)
    (result : Option sudo_rs.sudoers.ast.Tag) :
    sudo_rs.sudoers.check_commands inst result l verdict ⦃ r =>
      r.map absTag = checkCommandsSpec V (SudoersSpec.distributeTags (absLine fr fc l.val))
        (result.map absTag) ⦄ := by
  unfold sudo_rs.sudoers.check_commands
  step with distribute_tags_spec fr fc l hwf hig as ⟨tags, hlen, hzip, hpos⟩
  step with check_commands_loop_spec inst verdict fr fc V GoodR GoodC hv l hl tags hlen
    (fun k hk j hj => by
      obtain ⟨h1, -⟩ := hpos k hk j hj
      omega) result 0#usize as ⟨r, hr⟩
  simpa [hzip] using hr

end SudoRsProofs
