import SudoRsProofs.AbsTags

/-!
# The tag layer: `Modifier::apply`, `apply_modifiers`, `command_tag`, `distribute_tags`
-/

open Aeneas Aeneas.Std Result

namespace SudoRsProofs

/-! ## Derived `Clone` / `Default` / `PartialEq` impls -/

@[step]
theorem ChDir.clone_spec (d : sudo_rs.sudoers.tokens.ChDir) :
    sudo_rs.sudoers.tokens.ChDir.Insts.CoreCloneClone.clone d ⦃ d' => d' = d ⦄ := by
  cases d <;>
    simp [sudo_rs.sudoers.tokens.ChDir.Insts.CoreCloneClone.clone,
      sudo_rs.common.path.SudoPath.Insts.CoreCloneClone.clone,
      alloc.string.String.Insts.CoreCloneClone.clone]

theorem Option.clone_eq {T : Type _} (inst : core.clone.Clone T) (h : ∀ x, inst.clone x = ok x)
    (o : Option T) : core.option.Option.Insts.CoreCloneClone.clone inst o = ok o := by
  cases o <;> simp [core.option.Option.Insts.CoreCloneClone.clone, h]

theorem Vec.clone_eq {T : Type _} (inst : core.clone.Clone T) (h : ∀ x, inst.clone x = ok x)
    (v : alloc.vec.Vec T) : alloc.vec.CloneVec.clone inst v = ok v := by
  apply eq_ok_of_spec
  unfold alloc.vec.CloneVec.clone
  apply WP.spec_bind (Slice.clone_spec (fun x _ => h x))
  intro s hs
  subst hs
  simp

@[step]
theorem Tag.clone_spec (t : sudo_rs.sudoers.ast.Tag) :
    sudo_rs.sudoers.ast.Tag.Insts.CoreCloneClone.clone t ⦃ t' => t' = t ⦄ := by
  have hcd : ∀ d, sudo_rs.sudoers.tokens.ChDir.Insts.CoreCloneClone.clone d = ok d :=
    fun d => eq_ok_of_spec (ChDir.clone_spec d)
  simp [sudo_rs.sudoers.ast.Tag.Insts.CoreCloneClone.clone,
    sudo_rs.sudoers.ast.Authenticate.Insts.CoreCloneClone.clone,
    sudo_rs.sudoers.ast.EnvironmentControl.Insts.CoreCloneClone.clone,
    sudo_rs.sudoers.ast.ExecControl.Insts.CoreCloneClone.clone,
    Option.clone_eq sudo_rs.sudoers.tokens.ChDir.Insts.CoreCloneClone hcd,
    Option.clone_eq sudo_rs.alloc.string.String.Insts.CoreCloneClone (fun _ => rfl),
    Vec.clone_eq sudo_rs.sudoers.basic_parser.Span.Insts.CoreCloneClone (fun _ => rfl)]

@[step]
theorem Tag.default_spec :
    sudo_rs.sudoers.ast.Tag.Insts.CoreDefaultDefault.default
      ⦃ t => absTag t = {} ∧ t.ignored.val = [] ⦄ := by
  simp [sudo_rs.sudoers.ast.Tag.Insts.CoreDefaultDefault.default,
    sudo_rs.sudoers.ast.Authenticate.Insts.CoreDefaultDefault.default,
    sudo_rs.sudoers.ast.EnvironmentControl.Insts.CoreDefaultDefault.default,
    sudo_rs.sudoers.ast.ExecControl.Insts.CoreDefaultDefault.default,
    core.option.Option.Insts.CoreDefaultDefault.default,
    alloc.vec.Vec.Insts.CoreDefaultDefault.default, absTag, absAuthenticate, absEnv, absExec]

@[step]
theorem EnvironmentControl.eq_spec (a b : sudo_rs.sudoers.ast.EnvironmentControl) :
    sudo_rs.sudoers.ast.EnvironmentControl.Insts.CoreCmpPartialEqEnvironmentControl.eq a b
      ⦃ r => r ↔ a = b ⦄ := by
  cases a <;> cases b <;>
    simp [sudo_rs.sudoers.ast.EnvironmentControl.Insts.CoreCmpPartialEqEnvironmentControl.eq] <;>
    decide

/-! ## `Modifier::apply`, `apply_modifiers` -/

/-- **`Modifier::apply` is `SudoersSpec.Modifier.apply`.** Only `Ignored` grows the tag's
`ignored` vector (by one), which is where the `push` can overflow. -/
@[step]
theorem Modifier.apply_spec (m : sudo_rs.sudoers.ast.Modifier) (t : sudo_rs.sudoers.ast.Tag)
    (hwf : ModifierWF m) (h : t.ignored.val.length < Usize.max) :
    sudo_rs.sudoers.ast.Modifier.apply m t ⦃ t' =>
      absTag t' = (absModifier m).apply (absTag t) ∧
      t'.ignored.val.length ≤ t.ignored.val.length + 1 ⦄ := by
  unfold sudo_rs.sudoers.ast.Modifier.apply
  cases m with
  | Authenticate a =>
    cases a <;> simp_all [ModifierWF, absModifier, SudoersSpec.Modifier.apply, absTag,
      absAuthenticate]
  | Env e =>
    cases e <;> simp_all [ModifierWF, absModifier, SudoersSpec.Modifier.apply, absTag, absEnv]
  | Exec x =>
    cases x <;> simp_all [ModifierWF, absModifier, SudoersSpec.Modifier.apply, absTag, absExec]
  | Cwd d =>
    step as ⟨d', hd'⟩
    simp [hd', absModifier, SudoersSpec.Modifier.apply, absTag]
  | AppArmorProfile p =>
    simp [alloc.string.String.Insts.CoreCloneClone.clone, absModifier,
      SudoersSpec.Modifier.apply, absTag]
  | Ignored s =>
    step as ⟨v, hv⟩
    simp [hv, absModifier, SudoersSpec.Modifier.apply, absTag]
  | NoOp => simp [absModifier, SudoersSpec.Modifier.apply]

theorem apply_modifiers_loop_spec (mods : Slice sudo_rs.sudoers.ast.Modifier)
    (t : sudo_rs.sudoers.ast.Tag) (i : Usize) (hwf : ∀ m ∈ mods.val, ModifierWF m)
    (h : t.ignored.val.length + (mods.val.length - i.val) ≤ Usize.max) :
    sudo_rs.sudoers.apply_modifiers_loop mods t i ⦃ t' =>
      absTag t' = SudoersSpec.applyMods ((mods.val.drop i.val).map absModifier) (absTag t) ∧
      t'.ignored.val.length ≤ t.ignored.val.length + (mods.val.length - i.val) ⦄ := by
  unfold sudo_rs.sudoers.apply_modifiers_loop
  dsimp only
  split
  · have hlt : i.val < mods.val.length := by scalar_tac
    have hdrop := List.drop_eq_getElem_cons hlt
    step as ⟨m, hm⟩
    have hmw : ModifierWF m := hwf m (by rw [hm]; exact List.getElem_mem hlt)
    step with Modifier.apply_spec m t hmw (by omega) as ⟨t1, ht1, hl1⟩
    step as ⟨i2, hi2⟩
    step with apply_modifiers_loop_spec mods t1 i2 hwf (by omega) as ⟨t2, ht2, hl2⟩
    refine ⟨?_, by omega⟩
    rw [ht2, ht1, hdrop, hi2, List.map_cons, ← hm]
    rfl
  · have : mods.val.length ≤ i.val := by scalar_tac
    simp [List.drop_eq_nil_of_le this, SudoersSpec.applyMods]
termination_by mods.val.length - i.val
decreasing_by all_goals (simp_all; scalar_tac)

/-- **`apply_modifiers` is `SudoersSpec.applyMods`.** -/
@[step]
theorem apply_modifiers_spec (mods : Slice sudo_rs.sudoers.ast.Modifier)
    (t : sudo_rs.sudoers.ast.Tag) (hwf : ∀ m ∈ mods.val, ModifierWF m)
    (h : t.ignored.val.length + mods.val.length ≤ Usize.max) :
    sudo_rs.sudoers.apply_modifiers mods t ⦃ t' =>
      absTag t' = SudoersSpec.applyMods (mods.val.map absModifier) (absTag t) ∧
      t'.ignored.val.length ≤ t.ignored.val.length + mods.val.length ⦄ := by
  simpa using apply_modifiers_loop_spec mods t 0#usize hwf (by simpa using h)

/-! ## `command_tag` -/

/-- **`command_tag` is `SudoersSpec.implicitSetenv`**, and keeps the `ignored` vector. -/
@[step]
theorem command_tag_spec (fc : RCommand → SudoersSpec.Command) (t : sudo_rs.sudoers.ast.Tag)
    (cmd : RSpec RCommand) :
    sudo_rs.sudoers.command_tag t cmd ⦃ t' =>
      absTag t' = SudoersSpec.implicitSetenv (absSpec fc cmd) (absTag t) ∧
      t'.ignored = t.ignored ⦄ := by
  unfold sudo_rs.sudoers.command_tag
  cases cmd with
  | Forbid m =>
    step as ⟨t', ht'⟩
    simp [ht', absSpec, absQualified, SudoersSpec.implicitSetenv]
  | Allow m =>
    cases m with
    | Only x =>
      step as ⟨t', ht'⟩
      simp [ht', absSpec, absQualified, absMeta, SudoersSpec.implicitSetenv]
    | Alias n =>
      step as ⟨t', ht'⟩
      simp [ht', absSpec, absQualified, absMeta, SudoersSpec.implicitSetenv]
    | All =>
      step with core.cmp.PartialEq.ne.trait_default.spec
        sudo_rs.sudoers.ast.EnvironmentControl.Insts.CoreCmpPartialEqEnvironmentControl t.env
        .Nosetenv (EnvironmentControl.eq_spec _ _) as ⟨b, hb⟩
      split
      · step as ⟨t', ht'⟩
        subst t'
        rename_i hbt
        have hne : t.env ≠ .Nosetenv := by simpa [hbt] using hb
        cases he : t.env <;> simp_all [absSpec, absQualified, absMeta,
          SudoersSpec.implicitSetenv, absTag, absEnv]
      · step as ⟨t', ht'⟩
        subst t'
        rename_i hbf
        have heq : t.env = .Nosetenv := by simpa [hbf] using hb
        simp [absSpec, absQualified, absMeta, SudoersSpec.implicitSetenv, absTag, absEnv, heq]

/-! ## `distribute_tags` -/

theorem lineMods_cons (e : REntry) (l : List REntry) :
    lineMods (e :: l) = csMods e.2 ++ lineMods l := by
  simp [lineMods]

theorem distribute_tags_loop_spec (fr : sudo_rs.sudoers.ast.RunAs → SudoersSpec.RunAs)
    (fc : RCommand → SudoersSpec.Command) (l : Slice REntry) (lr : Option Usize)
    (t : sudo_rs.sudoers.ast.Tag) (res : alloc.vec.Vec (Option Usize × sudo_rs.sudoers.ast.Tag))
    (i : Usize) (hwf : LineWF l.val) (hres : res.val.length = i.val)
    (hlr : ∀ j, lr = some j → j.val < i.val ∧ (l.val[j.val]?.bind (·.1)).isSome)
    (hig : t.ignored.val.length + (lineMods (l.val.drop i.val)).length ≤ Usize.max) :
    sudo_rs.sudoers.distribute_tags_loop l lr t res i ⦃ r =>
      ∃ ys, r.val = res.val ++ ys ∧ ys.length = l.val.length - i.val ∧
        List.zipWith (resolveEntry fr fc l.val) (l.val.drop i.val) ys =
          SudoersSpec.distributeTagsGo (resolveRunas fr l.val lr) (absTag t)
            (absLine fr fc (l.val.drop i.val)) ∧
        ∀ k (hk : k < ys.length), ∀ j, (ys[k]).1 = some j →
          j.val ≤ i.val + k ∧ (l.val[j.val]?.bind (·.1)).isSome ⦄ := by
  unfold sudo_rs.sudoers.distribute_tags_loop
  dsimp only
  split
  · have hlt : i.val < l.val.length := by scalar_tac
    have hdrop := List.drop_eq_getElem_cons hlt
    apply WP.spec_bind (Slice.index_usize_spec l i hlt)
    rintro ⟨runas, ⟨mods, cmd⟩⟩ hq
    simp only [uncurry]
    have hmem := List.getElem_mem hlt (l := l.val)
    have hmwf : ∀ m ∈ (alloc.vec.Vec.deref mods).val, ModifierWF m := by
      have := hwf _ hmem
      simpa [← hq, csMods] using this
    rw [hdrop, ← hq, lineMods_cons] at hig
    simp only [csMods, List.length_append] at hig
    -- everything after `last_runas` is computed
    have tail : ∀ lr1 : Option Usize,
        resolveRunas fr l.val lr1 = (runas.map fr).or (resolveRunas fr l.val lr) →
        (∀ j, lr1 = some j → j.val ≤ i.val ∧ (l.val[j.val]?.bind (·.1)).isSome) →
        (do
          let tag1 ← sudo_rs.sudoers.apply_modifiers (alloc.vec.Vec.deref mods) t
          let t ← sudo_rs.sudoers.command_tag tag1 cmd
          let result1 ← alloc.vec.Vec.push res (lr1, t)
          let i2 ← i + 1#usize
          sudo_rs.sudoers.distribute_tags_loop l lr1 tag1 result1 i2) ⦃ r =>
        ∃ ys, r.val = res.val ++ ys ∧ ys.length = l.val.length - i.val ∧
          List.zipWith (resolveEntry fr fc l.val) (l.val.drop i.val) ys =
            SudoersSpec.distributeTagsGo (resolveRunas fr l.val lr) (absTag t)
              (absLine fr fc (l.val.drop i.val)) ∧
          ∀ k (hk : k < ys.length), ∀ j, (ys[k]).1 = some j →
            j.val ≤ i.val + k ∧ (l.val[j.val]?.bind (·.1)).isSome ⦄ := by
      intro lr1 hres1 hlr1
      step with apply_modifiers_spec (alloc.vec.Vec.deref mods) t hmwf
        (by simp only [Vec.deref_val]; omega)
        as ⟨t1, ht1, hl1⟩
      step with command_tag_spec fc t1 cmd as ⟨t2, ht2, _⟩
      have hpush : res.val.length < Usize.max := by scalar_tac
      step as ⟨res1, hres1v⟩
      step as ⟨i2, hi2⟩
      have hlr2 : ∀ j, lr1 = some j → j.val < i2.val ∧ (l.val[j.val]?.bind (·.1)).isSome := by
        intro j hj
        obtain ⟨h1, h2⟩ := hlr1 j hj
        exact ⟨by omega, h2⟩
      have hig2 : t1.ignored.val.length + (lineMods (l.val.drop i2.val)).length ≤ Usize.max := by
        simp only [Vec.deref_val] at hl1
        rw [hi2]; omega
      step with distribute_tags_loop_spec fr fc l lr1 t1 res1 i2 hwf
        (by simp [hres1v, hres, hi2]) hlr2 hig2 as ⟨r, ys, hr, hlen, hzip, hpos⟩
      refine ⟨(lr1, t2) :: ys, by simp [hr, hres1v], by simp [hlen, hi2]; omega, ?_, ?_⟩
      · rw [hdrop, ← hq, List.zipWith_cons_cons, ← hi2, hzip]
        simp only [absLine, List.map_cons, absCommandSpec, csMods, csCmd,
          SudoersSpec.distributeTagsGo, resolveEntry, Vec.deref_val] at ht1 ⊢
        rw [hres1, ht2, ht1]
      · intro k hk j hj
        cases k with
        | zero =>
          obtain ⟨h1, h2⟩ := hlr1 j (by simpa using hj)
          exact ⟨by omega, h2⟩
        | succ k =>
          obtain ⟨h1, h2⟩ := hpos k (by simpa using hk) j (by simpa using hj)
          exact ⟨by omega, h2⟩
    have hli : (l.val[i.val]?).bind (·.1) = runas := by
      simp [List.getElem?_eq_getElem hlt, ← hq]
    cases runas with
    | none =>
      simp only [core.option.Option.is_some, Option.isSome_none, Bool.false_eq_true, ite_false,
        Aeneas.Std.bind_ok]
      apply tail lr (by simp)
      intro j hj
      obtain ⟨h1, h2⟩ := hlr j hj
      exact ⟨by omega, h2⟩
    | some ra =>
      simp only [core.option.Option.is_some, Option.isSome_some, ite_true, Aeneas.Std.bind_ok]
      apply tail (some i)
      · simp [resolveRunas, hli]
      · intro j hj
        cases hj
        exact ⟨le_refl _, by simp [hli]⟩
  · have : l.val.length ≤ i.val := by scalar_tac
    rw [WP.spec_ok]
    refine ⟨[], by simp, by simp; omega, ?_, by simp⟩
    simp [List.drop_eq_nil_of_le this, absLine, SudoersSpec.distributeTagsGo]
termination_by l.val.length - i.val
decreasing_by all_goals scalar_decr_tac

/-- **`distribute_tags` refines `SudoersSpec.distributeTags`.** The Rust result has one entry
per command of the line; entry `k` holds the position `j ≤ k` of the runas spec in effect (an
entry of the same line with an explicit runas spec) and the distributed tag. Reading each
position against the line (`resolveEntry`) gives exactly the spec's distributed list.
Hypotheses: the modifiers are parser-produced (`LineWF`) and their total number fits in `usize`
(bounds the `ignored` vector that `Modifier::Ignored` pushes to). -/
@[step]
theorem distribute_tags_spec (fr : sudo_rs.sudoers.ast.RunAs → SudoersSpec.RunAs)
    (fc : RCommand → SudoersSpec.Command) (l : Slice REntry) (hwf : LineWF l.val)
    (hig : (lineMods l.val).length ≤ Usize.max) :
    sudo_rs.sudoers.distribute_tags l ⦃ r =>
      r.val.length = l.val.length ∧
      List.zipWith (resolveEntry fr fc l.val) l.val r.val =
        SudoersSpec.distributeTags (absLine fr fc l.val) ∧
      ∀ k (hk : k < r.val.length), ∀ j, (r.val[k]).1 = some j →
        j.val ≤ k ∧ (l.val[j.val]?.bind (·.1)).isSome ⦄ := by
  unfold sudo_rs.sudoers.distribute_tags
  step as ⟨t, ht, hti⟩
  step with distribute_tags_loop_spec fr fc l none t (alloc.vec.Vec.new _) 0#usize hwf
    (by simp) (by simp) (by simpa [hti] using hig) as ⟨r, ys, hr, hlen, hzip, hpos⟩
  simp only [alloc.vec.Vec.new] at hr
  refine ⟨?_, ?_, ?_⟩
  · simp_all
  · simp_all [SudoersSpec.distributeTags, resolveRunas]
  · intro k hk j hj
    simp only [hr] at hk hj
    simpa using hpos k hk j hj

end SudoRsProofs
