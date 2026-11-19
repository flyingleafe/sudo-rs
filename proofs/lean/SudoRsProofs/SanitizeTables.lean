import SudoRsProofs.SanitizeOrder

/-!
# Alias preprocessing of all four tables (`sanitize_alias_tables`)

`analyze` ends with `sanitize_alias_tables(&mut result.aliases, &mut diagnostics)`, which runs
`sanitize_alias_table` on the user, host, command and runas tables in that order. A successful
return keeps every definition list, gives every table a well-formed order (hence
`AliasTableOK` given the caller's `TableFits`/`TableGood`), and, if no diagnostic was added,
makes every table a sorted permutation of its definitions. `analyze` itself (parsing,
includes, IO) is not covered.
-/

open Aeneas Aeneas.Std Result
open Aeneas.Std.alloc.vec (Vec)
open sudo_rs sudo_rs.sudoers

namespace SudoRsProofs

/-- The conclusion of `sanitize_alias_table_sorted` for one table, for every abstraction of
its elements. -/
def SortedTable {T : Type} (t : VecOrd (RDef T)) : Prop :=
  ∀ (β : Type) (f : T → β), (t.2.val.map (absDef f)).Perm (absTable f t) ∧
    (SudoersSpec.names (absTable f t)).Nodup ∧ SudoersSpec.Sorted (absTable f t)

/-- A successful `sanitize_alias_tables` is four successful `sanitize_alias_table` calls,
threading the diagnostics in the order user, host, command, runas; definitions are kept. -/
theorem sanitize_alias_tables_ok {t t' : AliasTable} {diags diags' : Vec sudoers.Error}
    (h : sanitize_alias_tables t diags = ok (t', diags')) :
    ∃ d1 d2 d3, sanitize_alias_table t.user.2 diags = ok (t'.user.1, d1) ∧
      sanitize_alias_table t.host.2 d1 = ok (t'.host.1, d2) ∧
      sanitize_alias_table t.cmnd.2 d2 = ok (t'.cmnd.1, d3) ∧
      sanitize_alias_table t.runas.2 d3 = ok (t'.runas.1, diags') ∧
      t'.user.2 = t.user.2 ∧ t'.host.2 = t.host.2 ∧ t'.cmnd.2 = t.cmnd.2 ∧
      t'.runas.2 = t.runas.2 := by
  suffices hr : OnReturn (sanitize_alias_tables t diags) fun r =>
      ∃ d1 d2 d3, sanitize_alias_table t.user.2 diags = ok (r.1.user.1, d1) ∧
        sanitize_alias_table t.host.2 d1 = ok (r.1.host.1, d2) ∧
        sanitize_alias_table t.cmnd.2 d2 = ok (r.1.cmnd.1, d3) ∧
        sanitize_alias_table t.runas.2 d3 = ok (r.1.runas.1, r.2) ∧
        r.1.user.2 = t.user.2 ∧ r.1.host.2 = t.host.2 ∧ r.1.cmnd.2 = t.cmnd.2 ∧
        r.1.runas.2 = t.runas.2 from hr _ h
  rcases t with ⟨⟨ou, du⟩, ⟨oh, dh⟩, ⟨oc, dc⟩, ⟨or, dr⟩⟩
  unfold sanitize_alias_tables
  simp only [uncurry_apply_pair]
  apply OnReturn.bind
  rintro ⟨ou', d1⟩ h1
  simp only [uncurry_apply_pair]
  apply OnReturn.bind
  rintro ⟨oh', d2⟩ h2
  simp only [uncurry_apply_pair]
  apply OnReturn.bind
  rintro ⟨oc', d3⟩ h3
  simp only [uncurry_apply_pair]
  apply OnReturn.bind
  rintro ⟨or', d4⟩ h4
  simp only [uncurry_apply_pair]
  exact OnReturn.pure ⟨d1, d2, d3, h1, h2, h3, h4, rfl, rfl, rfl, rfl⟩

/-- **Well-formed orders.** After a successful `sanitize_alias_tables` every table keeps its
definitions and has a well-formed processing order; the diagnostics passed in are a prefix
of the returned ones. -/
theorem sanitize_alias_tables_tableWF {t t' : AliasTable} {diags diags' : Vec sudoers.Error}
    (h : sanitize_alias_tables t diags = ok (t', diags')) :
    (t'.user.2 = t.user.2 ∧ t'.host.2 = t.host.2 ∧ t'.cmnd.2 = t.cmnd.2 ∧
      t'.runas.2 = t.runas.2) ∧
    (TableWF t'.user ∧ TableWF t'.host ∧ TableWF t'.cmnd ∧ TableWF t'.runas) ∧
    diags.val <+: diags'.val := by
  obtain ⟨d1, d2, d3, h1, h2, h3, h4, eu, eh, ec, er⟩ := sanitize_alias_tables_ok h
  refine ⟨⟨eu, eh, ec, er⟩, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · have := sanitize_alias_table_tableWF _ _ h1; rwa [← eu] at this
  · have := sanitize_alias_table_tableWF _ _ h2; rwa [← eh] at this
  · have := sanitize_alias_table_tableWF _ _ h3; rwa [← ec] at this
  · have := sanitize_alias_table_tableWF _ _ h4; rwa [← er] at this
  · exact (sanitize_alias_table_distinct _ _ h1).2.1.trans <|
      (sanitize_alias_table_distinct _ _ h2).2.1.trans <|
      (sanitize_alias_table_distinct _ _ h3).2.1.trans (sanitize_alias_table_distinct _ _ h4).2.1

/-- `AliasTableOK` for the output of a successful `sanitize_alias_tables`, given the name and
element conditions on the input definitions. -/
theorem AliasTableOK.of_sanitize_alias_tables {t t' : AliasTable}
    {diags diags' : Vec sudoers.Error} (h : sanitize_alias_tables t diags = ok (t', diags'))
    (userFits : TableFits t.user) (userGood : TableGood UserSpecFits t.user)
    (hostFits : TableFits t.host) (hostGood : TableGood Fits t.host)
    (cmndFits : TableFits t.cmnd)
    (runasFits : TableFits t.runas) (runasGood : TableGood UserSpecFits t.runas) :
    AliasTableOK t' := by
  obtain ⟨⟨eu, eh, ec, er⟩, ⟨wu, wh, wc, wr⟩, -⟩ := sanitize_alias_tables_tableWF h
  refine ⟨⟨wu, ?_, ?_⟩, ⟨wh, ?_, ?_⟩, ⟨wc, ?_⟩, ⟨wr, ?_, ?_⟩⟩ <;>
    first
    | (intro d hd; first
        | exact userFits d (eu ▸ hd) | exact userGood d (eu ▸ hd)
        | exact hostFits d (eh ▸ hd) | exact hostGood d (eh ▸ hd)
        | exact cmndFits d (ec ▸ hd)
        | exact runasFits d (er ▸ hd) | exact runasGood d (er ▸ hd))

/-- **Sorted tables.** If `sanitize_alias_tables` returns without adding a diagnostic, every
one of the four tables is a sorted permutation of its definitions with unique names. -/
theorem sanitize_alias_tables_sorted {t t' : AliasTable} {diags diags' : Vec sudoers.Error}
    (h : sanitize_alias_tables t diags = ok (t', diags'))
    (hclean : diags'.val.length = diags.val.length) :
    SortedTable t'.user ∧ SortedTable t'.host ∧ SortedTable t'.cmnd ∧ SortedTable t'.runas := by
  obtain ⟨d1, d2, d3, h1, h2, h3, h4, eu, eh, ec, er⟩ := sanitize_alias_tables_ok h
  have p1 := (sanitize_alias_table_distinct _ _ h1).2.1.length_le
  have p2 := (sanitize_alias_table_distinct _ _ h2).2.1.length_le
  have p3 := (sanitize_alias_table_distinct _ _ h3).2.1.length_le
  have p4 := (sanitize_alias_table_distinct _ _ h4).2.1.length_le
  refine ⟨fun β f => ?_, fun β f => ?_, fun β f => ?_, fun β f => ?_⟩
  · have := sanitize_alias_table_sorted f _ _ h1 (by omega)
    rwa [← eu] at this
  · have := sanitize_alias_table_sorted f _ _ h2 (by omega)
    rwa [← eh] at this
  · have := sanitize_alias_table_sorted f _ _ h3 (by omega)
    rwa [← ec] at this
  · have := sanitize_alias_table_sorted f _ _ h4 (by omega)
    rwa [← er] at this

end SudoRsProofs
