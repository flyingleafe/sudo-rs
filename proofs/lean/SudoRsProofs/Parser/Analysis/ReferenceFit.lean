import SudoRsProofs.Parser.Analysis.ReferenceFit.Permissions

/-!
# Parsed reference items meet the matcher/collector representation bounds

This theorem also applies to files with diagnostics: each successful item in the recovery
trace has a grammar derivation. It does not assert the separate aggregate output-size budget
for analysis, which accounts for collection, diagnostics, and alias sanitizer storage.
-/

open SudoersSpec SudoersSpec.Syntax SudoersSpec.Grammar

namespace SudoRsProofs.Parser.Analysis.Ref

private theorem cursor_good {good : α → Prop} {G : Gram α} (h : GrammarGood good G)
    {s a t} (hg : AtCursor G s a t) : good a := by
  obtain ⟨_, _, ha, _⟩ := hg
  exact h ha

private theorem alias_defs_fit {good : α → Prop} {G : Gram (Meta α)} {m : Many}
    (h : GrammarGood (MetaFit good) G) : GrammarGood (defsFit good) (AliasDefsG G m) := by
  apply list_good
  intro c d r hd
  cases hd with
  | mk hn _ _ hm => exact ⟨nonterm_good alias_name_good hn, nonterm_good (spec_list_good h) hm⟩

private theorem punct_scope_fits {O s a t} (h : DefaultsPunctG O s a t) : scopeFits a := by
  cases h with
  | user _ h => exact cursor_good (nonterm_good (users_good O)) h
  | runAs _ _ _ h => exact cursor_good (nonterm_good (users_good O)) h
  | command _ _ h => exact cursor_good (nonterm_good (simple_command_list_good O)) h
  | generic => trivial

private theorem defaults_scope_fits {O rest s u a t} (h : DefaultsScopeG O rest s u a t) :
    scopeFits a := by
  cases h with
  | host _ _ h => exact cursor_good (nonterm_good (hosts_good O.char)) h
  | punct _ _ h => exact punct_scope_fits h
  | unscoped => trivial

private theorem directive_fits {O origin key s a t} (h : DirectiveG O origin key s a t) :
    itemFits (.ok (.decl a)) := by
  cases h with
  | user h | runAs h =>
    obtain ⟨_, _, ⟨defs, hd, rfl⟩, _⟩ := h
    exact nonterm_good (alias_defs_fit (meta_user_good O)) hd
  | host h =>
    obtain ⟨_, _, ⟨defs, hd, rfl⟩, _⟩ := h
    exact nonterm_good (alias_defs_fit (meta_hostname_good O.char)) hd
  | command _ h =>
    obtain ⟨_, _, ⟨defs, hd, rfl⟩, _⟩ := h
    exact nonterm_good (alias_defs_fit (command_meta_good O)) hd
  | defaults _ h _ => exact defaults_scope_fits h

theorem sudo_grammar_item_fits {O s a t} (h : SudoG O s a t) : itemFits (.ok a) := by
  rcases h with ⟨_, h⟩
  cases h with
  | permission h =>
    obtain ⟨_, _, hd, _⟩ := h
    exact permission_rule_fits hd
  | declaration _ _ h _ => exact directive_fits h
  | atInclude _ h | hashInclude _ _ h => cases h <;> trivial
  | hashComment | ordinaryComment => trivial

private theorem finish_fits {r : Parsed Sudo} {s : Stream} (h : itemFits r) :
    ∀ i ∈ (Recovery.finish r s).1, itemFits i := by
  intro i hi
  by_cases hn : (Recovery.afterComment s).peek = some '\n'
  · have he : i = r := by simpa [Recovery.finish, hn] using hi
    exact he ▸ h
  · cases r with
    | error e =>
      have he : i = .error e := by simpa [Recovery.finish, hn] using hi
      subst i
      trivial
    | ok a =>
      have he : i = .ok a ∨ i = .error (Recovery.terminatorError (Recovery.afterComment s)) := by
        simpa [Recovery.finish, hn] using hi
      rcases he with rfl | rfl
      · exact h
      · trivial

private theorem trace_items_fit {O : Oracles} {D : Descriptions} {s t : Stream} {items}
    (h : Recovery.Trace D.sudo (Syntax.sudo O D) s items t) : ∀ i ∈ items, itemFits i := by
  induction h with
  | eof => simp
  | @line _ r _ _ _ _ hp _ ih =>
    intro i hi
    rcases List.mem_append.mp hi with hin | hin
    · apply finish_fits _ i hin
      cases r with
      | error _ => trivial
      | ok a =>
        obtain ⟨_, hs, _⟩ := sudo_item_sound O D _ a _ hp
        exact sudo_grammar_item_fits hs
    · exact ih _ hin

theorem parseSudoersWith_items_fit {O : Oracles} {D : Descriptions} {src : List Char} {items}
    (h : parseSudoersWith D O src = .ok items) : ∀ i ∈ items, itemFits i := by
  obtain ⟨rs, hr, _⟩ := parseLines_ok D.sudo (Syntax.sudo O D) (Stream.new src)
  simp only [parseSudoersWith, hr] at h
  split at h
  · cases h
  · injection h with hEq
    subst items
    have ht : (parseLines D.sudo (Syntax.sudo O D)).run (Stream.new src) =
        (.ok rs, (Stream.new src).advance src.length) :=
      Prod.ext hr (Recovery.parseLines_end D.sudo (Syntax.sudo O D) (Stream.new src))
    exact trace_items_fit ((Recovery.parseLines_iff_trace _ _ _ _ _).mp ht)

/-- A successful release reference parse meets all per-item name and tag-count bounds. -/
theorem parseSudoers_items_fit {O : Oracles} {src : List Char} {items}
    (h : parseSudoers O src = .ok items) : ∀ i ∈ items, itemFits i :=
  parseSudoersWith_items_fit h

end SudoRsProofs.Parser.Analysis.Ref
