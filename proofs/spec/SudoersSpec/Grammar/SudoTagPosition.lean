import SudoersSpec.Grammar.PermissionTags
import SudoersSpec.Grammar.SudoInclude

namespace SudoersSpec.Grammar

open SudoersSpec.Syntax SudoersSpec.Syntax.Parser

/-- `MetaTagG` with its start witness fixed to the ambient cursor position. -/
def MetaTagAtG (O : Oracles) (start : Nat × Nat) : Gram (Meta Modifier) :=
  fun c a r => ∃ key kw body, c = kw ++ body ∧ NontermG AliasNameG kw key (body ++ r) ∧
    TagRhsG O ⟨start, posAfter kw start⟩ key body a r

private theorem switch_run_iff (m : Modifier) {c r : List Char} {s : Stream}
    {a : Meta Modifier} (hs : s.rest = c ++ r) :
    (∃ t, (MapP (expectSyntax ':') (fun _ => .only m)).run s = (.ok a, t) ∧ t.rest = r) ↔
      MapG (SynG ':') (fun _ => .only m) c a r :=
  run_ok_iff (mapP_sound (expectSyntax_sound ':') _) (mapP_complete (expectSyntax_complete ':') _) hs

private theorem payload_run_iff (desc : String) (T : TokenSpec α) (f : α → Modifier)
    {c r : List Char} {s : Stream} {a : Meta Modifier} (hs : s.rest = c ++ r) :
    (∃ t, ((do
      expectSyntax '='
      let x ← expectNonterminal desc (token T)
      pure (.only (f x)) : Parser (Meta Modifier))).run s = (.ok a, t) ∧ t.rest = r) ↔
      SeqG (SynG '=') (fun _ => MapG (NontermG (TokenG T)) (fun x => .only (f x))) c a r :=
  run_ok_iff
    (seq_sound (expectSyntax_sound '=') (fun _ => mapP_sound (expectNonterminal_sound (token_sound T) desc) _))
    (seq_complete (expectSyntax_complete '=') (fun _ => mapP_complete (expectNonterminal_complete (token_complete T) desc) _)) hs

private theorem alias_run_iff (start : Nat × Nat) (key : String) {c r : List Char} {s : Stream}
    {a : Meta Modifier} (hs : s.rest = c ++ r) :
    (∃ t, ((do
      let eq ← isSyntax '='
      if eq then fatalFrom start (.unsupportedModifier key) else pure (.alias key) :
        Parser (Meta Modifier))).run s = (.ok a, t) ∧ t.rest = r) ↔
      c = [] ∧ a = .alias key ∧ NextNot (· = '=') r := by
  constructor
  · rintro ⟨t, ht, hr⟩
    obtain ⟨b, u, hb, he⟩ := run_bind_eq_ok.mp ht
    cases b with
    | true => simp at he
    | false =>
      obtain ⟨rfl, hn⟩ := isSyntax_false_iff.mp hb
      simp at he
      obtain ⟨rfl, rfl⟩ := he
      have hc : c ++ r = [] ++ r := hs.symm.trans hr
      exact ⟨List.append_cancel_right hc, rfl, hr ▸ hn⟩
  · rintro ⟨rfl, rfl, hn⟩
    have hr : s.rest = r := hs
    have hb : (isSyntax '=').run s = (.ok false, s) :=
      isSyntax_false_iff.mpr ⟨rfl, hr.symm ▸ hn⟩
    exact ⟨s, by rw [run_bind_of_ok hb]; rfl, hr⟩

/-- After the maximal keyword and its whitespace, the actual continuation is exactly
`TagRhsG` with the two observed positions. -/
private theorem metaOrTag_after_keyword_iff (O : Oracles) (D : Descriptions) {s u : Stream}
    {key : String} {body r : List Char} {a : Meta Modifier}
    (hk : (tryNonterminal (token aliasNameToken)).run s = (.ok key, u))
    (hu : u.rest = body ++ r) :
    (∃ t, (metaOrTag O D).run s = (.ok a, t) ∧ t.rest = r) ↔
      TagRhsG O ⟨s.getPos, u.getPos⟩ key body a r := by
  unfold metaOrTag TagRhsG
  rw [run_bind_of_ok (run_getPos s), run_bind_of_ok hk]
  split
  all_goals first
    | exact switch_run_iff _ hu
    | exact payload_run_iff _ _ _ hu
    | exact run_ok_iff (pure_sound (.all : Meta Modifier)) (pure_complete (.all : Meta Modifier)) hu
    | rw [run_bind_of_ok (run_getPos u)]; exact switch_run_iff _ hu
    | simp <;> exact alias_run_iff s.getPos key (a := a) hu

/-- Successful parsing agrees with the position-anchored grammar, including both endpoints
of ignored tag spans and the exact remaining cursor. -/
theorem metaOrTag_at_iff (O : Oracles) (D : Descriptions) {s t : Stream} {a : Meta Modifier} :
    (metaOrTag O D).run s = (.ok a, t) ↔ AtCursor (MetaTagAtG O s.getPos) s a t := by
  constructor
  · intro h
    have hp := h
    unfold metaOrTag at hp
    rw [run_bind_of_ok (run_getPos s)] at hp
    obtain ⟨key, u, hk, htail⟩ := run_bind_eq_ok.mp hp
    obtain ⟨kw, hkw, hg, hu⟩ := (tryNonterminal_sound aliasName_sound).pos hk
    let body := u.rest.take (u.rest.length - t.rest.length)
    have hr : u.rest = body ++ t.rest := (reaches_of_run htail).getPos_eq.1
    have hd := (metaOrTag_after_keyword_iff O D hk hr).mp ⟨t, h, rfl⟩
    have hc : s.rest = (kw ++ body) ++ t.rest := calc
      s.rest = kw ++ u.rest := hkw
      _ = kw ++ (body ++ t.rest) := congrArg (kw ++ ·) hr
      _ = _ := (List.append_assoc _ _ _).symm
    exact AtCursor.of_run h hc ⟨key, kw, body, rfl, hr ▸ hg, hu ▸ hd⟩
  · intro h
    have ht := h.reaches
    obtain ⟨_, hs, ⟨key, kw, body, rfl, hk, hd⟩, _⟩ := h
    obtain ⟨u, hu, hur⟩ := tryNonterminal_complete aliasName_complete _ _ _ _ hk
      (by rw [hs, List.append_assoc])
    have hup : u.getPos = posAfter kw s.getPos := by
      rw [(reaches_of_run hu).getPos_eq.2, hur, hs, List.append_assoc, take_sub_length_append]
    obtain ⟨v, hv, hvr⟩ := (metaOrTag_after_keyword_iff O D hu hur).mpr (hup.symm ▸ hd)
    have he : v = t := by
      rw [(reaches_of_run hv).eq_advance, ht.eq_advance, hvr]
    exact he ▸ hv

/-- From a fixed cursor the anchored grammar determines both the value and the final cursor. -/
theorem metaTagAtG_unique (O : Oracles) (D : Descriptions) {s t u : Stream}
    {a b : Meta Modifier} (ha : AtCursor (MetaTagAtG O s.getPos) s a t)
    (hb : AtCursor (MetaTagAtG O s.getPos) s b u) : a = b ∧ t = u := by
  have h := ((metaOrTag_at_iff O D).mpr ha).symm.trans ((metaOrTag_at_iff O D).mpr hb)
  simpa only [Prod.mk.injEq, Except.ok.injEq] using h

private theorem tagRhsG_ignored_rebase (O : Oracles) {span recorded : Span} (target : Span)
    {key : String} {c r : List Char} (h : TagRhsG O span key c (.only (.ignored recorded)) r) :
    TagRhsG O target key c (.only (.ignored target)) r := by
  unfold TagRhsG at h ⊢
  split at h
  all_goals first
    | exact False.elim h
    | obtain ⟨x, hx, _⟩ := h; exact ⟨x, hx, rfl⟩
    | simp [MapG, SeqG, PureG] at h

/-- The unanchored grammar leaves the start of an ignored span free. Its stop is still
computed by advancing over the keyword and its trailing whitespace. -/
theorem metaTagG_ignored_rebase (O : Oracles) {c r : List Char} {span : Span}
    (h : MetaTagG O c (.only (.ignored span)) r) (start : Nat × Nat) :
    ∃ stop, MetaTagG O c (.only (.ignored ⟨start, stop⟩)) r := by
  obtain ⟨key, kw, body, _, hc, hk, hd⟩ := h
  exact ⟨posAfter kw start, key, kw, body, start, hc, hk, tagRhsG_ignored_rebase O _ hd⟩

end SudoersSpec.Grammar
