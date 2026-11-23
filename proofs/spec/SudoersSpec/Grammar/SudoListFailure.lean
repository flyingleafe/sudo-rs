import SudoersSpec.Grammar.SudoInclude

namespace SudoersSpec.Grammar

open SudoersSpec.Syntax SudoersSpec.Syntax.Parser

variable {α β σ : Type}

private def MarkWsFailureG (ch : Char) : Gram Unit :=
  fun c _ r => ∃ w, c = ch :: w ∧ WsFailureG w () r

private theorem markWsFailure_sound {ch : Char} {s t : Stream} {sp : Span} {k : ErrKind}
    (h : (trySyntax ch).run s = (.error (.fatal sp k), t)) :
    ∃ c, s.rest = c ++ t.rest ∧ MarkWsFailureG ch c () t.rest := by
  rw [trySyntax_run] at h
  split at h
  · rename_i hp
    obtain ⟨w, hw, hg⟩ := ws_failure_sound _ _ _ h
    exact ⟨ch :: w, by rw [Stream.rest_of_peek hp, hw]; rfl, w, rfl, hg⟩
  · cases h

private theorem markWsFailure_complete {ch : Char} {c r : List Char} {s : Stream}
    (hg : MarkWsFailureG ch c () r) (hs : s.rest = c ++ r) :
    ∃ sp k t, (trySyntax ch).run s = (.error (.fatal sp k), t) ∧ t.rest = r := by
  obtain ⟨w, rfl, hw⟩ := hg
  have hp : s.peek = some ch := by rw [Stream.peek_eq_head, hs]; rfl
  obtain ⟨e, t, ht, hr⟩ := ws_failure_complete _ _ s.pop hw
    (by rw [Stream.pop_rest, hs]; rfl)
  cases e with
  | reject => exact (skipTrailingWhitespace_ne_reject _ (congrArg Prod.fst ht)).elim
  | fatal sp k => exact ⟨sp, k, t, by simp only [trySyntax_run, hp, ite_true, ht], hr⟩

private theorem syntaxStep_run (ch : Char) (k : σ → Unit → Parser (Step σ β))
    (finish : σ → β) (st : σ) (s : Stream) :
    (whileMaybeBody (trySyntax ch) k finish st).run s =
      match (trySyntax ch).run s with
      | (.ok a, u) => (k st a).run u
      | (.error .reject, u) => (.ok (.done (finish st)), u)
      | (.error (.fatal sp kind), u) => (.error (.fatal sp kind), u) := by
  rw [whileMaybeBody_run]
  rcases (trySyntax ch).run s with ⟨res, u⟩
  cases res with
  | ok a => rfl
  | error e => cases e <;> rfl

private theorem seqPrefix {G : Gram α} {H : α → Gram β} {s u t : Stream} {a : α} {b : β}
    (hG : ∃ c, s.rest = c ++ u.rest ∧ G c a u.rest)
    (hH : ∃ c, u.rest = c ++ t.rest ∧ H a c b t.rest) :
    ∃ c, s.rest = c ++ t.rest ∧ SeqG G H c b t.rest := by
  obtain ⟨x, hx, hd⟩ := hG
  obtain ⟨y, hy, hf⟩ := hH
  exact ⟨x ++ y, by rw [hx, hy, List.append_assoc], x, y, a, rfl, hy ▸ hd, hf⟩

private inductive BangWsFailureG : Gram Unit
  | here : MarkWsFailureG '!' c () r → BangWsFailureG c () r
  | next : SynG '!' b () (c ++ r) → BangWsFailureG c () r → BangWsFailureG (b ++ c) () r

private theorem bangLoop_failure_sound (neg : Bool) : FailureSound (bangLoop neg) BangWsFailureG := by
  intro s e t h
  have key := loop_rel (whileMaybeBody_progressive (trySyntax_consumes '!')
      (fun neg () => pure (.next !neg)) id)
    (fun _ s out t => ∀ e, out = .error e → ∃ c, s.rest = c ++ t.rest ∧ BangWsFailureG c () t.rest)
    ?_ ?_ ?_ neg s
  · unfold bangLoop whileMaybe at h
    rw [h] at key
    exact key e rfl
  · intro st s b t hb e he; cases he
  · intro st s e t hb e' _
    rw [syntaxStep_run] at hb
    rcases hq : (trySyntax '!').run s with ⟨res, u⟩
    rw [hq] at hb
    cases res with
    | ok a => cases hb
    | error err =>
      cases err with
      | reject => cases hb
      | fatal sp k =>
        cases hb
        obtain ⟨c, hc, hf⟩ := markWsFailure_sound hq
        exact ⟨c, hc, .here hf⟩
  · intro st s st' u out t hb ih e he
    rw [syntaxStep_run] at hb
    rcases hq : (trySyntax '!').run s with ⟨res, v⟩
    rw [hq] at hb
    cases res with
    | error err => cases err <;> cases hb
    | ok a =>
      cases a
      cases hb
      obtain ⟨b, hb, hw⟩ := trySyntax_sound '!' _ _ _ hq
      obtain ⟨c, hc, hf⟩ := ih e he
      exact ⟨b ++ c, by rw [hb, hc, List.append_assoc], .next (hc ▸ hw) hf⟩

private theorem bangLoop_failure_complete (neg : Bool) : FailureComplete (bangLoop neg) BangWsFailureG := by
  intro c r s hg hs
  generalize () = a at hg
  induction hg generalizing neg s with
  | here hw =>
    obtain ⟨sp, k, t, ht, hr⟩ := markWsFailure_complete hw hs
    refine ⟨.fatal sp k, t, ?_, hr⟩
    unfold bangLoop whileMaybe
    rw [loop_run, syntaxStep_run, ht]
  | @next b c r hb _ ih =>
    obtain ⟨u, hu, hrest⟩ := trySyntax_complete '!' b () (c ++ r) s hb (by rw [hs, List.append_assoc])
    obtain ⟨e, t, ht, hr⟩ := ih (!neg) u hrest
    refine ⟨e, t, ?_, hr⟩
    have hstep : (bangLoop neg).run s = (bangLoop (!neg)).run u := by
      unfold bangLoop whileMaybe
      rw [loop_run, syntaxStep_run, hu]
      rfl
    exact hstep.trans ht

/-- Whitespace after any bang can fail. Otherwise the item is attempted only after all
leading bangs, and its nonterminal may fail in the item or in its following whitespace. -/
inductive QualifiedFailureG (G : Gram α) (F : Gram Unit) : Gram Unit
  | bang : BangWsFailureG c () r → QualifiedFailureG G F c () r
  | item : Bangs n b (c ++ r) → NextNot (· = '!') (c ++ r) → NontermFailureG G F c () r →
      QualifiedFailureG G F (b ++ c) () r

theorem qualified_failure_sound {p : Parser α} {G : Gram α} {F : Gram Unit}
    (hG : Sound p G) (hF : FailureSound p F) (description : String) :
    FailureSound (qualified description p) (QualifiedFailureG G F) := by
  intro s e t h
  rw [qualified_run] at h
  rcases hi : (isSyntax '!').run s with ⟨ri, u⟩
  rw [hi] at h
  cases ri with
  | error err =>
    cases h
    rw [isSyntax_run] at hi
    rcases hq : (trySyntax '!').run s with ⟨res, v⟩
    rw [hq] at hi
    cases res with
    | ok a => cases hi
    | error k =>
      cases k with
      | reject => cases hi
      | fatal sp k =>
        cases hi
        obtain ⟨c, hc, hf⟩ := markWsFailure_sound hq
        exact ⟨c, hc, .bang (.here hf)⟩
  | ok flag =>
    cases flag with
    | false =>
      obtain ⟨hu, hn⟩ := isSyntax_false_iff.mp hi
      subst u
      rcases hp : (tryNonterminal p).run s with ⟨res, v⟩
      simp only [hp] at h
      cases res with
      | ok a => cases h
      | error k =>
        cases h
        obtain ⟨c, hc, hf⟩ := tryNonterm_failure hG hF _ _ _ hp
        exact ⟨c, hc, .item .nil (hc ▸ hn) hf⟩
    | true =>
      obtain ⟨b, hb, hd⟩ := trySyntax_sound '!' _ _ _ (isSyntax_true_iff.mp hi)
      rcases hloop : (bangLoop true).run u with ⟨res, v⟩
      simp only [hloop] at h
      cases res with
      | error k =>
        cases h
        obtain ⟨c, hc, hf⟩ := bangLoop_failure_sound true _ _ _ hloop
        exact ⟨b ++ c, by rw [hb, hc, List.append_assoc], .bang (.next (hc ▸ hd) hf)⟩
      | ok neg =>
        obtain ⟨b', n, hb', hbs, hn, _⟩ := bangLoop_sound true u hloop
        rcases hp : (expectNonterminal description p).run v with ⟨res, w⟩
        simp only [hp] at h
        cases res with
        | ok a => cases h
        | error k =>
          cases h
          obtain ⟨c, hc, hf⟩ := expectNonterm_failure hG hF description _ _ _ hp
          obtain ⟨w, rfl, hw⟩ := hd
          exact ⟨('!' :: w ++ b') ++ c, by rw [hb, hb', hc]; simp,
            .item (.cons (by rw [← hc, ← hb']; exact hw) (hc ▸ hbs)) (hc ▸ hn) hf⟩

theorem qualified_failure_complete {p : Parser α} {G : Gram α} {F : Gram Unit}
    (hG : Complete p G) (hF : FailureComplete p F) (description : String) :
    FailureComplete (qualified description p) (QualifiedFailureG G F) := by
  intro c r s hg hs
  cases hg with
  | bang hf =>
    cases hf with
    | here hw =>
      obtain ⟨sp, k, t, ht, hr⟩ := markWsFailure_complete hw hs
      have hi : (isSyntax '!').run s = (.error (.fatal sp k), t) := by
        rw [isSyntax_run, ht]; rfl
      exact ⟨.fatal sp k, t, by rw [qualified_run, hi], hr⟩
    | @next b c r hb hf =>
      obtain ⟨u, hu, hrest⟩ := trySyntax_complete '!' b () (c ++ r) s hb (by rw [hs, List.append_assoc])
      obtain ⟨e, t, ht, hr⟩ := bangLoop_failure_complete true _ _ _ hf hrest
      exact ⟨e, t, by rw [qualified_run, isSyntax_true_iff.mpr hu]; simp only [ht], hr⟩
  | @item n b c r hb hn hf =>
    cases hb with
    | nil =>
      have hi : (isSyntax '!').run s = (.ok false, s) :=
        isSyntax_false_iff.mpr ⟨rfl, hs.symm ▸ hn⟩
      obtain ⟨e, t, ht, hr⟩ := tryNontermFailure_complete hG hF _ _ _ hf hs
      exact ⟨e, t, by rw [qualified_run, hi]; simp only [ht], hr⟩
    | @cons w b' n _ hw hb =>
      obtain ⟨u, hu, hrest⟩ := trySyntax_complete '!' ('!' :: w) () (b' ++ (c ++ r)) s
        ⟨w, rfl, hw⟩ (by rw [hs]; simp)
      obtain ⟨v, hv, hrest'⟩ := bangLoop_complete hb hn true u hrest
      obtain ⟨e, t, ht, hr⟩ := expectNontermFailure_complete hG hF description _ _ _ hf hrest'
      exact ⟨e, t, by rw [qualified_run, isSyntax_true_iff.mpr hu]; simp only [hv, ht], hr⟩

/-- Failures of the loop after `n` items. The separator (including its whitespace) is processed
before the count is tested, and a later item is required only if there is room for it. -/
private inductive ListTailFailureG (G : Gram α) (F : Gram Unit) (sep : Char) (max : Nat) :
    Nat → Gram Unit
  | separator : MarkWsFailureG sep c () r → ListTailFailureG G F sep max n c () r
  | limit : max ≤ n → SynG sep c () r → ListTailFailureG G F sep max n c () r
  | item : n < max → SeqG (SynG sep) (fun _ => NontermFailureG G F) c () r →
      ListTailFailureG G F sep max n c () r
  | next : n < max → SeqG (SynG sep) (fun _ => NontermG G) b a (c ++ r) →
      ListTailFailureG G F sep max (n + 1) c () r → ListTailFailureG G F sep max n (b ++ c) () r

private theorem listLoop_failure_sound {p : Parser α} {G : Gram α} {F : Gram Unit}
    (hG : Sound p G) (hF : FailureSound p F) (sep : Char) (max : Nat) (description : String)
    (elems : List α) : FailureSound (listLoop sep max description p elems)
      (ListTailFailureG G F sep max elems.length) := by
  intro s e t h
  have key := loop_rel (whileMaybeBody_progressive (trySyntax_consumes sep)
      (parseListBody max description p) id)
    (fun st s out t => ∀ e, out = .error e → ∃ c, s.rest = c ++ t.rest ∧
      ListTailFailureG G F sep max st.length c () t.rest) ?_ ?_ ?_ elems s
  · unfold listLoop whileMaybe at h
    rw [h] at key
    exact key e rfl
  · intro st s b t hb e he; cases he
  · intro st s e t hb e' _
    rw [syntaxStep_run] at hb
    rcases hsep : (trySyntax sep).run s with ⟨res, u⟩
    rw [hsep] at hb
    cases res with
    | error err =>
      cases err with
      | reject => cases hb
      | fatal sp k =>
        cases hb
        obtain ⟨c, hc, hf⟩ := markWsFailure_sound hsep
        exact ⟨c, hc, .separator hf⟩
    | ok a =>
      cases a
      change (parseListBody max description p st ()).run u = _ at hb
      rw [parseListBody_run] at hb
      split at hb
      · rename_i hn
        cases hb
        obtain ⟨c, hc, hd⟩ := trySyntax_sound sep _ _ _ hsep
        exact ⟨c, hc, .limit hn hd⟩
      · rename_i hn
        rcases hp : (expectNonterminal description p).run u with ⟨res, v⟩
        rw [hp] at hb
        cases res with
        | ok a => cases hb
        | error k =>
          cases hb
          obtain ⟨c, hc, hf⟩ := seqPrefix (H := fun _ => NontermFailureG G F)
            (trySyntax_sound sep _ _ _ hsep) (expectNonterm_failure hG hF description _ _ _ hp)
          exact ⟨c, hc, .item (Nat.lt_of_not_ge hn) hf⟩
  · intro st s st' u out t hb ih e he
    rw [syntaxStep_run] at hb
    rcases hsep : (trySyntax sep).run s with ⟨res, v⟩
    rw [hsep] at hb
    cases res with
    | error err => cases err <;> cases hb
    | ok x =>
      cases x
      change (parseListBody max description p st ()).run v = _ at hb
      rw [parseListBody_run] at hb
      split at hb
      · cases hb
      · rename_i hn
        rcases hp : (expectNonterminal description p).run v with ⟨res, w⟩
        rw [hp] at hb
        cases res with
        | error k => cases hb
        | ok a =>
          cases hb
          obtain ⟨b, hb, hd⟩ := seqPrefix (H := fun _ => NontermG G)
            (trySyntax_sound sep _ _ _ hsep) (expectNonterminal_sound hG description _ _ _ hp)
          obtain ⟨c, hc, hf⟩ := ih e he
          have hf' : ListTailFailureG G F sep max (st.length + 1) c () t.rest := by simpa using hf
          exact ⟨b ++ c, by rw [hb, hc, List.append_assoc],
            .next (Nat.lt_of_not_ge hn) (hc ▸ hd) hf'⟩

private theorem listLoop_failure_complete {p : Parser α} {G : Gram α} {F : Gram Unit}
    (hG : Complete p G) (hF : FailureComplete p F) (sep : Char) (max : Nat) (description : String)
    (elems : List α) : FailureComplete (listLoop sep max description p elems)
      (ListTailFailureG G F sep max elems.length) := by
  intro c r s hg hs
  generalize he : elems.length = n at hg
  generalize () = a at hg
  induction hg generalizing elems s with
  | separator hf =>
    obtain ⟨sp, k, t, ht, hr⟩ := markWsFailure_complete hf hs
    refine ⟨.fatal sp k, t, ?_, hr⟩
    unfold listLoop whileMaybe
    rw [loop_run, syntaxStep_run, ht]
  | @limit n c r hn hd =>
    obtain ⟨u, hu, hr⟩ := trySyntax_complete sep c () r s hd hs
    refine ⟨.fatal ⟨u.getPos, u.getPos⟩ .tooManyItemsInList, u, ?_, hr⟩
    unfold listLoop whileMaybe
    rw [loop_run, syntaxStep_run, hu]
    simp only [parseListBody_run, he, hn, ite_true]
  | item hn hf =>
    obtain ⟨b, c, u', rfl, hd, hf⟩ := hf
    cases u'
    obtain ⟨u, hu, hrest⟩ := trySyntax_complete sep _ () _ s hd (by rw [hs, List.append_assoc])
    obtain ⟨e, t, ht, hr⟩ := expectNontermFailure_complete hG hF description _ _ _ hf hrest
    refine ⟨e, t, ?_, hr⟩
    unfold listLoop whileMaybe
    rw [loop_run, syntaxStep_run, hu]
    simp only [parseListBody_run, he, Nat.not_le_of_lt hn, ite_false, ht]
  | @next n b a c r hn hd _ ih =>
    obtain ⟨b, d, u', rfl, hsep, hd⟩ := hd
    cases u'
    obtain ⟨u, hu, hrest⟩ := trySyntax_complete sep _ () _ s hsep
      (by rw [hs]; simp only [List.append_assoc])
    obtain ⟨v, hv, hrest'⟩ := expectNonterminal_complete hG description _ _ _ u hd hrest
    have hresult : ∃ e t, (listLoop sep max description p (elems ++ [a])).run v =
        (.error e, t) ∧ t.rest = r := by
      apply ih <;> first | exact hrest' | simp [he]
    obtain ⟨e, t, ht, hr⟩ := hresult
    refine ⟨e, t, ?_, hr⟩
    have hstep : (listLoop sep max description p elems).run s =
        (listLoop sep max description p (elems ++ [a])).run v := by
      unfold listLoop whileMaybe
      rw [loop_run, syntaxStep_run, hu]
      simp only [parseListBody_run, he, Nat.not_le_of_lt hn, ite_false, hv]
    exact hstep.trans ht

/-- The first item is attempted without a count check. Only its success enters the list loop. -/
def ListFailureG (G : Gram α) (F : Gram Unit) (sep : Char) (max : Nat) : Gram Unit :=
  fun c a r => NontermFailureG G F c a r ∨
    SeqG (NontermG G) (fun _ => ListTailFailureG G F sep max 1) c a r

theorem parseList_failure_sound {p : Parser α} {G : Gram α} {F : Gram Unit}
    (hG : Sound p G) (hF : FailureSound p F) (sep : Char) (max : Nat) (description : String) :
    FailureSound (parseList sep max description p) (ListFailureG G F sep max) :=
  bind_failure_sound (tryNonterminal_sound hG) (tryNonterm_failure hG hF)
    (fun a => listLoop_failure_sound hG hF sep max description [a])

theorem parseList_failure_complete {p : Parser α} {G : Gram α} {F : Gram Unit}
    (hG : Complete p G) (hF : FailureComplete p F) (sep : Char) (max : Nat) (description : String) :
    FailureComplete (parseList sep max description p) (ListFailureG G F sep max) := by
  intro c r s hg hs
  rcases hg with hf | ⟨x, y, a, rfl, hd, hf⟩
  · obtain ⟨e, t, ht, hr⟩ := tryNontermFailure_complete hG hF _ _ _ hf hs
    exact ⟨e, t, by rw [parseList_run, ht], hr⟩
  · obtain ⟨u, hu, hrest⟩ := tryNonterminal_complete hG _ _ _ s hd (by rw [hs, List.append_assoc])
    obtain ⟨e, t, ht, hr⟩ := listLoop_failure_complete hG hF sep max description [a] _ _ _ hf hrest
    exact ⟨e, t, by rw [parseList_run, hu]; exact ht, hr⟩

def SpecListFailureG (G : Gram (Meta α)) (F : Gram Unit) (m : Many) : Gram Unit :=
  ListFailureG (QualG G) (QualifiedFailureG G F) m.sep m.limit

theorem specList_failure_sound {p : Parser (Meta α)} {G : Gram (Meta α)} {F : Gram Unit}
    (hG : Sound p G) (hF : FailureSound p F) (m : Many) (description : String) :
    FailureSound (specList m description p) (SpecListFailureG G F m) :=
  parseList_failure_sound (qualified_sound hG description) (qualified_failure_sound hG hF description)
    m.sep m.limit description

theorem specList_failure_complete {p : Parser (Meta α)} {G : Gram (Meta α)} {F : Gram Unit}
    (hG : Complete p G) (hF : FailureComplete p F) (m : Many) (description : String) :
    FailureComplete (specList m description p) (SpecListFailureG G F m) :=
  parseList_failure_complete (qualified_complete hG description) (qualified_failure_complete hG hF description)
    m.sep m.limit description

end SudoersSpec.Grammar
