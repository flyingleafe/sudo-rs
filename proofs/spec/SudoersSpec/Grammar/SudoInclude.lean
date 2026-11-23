import SudoersSpec.Grammar.SudoFailure
import SudoersSpec.Syntax.Sudo

namespace SudoersSpec.Grammar

open SudoersSpec.Syntax SudoersSpec.Syntax.Parser

/-- A grammar judgment on cursors records both the consumed prefix and its effect on position. -/
def AtCursor (G : Gram α) (s : Stream) (a : α) (t : Stream) : Prop :=
  ∃ c, s.rest = c ++ t.rest ∧ G c a t.rest ∧ t.getPos = posAfter c s.getPos

theorem Sound.atCursor {G : Gram α} {p : Parser α} (hs : Sound p G)
    {s t : Stream} {a : α} (h : p.run s = (.ok a, t)) : AtCursor G s a t := hs.pos h

theorem AtCursor.of_run {G : Gram α} {p : Parser β} {s t : Stream} {r : Parsed β}
    {a : α} (h : p.run s = (r, t)) {c : List Char} (hc : s.rest = c ++ t.rest)
    (hg : G c a t.rest) : AtCursor G s a t := by
  refine ⟨c, hc, hg, ?_⟩
  rw [(reaches_of_run h).getPos_eq.2, hc, take_sub_length_append]

theorem AtCursor.reaches {G : Gram α} {s t : Stream} {a : α} (h : AtCursor G s a t) :
    s.Reaches t := by
  obtain ⟨c, hs, _, ht⟩ := h
  refine ⟨c.length, ?_⟩
  have hr : (s.advance c.length).rest = t.rest := by simp [hs]
  have hp : (s.advance c.length).getPos = t.getPos := by
    rw [Stream.advance_getPos, hs, ht]
    simp
  generalize s.advance c.length = u at hr hp ⊢
  cases t
  cases u
  simp only [Stream.getPos_mk, Prod.mk.injEq] at hp
  simp_all

private theorem atFailure {G : Gram Unit} {p : Parser α} (hs : FailureSound p G)
    {s t : Stream} {e : Status} (h : p.run s = (.error e, t)) : AtCursor G s () t := by
  obtain ⟨c, hc, hg⟩ := hs _ _ _ h
  exact AtCursor.of_run h hc hg

private abbrev OrG (G H : Gram α) : Gram α := fun c a r => G c a r ∨ H c a r

private theorem seq_witness {G : Gram α} {H : α → Gram β} {s u t : Stream} {a : α} {b : β}
    (h₁ : ∃ c, s.rest = c ++ u.rest ∧ G c a u.rest)
    (h₂ : ∃ c, u.rest = c ++ t.rest ∧ H a c b t.rest) :
    ∃ c, s.rest = c ++ t.rest ∧ SeqG G H c b t.rest := by
  obtain ⟨c₁, hc₁, hg⟩ := h₁
  obtain ⟨c₂, hc₂, hh⟩ := h₂
  exact ⟨c₁ ++ c₂, by rw [hc₁, hc₂, List.append_assoc], c₁, c₂, a, rfl, hc₂ ▸ hg, hh⟩

/-- A nonterminal can fail in the production or in its following whitespace. -/
def NontermFailureG (G : Gram α) (F : Gram Unit) : Gram Unit :=
  OrG F (SeqG G fun _ => WsFailureG)

private theorem tryNonterm_failure {p : Parser α} {G : Gram α} {F : Gram Unit}
    (hG : Sound p G) (hF : FailureSound p F) :
    FailureSound (tryNonterminal p) (NontermFailureG G F) := by
  intro s e t h
  rcases run_bind_eq_error.mp h with he | ⟨a, u, ha, he⟩
  · obtain ⟨c, hc, hf⟩ := hF _ _ _ he
    exact ⟨c, hc, .inl hf⟩
  · rcases run_bind_eq_error.mp he with hw | ⟨_, _, _, he⟩
    · obtain ⟨c, hc, hg⟩ := seq_witness (H := fun _ => WsFailureG)
        (hG _ _ _ ha) (ws_failure_sound _ _ _ hw)
      exact ⟨c, hc, .inr hg⟩
    · cases he

private theorem expectNonterm_failure {p : Parser α} {G : Gram α} {F : Gram Unit}
    (hG : Sound p G) (hF : FailureSound p F) (description : String) :
    FailureSound (expectNonterminal description p) (NontermFailureG G F) := by
  intro s e t h
  simp only [expectNonterminal, run_bind, run_getPos, run_observe] at h
  rcases hp : (tryNonterminal p).run s with ⟨rp, u⟩
  rw [hp] at h
  cases rp with
  | ok a => cases h
  | error e' =>
    cases e' <;> cases h <;> exact tryNonterm_failure hG hF _ _ _ hp

private theorem optionalToken_failure (T : TokenSpec α) :
    FailureSound (parseOption (token T)) (TokenFatalG T) := by
  intro s e t h
  simp only [parseOption, run_maybe] at h
  rcases ht : (token T).run s with ⟨res, u⟩
  rw [ht] at h
  cases res with
  | ok a => cases h
  | error k =>
    cases k with
    | reject => cases h
    | fatal span kind => cases h; exact token_fatal_sound T ht

/-- Failure of a required marker: it is absent, or present but followed by malformed space. -/
def RequiredMarkFailureG (ch : Char) : Gram Unit :=
  SeqG (MarkG ch) fun b => if b then WsFailureG else PureG ()

private theorem requiredMark_failure (ch : Char) :
    FailureSound (expectSyntax ch) (RequiredMarkFailureG ch) := by
  intro s e t h
  simp only [expectSyntax, run_bind, run_observe, trySyntax_run] at h
  by_cases hd : s.peek = some ch
  · simp only [hd, ite_true] at h
    rcases hw : skipTrailingWhitespace.run s.pop with ⟨res, u⟩
    rw [hw] at h
    cases res with
    | ok a => cases h
    | error er =>
      cases er with
      | reject =>
        have he := skipTrailingWhitespace_ne_reject s.pop
        rw [hw] at he
        exact (he rfl).elim
      | fatal span kind =>
        cases h
        obtain ⟨c, hc, hws⟩ := ws_failure_sound _ _ _ hw
        exact ⟨ch :: c, by rw [Stream.rest_of_peek hd, hc]; rfl,
          [ch], c, true, rfl, .present, hws⟩
  · simp only [hd, ite_false] at h
    cases h
    exact ⟨[], rfl, [], [], false, rfl, .absent (fun d hr hch => hd (hch ▸ hr)), rfl, rfl⟩

private def IncludePathTailG (O : Oracles) (quoted : Bool) : Gram String :=
  if quoted then
    SeqG (NontermG (TokenG (quotedIncludePathToken O.char))) fun path =>
      MapG (SynG '"') (fun _ => path)
  else fun c path r => NontermG (TokenG (includePathToken O.char)) c path r ∧ r.head? = some '\n'

/-- Path spelling with the lexer selected by the opening quote. Unquoted paths must end
at a physical newline, after their trailing whitespace. -/
def IncludePathG (O : Oracles) : Gram String :=
  SeqG (MarkG '"') (IncludePathTailG O)

def IncludePathFailureG (O : Oracles) : Gram Unit :=
  SeqG (MarkG '"') fun quoted =>
    if quoted then OrG
      (NontermFailureG (TokenG (quotedIncludePathToken O.char)) (TokenFailureG (quotedIncludePathToken O.char)))
      (SeqG (NontermG (TokenG (quotedIncludePathToken O.char))) fun _ => RequiredMarkFailureG '"')
    else OrG
      (NontermFailureG (TokenG (includePathToken O.char)) (TokenFailureG (includePathToken O.char)))
      (SeqG (NontermG (TokenG (includePathToken O.char))) fun _ c _ r => c = [] ∧ r.head? ≠ some '\n')

private theorem path_sound (O : Oracles) (D : Descriptions) {s t : Stream} {path : String}
    {span : Span} {keyPos : Nat × Nat} (h : (getPath O D keyPos).run s = (.ok (path, span), t)) :
    AtCursor (IncludePathG O) s path t ∧ span = ⟨keyPos, t.getPos⟩ := by
  obtain ⟨quoted, v, hmark, hbody⟩ := run_bind_eq_ok.mp h
  have hm := mark_sound '"' _ _ _ hmark
  have hb : (∃ c, v.rest = c ++ t.rest ∧ IncludePathTailG O quoted c path t.rest) ∧
      span = ⟨keyPos, t.getPos⟩ := by
    cases quoted
    · simp only [IncludePathTailG, Bool.false_eq_true, ite_false, run_bind_of_ok (run_getPos _)] at hbody ⊢
      obtain ⟨p, w, hp, hn⟩ := run_bind_eq_ok.mp hbody
      simp only [run_bind, run_peek] at hn
      by_cases hnl : w.peek = some '\n'
      · simp only [hnl, bne_self_eq_false, Bool.false_eq_true, ite_false, run_bind, run_getPos,
          run_pure, Prod.mk.injEq, Except.ok.injEq] at hn
        obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hn
        obtain ⟨c, hc, hg⟩ := expectNonterminal_sound (token_sound _) _ _ _ _ hp
        exact ⟨⟨c, hc, hg, hnl⟩, rfl⟩
      · have hne : (w.peek != some '\n') = true := by simpa using hnl
        simp [hne, run_bind] at hn
    · simp only [IncludePathTailG, ite_true] at hbody ⊢
      obtain ⟨p, w, hp, hrest⟩ := run_bind_eq_ok.mp hbody
      obtain ⟨_, z, hquote, hf⟩ := run_bind_eq_ok.mp hrest
      simp only [run_bind, run_getPos, run_pure, Prod.mk.injEq, Except.ok.injEq] at hf
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hf
      obtain ⟨c, hc, hg⟩ := expectSyntax_sound '"' _ _ _ hquote
      exact ⟨seq_witness (H := fun p => MapG (SynG '"') (fun _ => p))
        (expectNonterminal_sound (token_sound _) _ _ _ _ hp) ⟨c, hc, (), hg, rfl⟩, rfl⟩
  obtain ⟨c, hc, hg⟩ := seq_witness (H := IncludePathTailG O) hm hb.1
  exact ⟨AtCursor.of_run h hc hg, hb.2⟩

private theorem path_failure (O : Oracles) (D : Descriptions) (keyPos : Nat × Nat) :
    FailureSound (getPath O D keyPos) (IncludePathFailureG O) := by
  intro s e t h
  rcases run_bind_eq_error.mp h with h | ⟨quoted, u, hm, hb⟩
  · simp at h
  unfold IncludePathFailureG
  apply seq_witness (mark_sound '\"' _ _ _ hm)
  cases quoted
  · simp only [Bool.false_eq_true, ite_false, run_bind_of_ok (run_getPos _)] at hb ⊢
    rcases run_bind_eq_error.mp hb with he | ⟨path, v, hp, he⟩
    · obtain ⟨c, hc, hf⟩ := expectNonterm_failure (token_sound _) (token_failure_sound _) _ _ _ _ he
      exact ⟨c, hc, .inl hf⟩
    · simp only [run_bind, run_peek] at he
      by_cases hnl : v.peek = some '\n'
      · simp [hnl, run_bind] at he
      · have hne : (v.peek != some '\n') = true := by simpa using hnl
        simp only [hne, ite_true, run_bind, run_fatalFrom, Prod.mk.injEq] at he
        obtain ⟨-, rfl⟩ := he
        obtain ⟨c, hc, hg⟩ := seq_witness
          (expectNonterminal_sound (token_sound _) _ _ _ _ hp)
          (H := fun _ c _ r => c = [] ∧ r.head? ≠ some '\n') ⟨[], rfl, rfl, hnl⟩
        exact ⟨c, hc, .inr hg⟩
  · simp only [ite_true] at hb ⊢
    rcases run_bind_eq_error.mp hb with he | ⟨path, v, hp, he⟩
    · obtain ⟨c, hc, hf⟩ := expectNonterm_failure (token_sound _) (token_failure_sound _) _ _ _ _ he
      exact ⟨c, hc, .inl hf⟩
    · rcases run_bind_eq_error.mp he with hf | ⟨_, _, _, hf⟩
      · obtain ⟨c, hc, hg⟩ := seq_witness
          (H := fun _ => RequiredMarkFailureG '\"')
          (expectNonterminal_sound (token_sound _) _ _ _ _ hp) (requiredMark_failure _ _ _ _ hf)
        exact ⟨c, hc, .inr hg⟩
      · cases hf

abbrev IncludeKeyTokenG (O : Oracles) : Gram (Option String) :=
  OptG (UsernameG O) (TokenRejectG (usernameToken O))

abbrev IncludeKeyG (O : Oracles) : Gram (Option String) := NontermG (IncludeKeyTokenG O)

private theorem includeKey_sound (O : Oracles) :
    Sound (tryNonterminal (parseOption (token (usernameToken O)))) (IncludeKeyG O) :=
  tryNonterminal_sound (option_sound (token_sound _) (token_rejectSound _))

/-- Include text starting after `@` or after the failed id, with the actual path span. -/
inductive IncludeG (O : Oracles) : Stream → Sudo → Stream → Prop where
  | file : AtCursor (IncludeKeyG O) s (some "include") u → AtCursor (IncludePathG O) u path t →
      IncludeG O s (.include path ⟨s.getPos, t.getPos⟩) t
  | dir : AtCursor (IncludeKeyG O) s (some "includedir") u → AtCursor (IncludePathG O) u path t →
      IncludeG O s (.includeDir path ⟨s.getPos, t.getPos⟩) t

/-- The include attempt used by hash dispatch can fail before classifying the name,
after a different name, or in the path of a recognized directive. -/
inductive IncludeFailure (O : Oracles) : Stream → Stream → Prop where
  | key : AtCursor (NontermFailureG (IncludeKeyTokenG O) (TokenFatalG (usernameToken O))) s () t →
      IncludeFailure O s t
  | other : AtCursor (IncludeKeyG O) s key t → key ≠ some "include" → key ≠ some "includedir" →
      IncludeFailure O s t
  | path : AtCursor (IncludeKeyG O) s key u → (key = some "include" ∨ key = some "includedir") →
      AtCursor (IncludePathFailureG O) u () t → IncludeFailure O s t

theorem include_sound (O : Oracles) (D : Descriptions) {s t : Stream} {a : Sudo}
    (h : (parseInclude O D).run s = (.ok a, t)) : IncludeG O s a t := by
  simp only [parseInclude, run_bind_of_ok (run_getPos _)] at h
  obtain ⟨key, u, hk, hbody⟩ := run_bind_eq_ok.mp h
  split at hbody
  · obtain ⟨⟨path, span⟩, v, hp, he⟩ := run_bind_eq_ok.mp hbody
    cases he
    obtain ⟨hpath, rfl⟩ := path_sound O D hp
    exact .file ((includeKey_sound O).atCursor hk) hpath
  · obtain ⟨⟨path, span⟩, v, hp, he⟩ := run_bind_eq_ok.mp hbody
    cases he
    obtain ⟨hpath, rfl⟩ := path_sound O D hp
    exact .dir ((includeKey_sound O).atCursor hk) hpath
  · cases hbody

theorem include_failure (O : Oracles) (D : Descriptions) {s t : Stream} {e : Status}
    (h : (parseInclude O D).run s = (.error e, t)) : IncludeFailure O s t := by
  simp only [parseInclude, run_bind_of_ok (run_getPos _)] at h
  rcases run_bind_eq_error.mp h with he | ⟨k, u, hk, hb⟩
  · apply IncludeFailure.key
    exact atFailure (tryNonterm_failure (option_sound (token_sound _) (token_rejectSound _))
      (optionalToken_failure _)) he
  · split at hb
    · rcases run_bind_eq_error.mp hb with he | ⟨_, _, _, he⟩
      · exact .path ((includeKey_sound O).atCursor hk) (.inl rfl) (atFailure (path_failure O D _) he)
      · cases he
    · rcases run_bind_eq_error.mp hb with he | ⟨_, _, _, he⟩
      · exact .path ((includeKey_sound O).atCursor hk) (.inr rfl) (atFailure (path_failure O D _) he)
      · cases he
    · rename_i _ hn₁ hn₂
      cases hb
      exact .other ((includeKey_sound O).atCursor hk) hn₁ hn₂

/-- On the `#` branch, the mandatory decimal token can fail, or an accepted id may be
followed by malformed trailing whitespace before the include attempt. -/
def HashIdFailureG : Gram Unit :=
  OrG (SeqG (MarkG '#') fun b => if b then NontermFailureG DigitsG (TokenFailureG digitsU32Token) else EmptyG)
    (SeqG (SeqG (MarkG '#') fun b => if b then MapG (NontermG DigitsG) Identifier.id else EmptyG)
      fun _ => WsFailureG)

theorem hash_id_failure (O : Oracles) (D : Descriptions) {s t : Stream} {e : Status}
    (hh : s.peek = some '#') (h : (tryNonterminal (identifier O D)).run s = (.error e, t)) :
    AtCursor HashIdFailureG s () t := by
  have hs : ∃ c, s.rest = c ++ t.rest ∧ HashIdFailureG c () t.rest := by
    rcases run_bind_eq_error.mp h with he | ⟨ident, u, hi, he⟩
    · simp only [identifier, run_bind, run_eatChar, Stream.eatChar_eq, hh, ite_true] at he
      rcases run_bind_eq_error.mp he with hd | ⟨_, _, _, hd⟩
      · obtain ⟨c, hc, hf⟩ := expectNonterm_failure (token_sound digitsU32Token)
          (token_failure_sound digitsU32Token) _ _ _ _ hd
        exact ⟨'#' :: c, by rw [Stream.rest_of_peek hh, hc]; rfl, .inl
          ⟨['#'], c, true, rfl, .present, hf⟩⟩
      · cases hd
    · rcases run_bind_eq_error.mp he with hw | ⟨_, _, _, hw⟩
      · obtain ⟨c, hc, hg⟩ := seq_witness (H := fun _ => WsFailureG)
          (identifier_sound O D _ _ _ hi) (ws_failure_sound _ _ _ hw)
        obtain ⟨c₁, c₂, id, rfl, ⟨c₃, c₄, isId, rfl, hm, hrest⟩, hws⟩ := hg
        cases hm with
        | present => exact ⟨_, hc, .inr ⟨_, _, id, rfl, ⟨_, _, true, rfl, .present, hrest⟩, hws⟩⟩
        | absent hn =>
          rw [List.nil_append, List.append_assoc] at hc
          exact (hn '#' (by rw [← hc]; exact hh) rfl).elim
      · cases hw
  obtain ⟨c, hc, hg⟩ := hs
  exact AtCursor.of_run h hc hg

/-! ## Completeness, including the failure cursor observed by `#` -/

private theorem same_cursor {s t u : Stream} (ht : s.Reaches t) (hu : s.Reaches u)
    (hr : t.rest = u.rest) : t = u := by
  rw [ht.eq_advance, hu.eq_advance, hr]

theorem AtCursor.complete {G : Gram α} {p : Parser α} (hp : Complete p G)
    {s t : Stream} {a : α} (h : AtCursor G s a t) : p.run s = (.ok a, t) := by
  have ht := h.reaches
  obtain ⟨c, hc, hg, _⟩ := h
  obtain ⟨u, hu, hr⟩ := hp c a t.rest s hg hc
  rwa [same_cursor (reaches_of_run hu) ht hr] at hu

theorem AtCursor.failure_complete {G : Gram Unit} {p : Parser α} (hp : FailureComplete p G)
    {s t : Stream} (h : AtCursor G s () t) : ∃ e, p.run s = (.error e, t) := by
  have ht := h.reaches
  obtain ⟨c, hc, hg, _⟩ := h
  obtain ⟨e, u, hu, hr⟩ := hp c t.rest s hg hc
  exact ⟨e, same_cursor (reaches_of_run hu) ht hr ▸ hu⟩

theorem AtCursor.reject_complete {G : Gram Unit} {p : Parser α} (hp : RejectComplete p G)
    {s t : Stream} (h : AtCursor G s () t) : p.run s = (.error .reject, t) := by
  have ht := h.reaches
  obtain ⟨c, hc, hg, _⟩ := h
  obtain ⟨u, hu, hr⟩ := hp c t.rest s hg hc
  rwa [same_cursor (reaches_of_run hu) ht hr] at hu

private theorem tryNontermFailure_complete {p : Parser α} {G : Gram α} {F : Gram Unit}
    (hG : Complete p G) (hF : FailureComplete p F) :
    FailureComplete (tryNonterminal p) (NontermFailureG G F) := by
  intro c r s hg hs
  rcases hg with hf | ⟨x, y, a, rfl, hx, hy⟩
  · obtain ⟨e, t, he, ht⟩ := hF _ _ _ hf hs
    exact ⟨e, t, by simp [tryNonterminal, run_bind, he], ht⟩
  · obtain ⟨u, hu, hr⟩ := hG _ _ _ _ hx (by rw [hs, List.append_assoc])
    obtain ⟨e, t, he, ht⟩ := ws_failure_complete _ _ _ hy hr
    exact ⟨e, t, by simp [tryNonterminal, run_bind, hu, he], ht⟩

private theorem expect_failure_of_try (description : String) {p : Parser α} {s t : Stream} {e : Status}
    (h : (tryNonterminal p).run s = (.error e, t)) :
    ∃ e', (expectNonterminal description p).run s = (.error e', t) := by
  cases e with
  | reject => exact ⟨.fatal ⟨s.getPos, t.getPos⟩ (.expected description), by
      simp [expectNonterminal, run_bind, h]⟩
  | fatal sp k => exact ⟨.fatal sp k, by simp [expectNonterminal, run_bind, h]⟩

private theorem expectNontermFailure_complete {p : Parser α} {G : Gram α} {F : Gram Unit}
    (hG : Complete p G) (hF : FailureComplete p F) (description : String) :
    FailureComplete (expectNonterminal description p) (NontermFailureG G F) := by
  intro c r s hg hs
  obtain ⟨e, t, he, ht⟩ := tryNontermFailure_complete hG hF _ _ _ hg hs
  obtain ⟨e', he'⟩ := expect_failure_of_try description he
  exact ⟨e', t, he', ht⟩

private theorem optionalTokenFailure_complete (T : TokenSpec α) :
    FailureComplete (parseOption (token T)) (TokenFatalG T) := by
  intro c r s hg hs
  obtain ⟨sp, k, t, ht, hr⟩ := token_fatal_complete T _ _ _ hg hs
  exact ⟨.fatal sp k, t, by simp [parseOption, run_maybe, ht], hr⟩

private theorem requiredMarkFailure_complete (ch : Char) :
    FailureComplete (expectSyntax ch) (RequiredMarkFailureG ch) := by
  rintro c r s ⟨x, y, b, rfl, hm, hf⟩ hs
  cases hm with
  | present =>
    have hpeek : s.peek = some ch := by rw [Stream.peek_eq_head, hs]; rfl
    have hrest : s.pop.rest = y ++ r := by rw [Stream.pop_rest, hs]; rfl
    obtain ⟨e, t, ht, hr⟩ := ws_failure_complete _ _ _ hf hrest
    cases e with
    | reject => exact (skipTrailingWhitespace_ne_reject _ (congrArg Prod.fst ht)).elim
    | fatal sp k => exact ⟨.fatal ⟨t.getPos, t.getPos⟩ (.expectingSyntax ch t.peek), t, by
        simp [expectSyntax, run_bind, trySyntax_run, hpeek, ht], hr⟩
  | absent hn =>
    obtain ⟨rfl, _⟩ := hf
    have hn' : s.peek ≠ some ch := fun hd => hn ch (by simpa [Stream.peek_eq_head, hs] using hd) rfl
    exact ⟨.fatal ⟨s.getPos, s.getPos⟩ (.expectingSyntax ch s.peek), s, by
      simp [expectSyntax, run_bind, trySyntax_run, hn'], by simpa using hs⟩

private theorem path_complete (O : Oracles) (D : Descriptions) (keyPos : Nat × Nat)
    {s t : Stream} {path : String} (h : AtCursor (IncludePathG O) s path t) :
    (getPath O D keyPos).run s = (.ok (path, ⟨keyPos, t.getPos⟩), t) := by
  have ht := h.reaches
  obtain ⟨_, hs, ⟨pfx, body, quoted, rfl, hmark, hb⟩, _⟩ := h
  obtain ⟨u, hu, hr⟩ := mark_complete '"' _ _ _ _ hmark (by rw [hs, List.append_assoc])
  have finish (w : Stream)
      (hw : (getPath O D keyPos).run s = (.ok (path, ⟨keyPos, w.getPos⟩), w))
      (hrest : w.rest = t.rest) : (getPath O D keyPos).run s = (.ok (path, ⟨keyPos, t.getPos⟩), t) := by
    rwa [same_cursor (reaches_of_run hw) ht hrest] at hw
  cases quoted with
  | false =>
    obtain ⟨hg, hn⟩ := hb
    obtain ⟨v, hv, vr⟩ := expectNonterminal_complete (token_complete _) D.includePath _ _ _ _ hg hr
    have hnl : v.peek = some '\n' := by rw [Stream.peek_eq_head, vr]; exact hn
    exact finish v (by simp only [getPath, run_bind_of_ok hu]; simp [run_bind, hv, hnl]) vr
  | true =>
    obtain ⟨x, y, a, rfl, hx, ⟨z, hz, rfl⟩⟩ := hb
    cases z
    obtain ⟨v, hv, vr⟩ := expectNonterminal_complete (token_complete _) D.quotedIncludePath _ _ _ _ hx
      (by rw [hr, List.append_assoc])
    obtain ⟨w, hw, wr⟩ := expectSyntax_complete '"' _ _ _ _ hz vr
    exact finish w (by simp only [getPath, run_bind_of_ok hu]; simp [run_bind, hv, hw]) wr

private theorem pathFailure_complete (O : Oracles) (D : Descriptions) (keyPos : Nat × Nat) :
    FailureComplete (getPath O D keyPos) (IncludePathFailureG O) := by
  rintro c r s ⟨x, y, q, rfl, hm, hf⟩ hs
  obtain ⟨u, hu, ur⟩ := mark_complete '"' _ _ _ _ hm (by rw [hs, List.append_assoc])
  cases q with
  | false =>
    rcases hf with hf | ⟨x, y, p, rfl, hx, rfl, hn⟩
    · obtain ⟨e, t, ht, hr⟩ := expectNontermFailure_complete (token_complete _) (token_failure_complete _)
        D.includePath _ _ _ hf ur
      exact ⟨e, t, by simp only [getPath, run_bind_of_ok hu]; simp [run_bind, ht], hr⟩
    · obtain ⟨v, hv, vr⟩ := expectNonterminal_complete (token_complete _) D.includePath _ _ _ _ hx
        (by simpa using ur)
      have hnl : (v.peek != some '\n') = true := by simpa [Stream.peek_eq_head, vr] using hn
      exact ⟨.fatal ⟨u.getPos, v.getPos⟩ .useQuotesAroundFilenames, v, by
        simp only [getPath, run_bind_of_ok hu]
        simp [run_bind, hv, show v.peek ≠ some '\n' from by simpa using hnl], by simpa using vr⟩
  | true =>
    rcases hf with hf | ⟨x, y, p, rfl, hx, hy⟩
    · obtain ⟨e, t, ht, hr⟩ := expectNontermFailure_complete (token_complete _) (token_failure_complete _)
        D.quotedIncludePath _ _ _ hf ur
      exact ⟨e, t, by simp only [getPath, run_bind_of_ok hu]; simp [run_bind, ht], hr⟩
    · obtain ⟨v, hv, vr⟩ := expectNonterminal_complete (token_complete _) D.quotedIncludePath _ _ _ _ hx
        (by rw [ur, List.append_assoc])
      obtain ⟨e, w, hw, wr⟩ := requiredMarkFailure_complete '"' _ _ _ hy vr
      exact ⟨e, w, by simp only [getPath, run_bind_of_ok hu]; simp [run_bind, hv, hw], wr⟩

private theorem includeKey_complete (O : Oracles) :
    Complete (tryNonterminal (parseOption (token (usernameToken O)))) (IncludeKeyG O) :=
  tryNonterminal_complete (option_complete (token_complete _) (token_rejectComplete _))

theorem include_complete (O : Oracles) (D : Descriptions) {s t : Stream} {a : Sudo}
    (h : IncludeG O s a t) : (parseInclude O D).run s = (.ok a, t) := by
  cases h with
  | file hk hp =>
    simp [parseInclude, run_bind, hk.complete (includeKey_complete O), path_complete O D s.getPos hp]
  | dir hk hp =>
    simp [parseInclude, run_bind, hk.complete (includeKey_complete O), path_complete O D s.getPos hp]

theorem include_failure_complete (O : Oracles) (D : Descriptions) {s t : Stream}
    (h : IncludeFailure O s t) : ∃ e, (parseInclude O D).run s = (.error e, t) := by
  cases h with
  | key hk =>
    obtain ⟨e, he⟩ := hk.failure_complete (tryNontermFailure_complete
      (option_complete (token_complete _) (token_rejectComplete _)) (optionalTokenFailure_complete _))
    exact ⟨e, by simp [parseInclude, run_bind, he]⟩
  | other hk h₁ h₂ =>
    have hr := hk.complete (includeKey_complete O)
    simp only [parseInclude, run_bind_of_ok (run_getPos _), run_bind_of_ok hr]
    exact ⟨.fatal ⟨s.getPos, t.getPos⟩ .unknownDirective, rfl⟩
  | path hk hd hp =>
    obtain ⟨e, he⟩ := hp.failure_complete (pathFailure_complete O D s.getPos)
    rcases hd with rfl | rfl
    · exact ⟨e, by simp [parseInclude, run_bind, hk.complete (includeKey_complete O), he]⟩
    · exact ⟨e, by simp [parseInclude, run_bind, hk.complete (includeKey_complete O), he]⟩

theorem hash_id_failure_complete (O : Oracles) (D : Descriptions) {s t : Stream}
    (h : AtCursor HashIdFailureG s () t) :
    ∃ e, (tryNonterminal (identifier O D)).run s = (.error e, t) := by
  apply h.failure_complete
  intro c r s hc hs
  rcases hc with ⟨x, y, b, rfl, hm, hy⟩ | ⟨x, y, a, rfl, ⟨m, n, b, rfl, hm, hn⟩, hy⟩
  · cases b with
    | false => exact hy.elim
    | true =>
      obtain ⟨u, hu, hr⟩ := mark_complete '#' _ _ _ _ hm (by rw [hs, List.append_assoc])
      obtain ⟨e, v, hv, vr⟩ := expectNontermFailure_complete (token_complete _) (token_failure_complete _)
        D.digitsU32 _ _ _ hy hr
      have hi : (identifier O D).run s = (.error e, v) := by
        simp only [identifier, run_bind_of_ok hu]
        simp [run_bind, hv]
      exact ⟨e, v, by simp [tryNonterminal_run, hi], vr⟩
  · cases b with
    | false => exact hn.elim
    | true =>
      obtain ⟨i, hi, rfl⟩ := hn
      obtain ⟨u, hu, hr⟩ := mark_complete '#' m true (n ++ (y ++ r)) s hm
        (by simpa only [List.append_assoc] using hs)
      obtain ⟨v, hv, vr⟩ := expectNonterminal_complete (token_complete _) D.digitsU32 _ _ _ _ hi hr
      obtain ⟨e, w, hw, wr⟩ := ws_failure_complete _ _ _ hy vr
      have hi' : (identifier O D).run s = (.ok (.id i), v) := by
        simp only [identifier, run_bind_of_ok hu]
        simp [run_bind, hv]
      exact ⟨e, w, by simp [tryNonterminal_run, hi', hw], wr⟩

end SudoersSpec.Grammar
