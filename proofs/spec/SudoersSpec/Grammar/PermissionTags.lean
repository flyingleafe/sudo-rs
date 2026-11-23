import SudoersSpec.Grammar.PermissionRunAs

namespace SudoersSpec.Grammar

open SudoersSpec.Syntax SudoersSpec.Syntax.Parser

/-! ## Keyword discrimination and tag values -/

private abbrev tagSwitch (m : Modifier) : Parser (Meta Modifier) :=
  MapP (expectSyntax ':') (fun _ => .only m)

private abbrev tagPayload (desc : String) (T : TokenSpec α) (f : α → Modifier) : Parser (Meta Modifier) := do
  expectSyntax '='
  MapP (expectNonterminal desc (token T)) (fun a => .only (f a))

private abbrev colonTagG (m : Modifier) : Gram (Meta Modifier) :=
  MapG (SynG ':') (fun _ => .only m)

private abbrev payloadTagG (T : TokenSpec α) (f : α → Modifier) : Gram (Meta Modifier) :=
  SeqG (SynG '=') fun _ => MapG (NontermG (TokenG T)) (fun a => .only (f a))

/-- The continuation decided by the maximal `NAME` token. The span is observed immediately
before its `:` in the ignored case; ordinary tags carry no positions in the AST. -/
def TagRhsG (O : Oracles) (span : Span) (keyword : String) : Gram (Meta Modifier) :=
  match keyword with
  | "EXEC" => colonTagG .exec
  | "NOEXEC" => colonTagG .noexec
  | "SETENV" => colonTagG .setenv
  | "NOSETENV" => colonTagG .nosetenv
  | "PASSWD" => colonTagG .passwd
  | "NOPASSWD" => colonTagG .nopasswd
  | "CWD" => payloadTagG (chDirToken O) Modifier.cwd
  | "INTERCEPT" | "CHROOT" | "TIMEOUT" | "NOTBEFORE" | "NOTAFTER" => EmptyG
  | "ROLE" | "TYPE" => EmptyG
  | "LOG_INPUT" | "NOLOG_INPUT" | "LOG_OUTPUT" | "NOLOG_OUTPUT" | "MAIL" | "NOMAIL" | "FOLLOW" =>
      colonTagG (.ignored span)
  | "NOFOLLOW" | "NOINTERCEPT" => colonTagG .noop
  | "APPARMOR_PROFILE" => payloadTagG (stringParameterToken O.char) Modifier.apparmorProfile
  | "ALL" => PureG .all
  | alias => fun c a r => c = [] ∧ a = .alias alias ∧ NextNot (· = '=') r

private def tagRhs (O : Oracles) (D : Descriptions) (start : Nat × Nat) (keyword : String) :
    Parser (Meta Modifier) :=
  match keyword with
  | "EXEC" => tagSwitch .exec
  | "NOEXEC" => tagSwitch .noexec
  | "SETENV" => tagSwitch .setenv
  | "NOSETENV" => tagSwitch .nosetenv
  | "PASSWD" => tagSwitch .passwd
  | "NOPASSWD" => tagSwitch .nopasswd
  | "CWD" => tagPayload D.chDir (chDirToken O) Modifier.cwd
  | "INTERCEPT" | "CHROOT" | "TIMEOUT" | "NOTBEFORE" | "NOTAFTER" => fatalFrom start (.notSupported keyword)
  | "ROLE" | "TYPE" => fatalFrom start .selinuxNotSupported
  | "LOG_INPUT" | "NOLOG_INPUT" | "LOG_OUTPUT" | "NOLOG_OUTPUT" | "MAIL" | "NOMAIL" | "FOLLOW" => do
      let here ← getPos
      tagSwitch (.ignored ⟨start, here⟩)
  | "NOFOLLOW" | "NOINTERCEPT" => tagSwitch .noop
  | "APPARMOR_PROFILE" => tagPayload D.stringParameter (stringParameterToken O.char) Modifier.apparmorProfile
  | "ALL" => pure .all
  | alias => do
      if ← isSyntax '=' then fatalFrom start (.unsupportedModifier alias) else pure (.alias alias)

private theorem eq_metaOrTag (O : Oracles) (D : Descriptions) : metaOrTag O D = (do
    let start ← getPos
    let keyword ← tryNonterminal (token aliasNameToken)
    tagRhs O D start keyword) := by
  rfl

private theorem tagSwitch_sound (m : Modifier) : Sound (tagSwitch m) (colonTagG m) :=
  mapP_sound (expectSyntax_sound ':') _

private theorem tagSwitch_complete (m : Modifier) : Complete (tagSwitch m) (colonTagG m) :=
  mapP_complete (expectSyntax_complete ':') _

private theorem tagPayload_sound (desc : String) (T : TokenSpec α) (f : α → Modifier) :
    Sound (tagPayload desc T f) (payloadTagG T f) :=
  seq_sound (expectSyntax_sound '=') (fun _ => mapP_sound (expectNonterminal_sound (token_sound T) desc) _)

private theorem tagPayload_complete (desc : String) (T : TokenSpec α) (f : α → Modifier) :
    Complete (tagPayload desc T f) (payloadTagG T f) :=
  seq_complete (expectSyntax_complete '=') (fun _ => mapP_complete (expectNonterminal_complete (token_complete T) desc) _)

private abbrev tagAlias (start : Nat × Nat) (keyword : String) : Parser (Meta Modifier) := do
  if ← isSyntax '=' then fatalFrom start (.unsupportedModifier keyword) else pure (.alias keyword)

private theorem tagAlias_sound (start : Nat × Nat) (keyword : String) :
    Sound (tagAlias start keyword)
      (fun c a r => c = [] ∧ a = .alias keyword ∧ NextNot (· = '=') r) := by
  intro s a s' h
  obtain ⟨b, t, h₁, h₂⟩ := run_bind_eq_ok.mp h
  cases b with
  | false =>
    obtain ⟨rfl, hn⟩ := isSyntax_false_iff.mp h₁
    simp at h₂
    obtain ⟨he, rfl⟩ := h₂
    exact ⟨[], rfl, rfl, he.symm, hn⟩
  | true => simp at h₂

private theorem tagAlias_complete (start : Nat × Nat) (keyword : String) :
    Complete (tagAlias start keyword)
      (fun c a r => c = [] ∧ a = .alias keyword ∧ NextNot (· = '=') r) := by
  rintro c a r s ⟨rfl, rfl, hn⟩ hs
  have h : (isSyntax '=').run s = (.ok false, s) :=
    isSyntax_false_iff.mpr ⟨rfl, by rw [hs]; exact hn⟩
  exact ⟨s, by simp only [tagAlias, run_bind, h]; rfl, hs⟩

private theorem tagRhs_sound (O : Oracles) (D : Descriptions) (start : Nat × Nat) (keyword : String)
    (s : Stream) {a : Meta Modifier} {s' : Stream} (h : (tagRhs O D start keyword).run s = (.ok a, s')) :
    ∃ c, s.rest = c ++ s'.rest ∧ TagRhsG O ⟨start, s.getPos⟩ keyword c a s'.rest := by
  unfold tagRhs at h
  unfold TagRhsG
  split at h
  all_goals first
    | exact tagSwitch_sound _ s a s' h
    | exact tagPayload_sound _ _ _ s a s' h
    | exact pure_sound (.all : Meta Modifier) s a s' h
    | exact tagAlias_sound start keyword s a s' h
    | exact False.elim (by simp at h)
    | simp only [run_bind, run_getPos] at h; exact tagSwitch_sound _ s a s' h

/-- The structural grammar can tell that a tag carries an ignored source span, but the
positive printer never emits those tags. -/
def SpanFreeTag : Meta Modifier → Prop
  | .only (.ignored _) => False
  | _ => True

private theorem tagRhs_complete (O : Oracles) (D : Descriptions) (span : Span) (keyword : String)
    (start : Nat × Nat) {c : List Char} {a : Meta Modifier} {r : List Char} {s : Stream}
    (ha : SpanFreeTag a) (hd : TagRhsG O span keyword c a r) (hs : s.rest = c ++ r) :
    ∃ t, (tagRhs O D start keyword).run s = (.ok a, t) ∧ t.rest = r := by
  unfold TagRhsG at hd
  unfold tagRhs
  split at hd
  all_goals first
    | exact tagSwitch_complete _ c a r s hd hs
    | exact tagPayload_complete _ _ _ c a r s hd hs
    | exact pure_complete (.all : Meta Modifier) c a r s hd hs
    | exact tagAlias_complete start keyword c a r s hd hs
    | exact False.elim hd
    | obtain ⟨x, hx, rfl⟩ := hd; exact False.elim ha

private theorem fatal_not_reject (start : Nat × Nat) (kind : ErrKind) (s : Stream) :
    ((fatalFrom start kind : Parser α).run s).1 ≠ .error .reject := by simp

private theorem mapP_not_reject {p : Parser α} (f : α → β) (s : Stream)
    (h : (p.run s).1 ≠ .error .reject) : ((MapP p f).run s).1 ≠ .error .reject := by
  simp only [run_bind]
  rcases he : p.run s with ⟨a, t⟩
  rw [he] at h
  cases a with
  | ok a => simp
  | error e => simpa using h

private theorem expectSyntax_not_reject (ch : Char) (s : Stream) :
    ((expectSyntax ch).run s).1 ≠ .error .reject := by
  simp only [expectSyntax, run_bind, run_observe]
  split <;> simp [run_bind]

private theorem tagSwitch_not_reject (m : Modifier) (s : Stream) :
    ((tagSwitch m).run s).1 ≠ .error .reject :=
  mapP_not_reject _ s (expectSyntax_not_reject ':' s)

private theorem tagPayload_not_reject (desc : String) (T : TokenSpec α) (f : α → Modifier)
    (s : Stream) : ((tagPayload desc T f).run s).1 ≠ .error .reject := by
  intro h
  have he : (tagPayload desc T f).run s = (.error .reject, ((tagPayload desc T f).run s).2) := Prod.ext h rfl
  rcases run_bind_eq_error.mp he with h₁ | ⟨_, t, _, h₂⟩
  · exact expectSyntax_not_reject '=' s (congrArg Prod.fst h₁)
  · rcases run_bind_eq_error.mp h₂ with h₂ | ⟨_, _, _, h₂⟩
    · exact expectNonterminal_ne_reject desc (token T) t (congrArg Prod.fst h₂)
    · simp at h₂

private theorem tagRhs_not_reject (O : Oracles) (D : Descriptions) (start : Nat × Nat) (keyword : String)
    (s : Stream) : ((tagRhs O D start keyword).run s).1 ≠ .error .reject := by
  unfold tagRhs
  split
  case h_1 | h_2 | h_3 | h_4 | h_5 | h_6 | h_22 | h_23 =>
    exact tagSwitch_not_reject _ _
  case h_7 | h_24 => exact tagPayload_not_reject _ _ _ _
  case h_8 | h_9 | h_10 | h_11 | h_12 | h_13 | h_14 => exact fatal_not_reject _ _ _
  case h_15 | h_16 | h_17 | h_18 | h_19 | h_20 | h_21 =>
    simp only [run_bind, run_getPos]
    exact tagSwitch_not_reject _ _
  case h_25 => simp
  case h_26 =>
    intro h
    have e : (tagAlias start keyword).run s =
        (.error .reject, ((tagAlias start keyword).run s).2) := Prod.ext h rfl
    rcases run_bind_eq_error.mp e with hp | ⟨b, t, _, hb⟩
    · exact isSyntax_ne_reject '=' s (congrArg Prod.fst hp)
    · cases b <;> simp at hb

/-- A maximal alias token and its whitespace, then the rhs selected by the name. Ignored tag
spans are constrained locally: the stop is the position after the keyword and its whitespace
from the recorded start. The ambient position equation of the complete run is separate. -/
def MetaTagG (O : Oracles) : Gram (Meta Modifier) :=
  fun c a r => ∃ key kw body start, c = kw ++ body ∧ NontermG AliasNameG kw key (body ++ r) ∧
    TagRhsG O ⟨start, posAfter kw start⟩ key body a r

abbrev CleanMetaTagG (O : Oracles) : Gram (Meta Modifier) :=
  fun c a r => MetaTagG O c a r ∧ SpanFreeTag a

theorem metaOrTag_sound (O : Oracles) (D : Descriptions) : Sound (metaOrTag O D) (MetaTagG O) := by
  intro s a s' h
  rw [eq_metaOrTag] at h
  simp only [run_bind_of_ok (run_getPos s)] at h
  obtain ⟨kw, t, ht, hr⟩ := run_bind_eq_ok.mp h
  obtain ⟨x, hx, hg, hp⟩ := (tryNonterminal_sound aliasName_sound).pos ht
  obtain ⟨y, hy, hk⟩ := tagRhs_sound O D s.getPos kw t hr
  refine ⟨x ++ y, by rw [hx, hy, List.append_assoc], kw, x, y, s.getPos, rfl, ?_, ?_⟩
  · rw [← hy]; exact hg
  · rw [← hp]; exact hk

theorem metaOrTag_complete (O : Oracles) (D : Descriptions) :
    Complete (metaOrTag O D) (CleanMetaTagG O) := by
  rintro c a r s ⟨⟨kw, x, y, start, rfl, hg, hk⟩, ha⟩ hs
  obtain ⟨t, ht, tr⟩ := tryNonterminal_complete aliasName_complete _ _ _ _ hg
    (by rw [hs, List.append_assoc])
  obtain ⟨u, hu, ur⟩ := tagRhs_complete O D _ kw s.getPos ha hk tr
  exact ⟨u, by rw [eq_metaOrTag, run_bind_of_ok (run_getPos s), run_bind_of_ok ht, hu], ur⟩

abbrev TagRejectG : Gram Unit := fun c _ r => c = [] ∧ NextNot (fun d => AliasName.accept1st d = true) r

theorem metaOrTag_rejectSound (O : Oracles) (D : Descriptions) : RejectSound (metaOrTag O D) TagRejectG := by
  intro s t h
  rw [eq_metaOrTag, run_bind_of_ok (run_getPos s)] at h
  rcases run_bind_eq_error.mp h with he | ⟨kw, u, _, he⟩
  · have htok := tryNonterminal_reject.mp he
    rcases token_reject aliasNameToken htok with ⟨rfl, hstop⟩ | ⟨hesc, _⟩
    · exact ⟨[], rfl, rfl, (escStop_noEsc rfl).mp hstop⟩
    · cases hesc.1
  · exact False.elim (tagRhs_not_reject O D s.getPos kw u (congrArg Prod.fst he))

theorem metaOrTag_rejectComplete (O : Oracles) (D : Descriptions) :
    RejectComplete (metaOrTag O D) TagRejectG := by
  rintro c r s ⟨rfl, hn⟩ hs
  have htok : (token aliasNameToken).run s = (.error .reject, s) := by
    rw [token_run, acceptEscaped_stop _ _ ((escStop_noEsc rfl).mpr (hs.symm ▸ hn))]
  exact ⟨s, by rw [eq_metaOrTag, run_bind_of_ok (run_getPos s),
    run_bind_of_error (tryNonterminal_reject.mpr htok)], hs⟩

end SudoersSpec.Grammar
