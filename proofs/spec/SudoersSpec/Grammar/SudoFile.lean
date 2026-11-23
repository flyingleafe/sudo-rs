import SudoersSpec.Grammar.PermissionDispatch
import SudoersSpec.Grammar.SudoAliases
import SudoersSpec.Grammar.SudoInclude
import SudoersSpec.Grammar.SudoSettings
import SudoersSpec.Grammar.SudoUserReject
import SudoersSpec.Syntax.Recovery

/-! PT6 for the stable `Sudo` grammar. The broad permission judgment is soundness-only:
see `PositiveSudoPermissionG` for the smaller grammar with a completeness theorem. -/

namespace SudoersSpec.Grammar

open SudoersSpec.Syntax SudoersSpec.Syntax.Parser

private theorem anchorBind_ok {s₀ s t : Stream} {p : AParser s₀ α} {f : α → AParser s₀ β} {b : β} :
    (p >>= f).run s = (.ok b, t) ↔ ∃ a u, p.run s = (.ok a, u) ∧ (f a).run u = (.ok b, t) := by
  rw [AParser.run_bind]
  rcases h : p.run s with ⟨r, u⟩
  cases r with
  | error e => simp
  | ok a =>
    constructor
    · exact fun hp => ⟨a, u, rfl, hp⟩
    · rintro ⟨a', v, he, hp⟩
      cases he
      exact hp

/-- Since trailing whitespace belongs to tokens, `Defaults:`-style scopes are enabled only
at the original line and eight columns after the start of the keyword search. -/
def DefaultsSuffixPosition (origin current : Stream) : Prop :=
  current.getPos.1 = origin.getPos.1 ∧ current.getPos.2 - origin.getPos.2 = 8

/-- Scope markers other than `@` are tested at the cursor left by the keyword search. -/
inductive DefaultsPunctG (O : Oracles) : Stream → ConfigScope → Stream → Prop where
  | user : AtCursor (SynG ':') s () u → AtCursor (NontermG (UserListG O)) u users t →
      DefaultsPunctG O s (.user users) t
  | command : s.peek ≠ some ':' → AtCursor (SynG '!') s () u →
      AtCursor (NontermG (SimpleCommandListG O)) u cmds t → DefaultsPunctG O s (.command cmds) t
  | runAs : s.peek ≠ some ':' → s.peek ≠ some '!' → AtCursor (SynG '>') s () u →
      AtCursor (NontermG (UserListG O)) u users t → DefaultsPunctG O s (.runAs users) t
  | generic : s.peek ≠ some ':' → s.peek ≠ some '!' → s.peek ≠ some '>' → DefaultsPunctG O s .generic s

/-- The `@` scope rewinds to the original cursor and skips nine source characters. The
keyword search's lookahead may therefore overlap the source of the scope and settings. -/
inductive DefaultsScopeG (O : Oracles) (rest : List Char) (origin current : Stream) :
    ConfigScope → Stream → Prop where
  | host : rest.head? = some '@' → AtCursor WsG (origin.advance 9) () u →
      AtCursor (NontermG (HostListG O.char)) u hosts t → DefaultsScopeG O rest origin current (.host hosts) t
  | punct : rest.head? ≠ some '@' → DefaultsSuffixPosition origin current →
      DefaultsPunctG O current scope t → DefaultsScopeG O rest origin current scope t
  | unscoped : rest.head? ≠ some '@' → ¬ DefaultsSuffixPosition origin current →
      DefaultsScopeG O rest origin current .generic current

private theorem mark_absent {ch : Char} {s t : Stream} (h : (isSyntax ch).run s = (.ok false, t)) :
    t = s ∧ s.peek ≠ some ch := by
  obtain ⟨rfl, hn⟩ := isSyntax_false_iff.mp h
  exact ⟨rfl, fun hh => hn ch hh rfl⟩

private theorem mark_present {ch : Char} {s t : Stream} (h : (isSyntax ch).run s = (.ok true, t)) :
    AtCursor (SynG ch) s () t := (trySyntax_sound ch).atCursor (isSyntax_true_iff.mp h)

private theorem defaultsChosen_sound (O : Oracles) (D : Descriptions) (rest : List Char)
    {s₀ s t : Stream} {scope : ConfigScope}
    (h : ((if rest.head? == some '@' ||
        (s.getPos.1 == s₀.getPos.1 && s.getPos.2 - s₀.getPos.2 == 8)
      then defaultsScope O D rest s₀ else pure .generic : AParser s₀ ConfigScope).run s) = (.ok scope, t)) :
    DefaultsScopeG O rest s₀ s scope t := by
  by_cases ha : rest.head? = some '@'
  · simp only [ha, beq_self_eq_true, Bool.true_or, ite_true, defaultsScope, AParser.run_bind,
      AParser.run_restore, AParser.run_lift, run_advance] at h
    rcases hw : skipTrailingWhitespace.run (s₀.advance 9) with ⟨rr, u⟩
    rw [hw] at h
    cases rr with
    | error _ => cases h
    | ok a =>
      cases a
      simp only at h
      rcases hh : (expectNonterminal D.hostname (specListHostname O.char D)).run u with ⟨rr, v⟩
      rw [hh] at h
      cases rr with
      | error _ => cases h
      | ok hosts =>
        cases h
        exact .host ha (skipTrailingWhitespace_sound.atCursor hw)
          ((expectNonterminal_sound (specList_sound (metaHostname_sound O.char) _ _) _).atCursor hh)
  · have hb : (rest.head? == some '@') = false := by simpa using ha
    by_cases hpos : DefaultsSuffixPosition s₀ s
    · obtain ⟨hl, hc⟩ := hpos
      simp only [hb, Bool.false_or, hl, hc, beq_self_eq_true, Bool.and_self, ite_true, defaultsScope,
        Bool.false_eq_true, ite_false, AParser.run_bind, AParser.run_lift] at h
      apply DefaultsScopeG.punct ha ⟨hl, hc⟩
      rcases hcolon : (isSyntax ':').run s with ⟨colon, u⟩
      rw [hcolon] at h
      cases colon with
      | error _ => cases h
      | ok colon =>
        cases colon
        · obtain ⟨hu, hn⟩ := mark_absent hcolon
          subst u
          simp only [Bool.false_eq_true, ite_false, AParser.run_bind, AParser.run_lift] at h
          rcases hbang : (isSyntax '!').run s with ⟨bang, u⟩
          rw [hbang] at h
          cases bang with
          | error _ => cases h
          | ok bang =>
            cases bang
            · obtain ⟨hu, hb⟩ := mark_absent hbang
              subst u
              simp only [Bool.false_eq_true, ite_false, AParser.run_bind, AParser.run_lift] at h
              rcases hgt : (isSyntax '>').run s with ⟨gt, u⟩
              rw [hgt] at h
              cases gt with
              | error _ => cases h
              | ok gt =>
                cases gt
                · obtain ⟨hu, hg⟩ := mark_absent hgt
                  subst u
                  cases h
                  exact .generic hn hb hg
                · simp only [ite_true, AParser.run_bind, AParser.run_lift] at h
                  rcases hu : (expectNonterminal D.userSpecifier (specListUserSpecifier O D)).run u with ⟨rs, v⟩
                  rw [hu] at h
                  cases rs with
                  | error _ => cases h
                  | ok users =>
                    cases h
                    exact .runAs hn hb (mark_present hgt)
                      ((expectNonterminal_sound (userList_sound O D) _).atCursor hu)
            · simp only [ite_true, AParser.run_bind, AParser.run_lift] at h
              rcases hu : (expectNonterminal D.simpleCommand (specListSimpleCommand O D)).run u with ⟨rs, v⟩
              rw [hu] at h
              cases rs with
              | error _ => cases h
              | ok cmds =>
                cases h
                exact .command hn (mark_present hbang)
                  ((expectNonterminal_sound (simpleCommandList_sound O D) _).atCursor hu)
        · simp only [ite_true, AParser.run_bind, AParser.run_lift] at h
          rcases hu : (expectNonterminal D.userSpecifier (specListUserSpecifier O D)).run u with ⟨rs, v⟩
          rw [hu] at h
          cases rs with
          | error _ => cases h
          | ok users =>
            cases h
            exact .user (mark_present hcolon) ((expectNonterminal_sound (userList_sound O D) _).atCursor hu)
    · have hf : (s.getPos.1 == s₀.getPos.1 && s.getPos.2 - s₀.getPos.2 == 8) = false := by
        simpa [DefaultsSuffixPosition, Bool.and_eq_true] using hpos
      simp only [hb, Bool.false_or, hf, Bool.false_eq_true, ite_false, AParser.run_pure,
        Prod.mk.injEq, Except.ok.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact .unscoped ha hpos

/-- Plain, non-negated user name that can enter keyword dispatch. -/
def DirectiveKey (word : String) : Spec UserSpecifier := .allow (.only (.user (.name word)))

/-- Successful decisions selected by a plain first name. The settings/body are checked at
actual cursors, not by parsing the whole declaration again. -/
inductive DirectiveG (O : Oracles) (origin : Stream) : Spec UserSpecifier → Stream → Directive → Stream → Prop where
  | user : AtCursor (UserAliasBodyG O) s d t → DirectiveG O origin (DirectiveKey "User_Alias") s d t
  | host : AtCursor (HostAliasBodyG O) s d t → DirectiveG O origin (DirectiveKey "Host_Alias") s d t
  | command : (word = "Cmnd_Alias" ∨ word = "Cmd_Alias") → AtCursor (CmndAliasBodyG O) s d t →
      DirectiveG O origin (DirectiveKey word) s d t
  | runAs : AtCursor (RunasAliasBodyG O) s d t → DirectiveG O origin (DirectiveKey "Runas_Alias") s d t
  | defaults : "Defaults".toList.isPrefixOf word.toList = true →
      DefaultsScopeG O (word.toList.drop 8) origin s scope u → AtCursor (NontermG (SettingsG O)) u mods t →
      DirectiveG O origin (DirectiveKey word) s (.defaults mods scope) t

theorem directive_sound (O : Oracles) (D : Descriptions) {s₀ s t : Stream} {key : Spec UserSpecifier}
    {d : Directive} (h : (getDirective O D key s₀).run s = (.ok d, t)) : DirectiveG O s₀ key s d t := by
  unfold getDirective at h
  split at h
  · rename_i word
    split at h
    · exact .user ((userAliasBody_sound O D).atCursor h)
    · exact .host ((hostAliasBody_sound O D).atCursor h)
    · exact .command (.inl rfl) ((cmndAliasBody_sound O D).atCursor h)
    · exact .command (.inr rfl) ((cmndAliasBody_sound O D).atCursor h)
    · exact .runAs ((runasAliasBody_sound O D).atCursor h)
    · split at h
      · rename_i hpref
        obtain ⟨pos, u, hp, h⟩ := anchorBind_ok.mp h
        simp only [AParser.run_lift, run_getPos, Prod.mk.injEq, Except.ok.injEq] at hp
        obtain ⟨rfl, rfl⟩ := hp
        have finish (scope : ConfigScope) (u : Stream)
            (hs : DefaultsScopeG O (word.toList.drop 8) s₀ s scope u)
            (hf : (do
              let mods ← (expectNonterminal D.settingsModifier
                (parseVec settingsModifierMany D.settingsModifier (settingsModifier O D)) : Parser _)
              pure (.defaults mods scope) : AParser s₀ Directive).run u = (.ok d, t)) :
            DirectiveG O s₀ (DirectiveKey word) s d t := by
          obtain ⟨mods, v, hm, he⟩ := anchorBind_ok.mp hf
          cases he
          exact .defaults hpref hs ((expectNonterminal_sound (settings_sound O D) _).atCursor hm)
        by_cases hs : ((word.toList.drop 8).head? == some '@' ||
            (s.getPos.1 == s₀.getPos.1 && s.getPos.2 - s₀.getPos.2 == 8)) = true
        · simp only [hs, ite_true] at h
          obtain ⟨scope, u, hscope, hbody⟩ := anchorBind_ok.mp h
          exact finish scope u (defaultsChosen_sound O D _ (by simpa only [hs, ite_true] using hscope)) hbody
        · simp only [hs] at h
          obtain ⟨scope, u, hscope, hbody⟩ := anchorBind_ok.mp h
          exact finish scope u (defaultsChosen_sound O D _
            (by simpa only [hs, Bool.false_eq_true, ite_false] using hscope)) hbody
      · cases h
  · cases h

/-- The non-special starting characters of the directive/user probe. -/
def OrdinaryStart (s : Stream) : Prop :=
  NextNot (fun c => c = '@' ∨ c = '#' ∨ c = '"') s.rest

/-- Independent item grammar for all stable `Sudo` AST forms. An ordinary comment is the
rejection of the user-list probe; on the hash branch a failed id and failed include instead
skip the rest of the physical line, starting at the failure cursor. -/
inductive SudoForm (O : Oracles) : Stream → Sudo → Stream → Prop where
  | permission : AtCursor (SudoPermissionG O) s p t → SudoForm O s (.spec p) t
  | atInclude : s.peek = some '@' → IncludeG O s.pop a t → SudoForm O s a t
  | hashInclude : s.peek = some '#' → AtCursor HashIdFailureG s () u → IncludeG O u a t → SudoForm O s a t
  | hashComment : s.peek = some '#' → AtCursor HashIdFailureG s () u → IncludeFailure O u v →
      SudoForm O s .lineComment v.skipToNewline
  | ordinaryComment : OrdinaryStart s → AtCursor (UserListRejectG O) s () t → SudoForm O s .lineComment t
  | declaration : OrdinaryStart s → AtCursor (NontermG (UserListG O)) s users u →
      DirectiveG O s (users.headD (.allow .all)) u d t →
      (users.length = 1 ∨ d.couldBeUsername = false) → SudoForm O s (.decl d) t

/-- The net source interval advances from the original cursor, even for host-scoped Defaults
which have a separate, overlapping lookahead. -/
def SudoG (O : Oracles) (s : Stream) (a : Sudo) (t : Stream) : Prop :=
  s.Reaches t ∧ SudoForm O s a t

private theorem ordinaryStart {s : Stream} (ha : s.peek ≠ some '@') (hh : s.peek ≠ some '#')
    (hq : s.peek ≠ some '"') : OrdinaryStart s := by
  intro c hc he
  rcases he with rfl | rfl | rfl
  · exact ha hc
  · exact hh hc
  · exact hq hc

private theorem hash_nonpermission (O : Oracles) (D : Descriptions) {s t : Stream} {a : Sudo}
    (hh : s.peek = some '#') (h : (sudoHash O D).run s = (.ok a, t))
    (np : ∀ p, a ≠ .spec p) : SudoForm O s a t := by
  simp only [sudoHash, run_bind, run_observe] at h
  rcases hi : (tryNonterminal (identifier O D)).run s with ⟨res, u⟩
  rw [hi] at h
  cases res with
  | ok id =>
    simp only at h
    obtain ⟨b, v, _, h⟩ := run_bind_eq_ok.mp h
    have no (users : SpecList UserSpecifier) (u : Stream)
        (hf : (do
          let perms ← expectNonterminal D.hostsRunasCommands (permissions O D)
          pure (Sudo.spec ⟨users, perms⟩)).run u = (.ok a, t)) : False := by
      obtain ⟨perms, w, _, he⟩ := run_bind_eq_ok.mp hf
      simp only [run_pure, Prod.mk.injEq, Except.ok.injEq] at he
      exact np _ he.1.symm
    cases b
    · simp only [Bool.false_eq_true, ite_false, run_bind_of_ok (run_pure _ _)] at h
      exact (no _ _ h).elim
    · simp only [ite_true] at h
      obtain ⟨users, w, _, h⟩ := run_bind_eq_ok.mp h
      simp only [run_bind_of_ok (run_pure _ _)] at h
      exact (no _ _ h).elim
  | error e =>
    have hid := hash_id_failure O D hh hi
    simp only [run_bind, run_observe] at h
    rcases hk : (parseInclude O D).run u with ⟨inc, v⟩
    rw [hk] at h
    cases inc with
    | ok a' =>
      cases h
      exact .hashInclude hh hid (include_sound O D hk)
    | error e' =>
      simp only [run_bind, run_skipToNewline, run_pure, Prod.mk.injEq, Except.ok.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact .hashComment hh hid (include_failure O D hk)

private theorem main_nonpermission (O : Oracles) (D : Descriptions) {s t : Stream} {a : Sudo}
    (ha : s.peek ≠ some '@') (hh : s.peek ≠ some '#') (h : (sudoMain O D s).run s = (.ok a, t))
    (np : ∀ p, a ≠ .spec p) : SudoForm O s a t := by
  by_cases hq : s.peek = some '"'
  · simp only [sudoMain, AParser.run_bind, AParser.run_lift, run_peek, hq, beq_self_eq_true, ite_true] at h
    rcases hu : (expectNonterminal D.userSpecifier (specListUserSpecifier O D)).run s with ⟨rs, u⟩
    rw [hu] at h
    cases rs with
    | error _ => cases h
    | ok users =>
      simp only at h
      rcases hp : (expectNonterminal D.hostsRunasCommands (permissions O D)).run u with ⟨rs, v⟩
      rw [hp] at h
      cases rs with
      | error _ => cases h
      | ok perms =>
        simp only [AParser.run_pure, Prod.mk.injEq, Except.ok.injEq] at h
        exact (np _ h.1.symm).elim
  · have hqb : (s.peek == some '"') = false := by simpa using hq
    have ho := ordinaryStart ha hh hq
    simp only [sudoMain, AParser.run_bind, AParser.run_lift, run_peek, hqb, Bool.false_eq_true,
      ite_false, run_maybe] at h
    rcases hu : (tryNonterminal (specListUserSpecifier O D)).run s with ⟨rs, u⟩
    rw [hu] at h
    cases rs with
    | error e =>
      cases e with
      | fatal _ _ => cases h
      | reject =>
        simp only [maybe_reject, AParser.run_pure, Prod.mk.injEq, Except.ok.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨c, hc, hg⟩ := userList_reject_sound O D _ _ hu
        exact .ordinaryComment ho (AtCursor.of_run hu hc hg)
    | ok users =>
      simp only [maybe_ok, AParser.run_bind, AParser.run_maybe] at h
      rcases hd : (getDirective O D (users.headD (.allow .all)) s).run u with ⟨rs, v⟩
      rw [hd] at h
      cases rs with
      | error e =>
        cases e with
        | fatal _ _ => cases h
        | reject =>
          simp only [maybe_reject, AParser.run_bind, AParser.run_lift] at h
          rcases hp : (expectNonterminal D.hostsRunasCommands (permissions O D)).run v with ⟨rs, w⟩
          rw [hp] at h
          cases rs with
          | error _ => cases h
          | ok perms =>
            simp only [AParser.run_pure, Prod.mk.injEq, Except.ok.injEq] at h
            exact (np _ h.1.symm).elim
      | ok d =>
        simp only [maybe_ok] at h
        split at h
        · simp at h
        · rename_i hguard
          simp only [AParser.run_pure, Prod.mk.injEq, Except.ok.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          refine .declaration ho ((tryNonterminal_sound (userList_sound O D)).atCursor hu)
            (directive_sound O D hd) ?_
          by_cases hn : users.length = 1
          · exact .inl hn
          · right
            cases hc : d.couldBeUsername with
            | false => rfl
            | true => exact (hguard (by simp [hn, hc])).elim

/-- Single-item soundness for the actual stable parser, for every start position. -/
theorem sudo_sound (O : Oracles) (D : Descriptions) {s t : Stream} {a : Sudo}
    (h : (sudo O D).run s = (.ok a, t)) : SudoG O s a t := by
  refine ⟨reaches_of_run h, ?_⟩
  by_cases hs : ∃ p, a = .spec p
  · obtain ⟨p, rfl⟩ := hs
    exact .permission (sudo_permission_sound O D h)
  · have np : ∀ p, a ≠ .spec p := fun p he => hs ⟨p, he⟩
    simp only [sudo, run_bind, run_eatChar, Stream.eatChar_eq] at h
    by_cases ha : s.peek = some '@'
    · simp only [ha, ite_true] at h
      exact .atInclude ha (include_sound O D h)
    · simp only [ha, ite_false, Bool.false_eq_true, run_bind, run_peek] at h
      by_cases hh : s.peek = some '#'
      · simp only [hh, beq_self_eq_true, ite_true] at h
        exact hash_nonpermission O D hh h np
      · have hb : (s.peek == some '#') = false := by simpa using hh
        simp only [hb, Bool.false_eq_true, ite_false, run_anchored] at h
        exact main_nonpermission O D ha hh h np

/-- The file driver parses a nonterminal: it checks trailing whitespace once more after the
item production, including after a comment produced by a rejected user-list probe. -/
def SudoItemG (O : Oracles) (s : Stream) (a : Sudo) (t : Stream) : Prop :=
  ∃ u, SudoG O s a u ∧ AtCursor WsG u () t

theorem SudoItemG.reaches {O : Oracles} {s t : Stream} {a : Sudo} (h : SudoItemG O s a t) :
    s.Reaches t := by
  obtain ⟨_, hs, ht⟩ := h
  exact hs.1.trans ht.reaches

/-- The single-item premise of `Recovery.cleanFile_sound`. -/
theorem sudo_item_sound (O : Oracles) (D : Descriptions) (s : Stream) (a : Sudo) (t : Stream)
    (h : (expectNonterminal D.sudo (sudo O D)).run s = (.ok a, t)) : SudoItemG O s a t := by
  obtain ⟨b, u, hp, hws⟩ := run_bind_eq_ok.mp (expectNonterminal_ok_iff.mp h)
  obtain ⟨_, v, hw, he⟩ := run_bind_eq_ok.mp hws
  cases he
  exact ⟨u, sudo_sound O D hp, skipTrailingWhitespace_sound.atCursor hw⟩

/-- The public file wrapper returns the driver's output when it reports success; the
driver advances across the entire source, including any final blanks. -/
theorem parseSudoersWith_ok_lines (D : Descriptions) (O : Oracles) (src : List Char)
    {items : List (Parsed Sudo)} (h : parseSudoersWith D O src = .ok items) :
    (parseLines D.sudo (sudo O D)).run (Stream.new src) =
      (.ok items, (Stream.new src).advance src.length) := by
  obtain ⟨rs, hr, _⟩ := parseLines_ok D.sudo (sudo O D) (Stream.new src)
  simp only [parseSudoersWith, hr] at h
  split at h
  · cases h
  · cases h
    exact Prod.ext hr (Recovery.parseLines_end D.sudo (sudo O D) (Stream.new src))

/-- PT6: if the stable parser reports only successes, the file has a grammar derivation whose
final cursor accounts for every source character. The driver permits final horizontal blanks
and separates each item from any trailing comment and its physical newline. -/
theorem parseSudoersWith_clean_sound (D : Descriptions) (O : Oracles) (src : List Char)
    (items : List Sudo) (h : parseSudoersWith D O src = .ok (items.map Except.ok)) :
    Recovery.CleanFile (SudoItemG O) (Stream.new src) items ((Stream.new src).advance src.length) :=
  Recovery.cleanFile_sound (sudo_item_sound O D) (parseSudoersWith_ok_lines D O src h)

/-- Explicit source accounting for one clean-file step: leading blanks, the item, an optional
comment, a newline, and the remaining file. The `CleanFile.eof` rule covers the final blanks. -/
theorem sudo_clean_step_partition {O : Oracles} {s t : Stream} {a : Sudo}
    (item : SudoItemG O (Recovery.afterBlanks s) a t) (nl : (Recovery.afterComment t).peek = some '\n') :
    s.rest = s.rest.takeWhile blank ++ (Recovery.between (Recovery.afterBlanks s) t ++
      (Recovery.between t (Recovery.afterComment t) ++ '\n' :: (Recovery.afterComment t).pop.rest)) := by
  have hb : s.rest = s.rest.takeWhile blank ++ (Recovery.afterBlanks s).rest := by
    rw [Recovery.afterBlanks, blank_eq, Stream.skipWhile_rest, List.takeWhile_append_dropWhile]
  have hi : (Recovery.afterBlanks s).rest = Recovery.between (Recovery.afterBlanks s) t ++ t.rest :=
    item.reaches.getPos_eq.1
  have hc : t.Reaches (Recovery.afterComment t) := by
    unfold Recovery.afterComment
    split
    · exact (Stream.Reaches.pop t).trans (Stream.Reaches.skipWhile _ _)
    · exact .refl t
  have he : t.rest = Recovery.between t (Recovery.afterComment t) ++ (Recovery.afterComment t).rest :=
    hc.getPos_eq.1
  exact hb.trans (congrArg (s.rest.takeWhile blank ++ ·) (hi.trans
    (congrArg (Recovery.between (Recovery.afterBlanks s) t ++ ·) (he.trans
      (congrArg (Recovery.between t (Recovery.afterComment t) ++ ·) (Stream.rest_of_peek nl))))))

/-- The terminal clean-file rule consumes exactly the final horizontal blanks. -/
theorem sudo_clean_eof_partition {s : Stream} (h : (Recovery.afterBlanks s).rest = []) :
    s.rest = s.rest.takeWhile blank := by
  rw [Recovery.afterBlanks, blank_eq, Stream.skipWhile_rest] at h
  simpa only [h, List.append_nil] using
    (List.takeWhile_append_dropWhile (p := blank) (l := s.rest)).symm

end SudoersSpec.Grammar
