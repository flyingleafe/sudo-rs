import SudoersSpec.Analysis.Collect
import SudoersSpec.Grammar.Lexical
import SudoersSpec.Grammar.Token
import SudoersSpec.Syntax.Recovery

/-! Accepted Defaults modifiers come from the settings table. The invariant follows the
reference parser through recovery, collection and the two ordered scope passes. -/

namespace SudoersSpec.Settings

open Syntax Syntax.Parser

private theorem pure_value {a b : α} {s s' : Stream}
    (h : (pure a : Parser α).run s = (.ok b, s')) : a = b := by
  exact (Prod.mk.inj h).1 |> Except.ok.inj

private theorem listItems_produced {O : Oracles} {D : Descriptions} {pos : Nat × Nat}
    {mode : ListMode} {nm : String} {cfg : SettingKind} {s s' : Stream} {m : SettingsModifier}
    (h : (listItems O D pos mode nm cfg).run s = (.ok m, s')) : Produced m := by
  obtain ⟨_, _, _, h⟩ := run_bind_eq_ok.mp h
  cases cfg with
  | List id =>
    obtain ⟨items, _, _, h⟩ := run_bind_eq_ok.mp h
    exact .list (pure_value h)
  | _ => simp at h

/-- Every modifier accepted by the reference parser is produced by the corresponding DSL
operation. This is about actual parser calls, not arbitrary AST values. -/
theorem settingsModifier_produced (O : Oracles) (D : Descriptions) {s s' : Stream}
    {m : SettingsModifier} (h : (settingsModifier O D).run s = (.ok m, s')) : Produced m := by
  unfold settingsModifier at h
  obtain ⟨pos, _, _, h⟩ := run_bind_eq_ok.mp h
  obtain ⟨bang, _, _, h⟩ := run_bind_eq_ok.mp h
  split at h
  · obtain ⟨_, _, _, h⟩ := run_bind_eq_ok.mp h
    obtain ⟨nm, _, _, h⟩ := run_bind_eq_ok.mp h
    split at h
    · rename_i v hv
      rw [← pure_value h]
      exact .negate hv
    · split at h <;> simp at h
  · obtain ⟨nm, _, _, h⟩ := run_bind_eq_ok.mp h
    split at h
    · simp at h
    · rename_i cfg hcfg
      obtain ⟨plus, _, _, h⟩ := run_bind_eq_ok.mp h
      split at h
      · exact listItems_produced h
      · obtain ⟨minus, _, _, h⟩ := run_bind_eq_ok.mp h
        split at h
        · exact listItems_produced h
        · obtain ⟨eq, _, _, h⟩ := run_bind_eq_ok.mp h
          split at h
          · obtain ⟨_, _, _, h⟩ := run_bind_eq_ok.mp h
            cases cfg with
            | Flag _ => simp at h
            | Integer id =>
              obtain ⟨t, _, _, h⟩ := run_bind_eq_ok.mp h
              split at h
              · rename_i v hv
                rw [← pure_value h]
                exact .integer hv
              · simp at h
            | List id =>
              obtain ⟨items, _, _, h⟩ := run_bind_eq_ok.mp h
              exact .list (pure_value h)
            | Text id =>
              obtain ⟨t, _, _, h⟩ := run_bind_eq_ok.mp h
              split at h
              · rename_i v hv
                rw [← pure_value h]
                exact .text hv
              · simp at h
          · cases cfg with
            | Flag v =>
              rw [← pure_value h]
              exact .flag hcfg
            | _ => simp at h

/-! ## Lists of modifiers and directive dispatch -/

private def AllProduced (ms : List SettingsModifier) : Prop := ∀ m ∈ ms, Produced m

private theorem tryNonterminal_value {p : Parser α} {s stop : Stream} {a : α}
    (h : (tryNonterminal p).run s = (.ok a, stop)) :
    ∃ mid, p.run s = (.ok a, mid) := by
  obtain ⟨b, mid, hp, h⟩ := run_bind_eq_ok.mp h
  obtain ⟨_, _, _, h⟩ := run_bind_eq_ok.mp h
  cases pure_value h
  exact ⟨mid, hp⟩

private theorem expectNonterminal_value {p : Parser α} {d : String} {s stop : Stream} {a : α}
    (h : (expectNonterminal d p).run s = (.ok a, stop)) : ∃ mid, p.run s = (.ok a, mid) :=
  tryNonterminal_value (Grammar.expectNonterminal_ok_iff.mp h)

private theorem bytes_ofList_length (cs : List Char) :
    (bytes (String.ofList cs)).length = utf8Len cs := by
  simp [bytes, List.utf8Encode, List.length_flatMap,
    String.length_utf8EncodeChar, utf8Len]

private theorem numeric_char_one_byte {c : Char} (h : numericToken.accept c = true) :
    c.utf8Size = 1 := by
  have h' : isAsciiHexdigit c = true ∨ c = '.' := by
    simpa only [numericToken, Bool.or_eq_true, beq_iff_eq] using h
  rcases h' with h' | rfl
  · apply Char.utf8Size_eq_one_iff.mpr
    simp only [isAsciiHexdigit, isAsciiDigit, Bool.or_eq_true, Bool.and_eq_true,
      decide_eq_true_eq, Char.le_def, UInt32.le_iff_toNat_le] at h' ⊢
    rcases h' with (h' | h') | h'
    all_goals exact Nat.le_trans h'.2 (by decide)
  · rfl

/-- A successful `Numeric` parse, including the actual `expectNonterminal` call of
`settingsModifier`, supplies at most 18 UTF-8 bytes to the checker. -/
theorem numeric_bytes_le {d : String} {s stop : Stream} {t : String}
    (h : (expectNonterminal d (token numericToken)).run s = (.ok t, stop)) :
    (bytes t).length ≤ 18 := by
  obtain ⟨mid, ht⟩ := expectNonterminal_value h
  obtain ⟨cs, _, hg⟩ := Grammar.token_sound numericToken s t mid ht
  obtain ⟨c, tail, rfl, hc, htail, _, hlen, htext⟩ :=
    (Grammar.tokenG_noEsc (T := numericToken) rfl).mp hg
  change Except.ok (ε := ErrKind) (String.ofList (c :: tail)) = Except.ok t at htext
  have he : String.ofList (c :: tail) = t := Except.ok.inj htext
  rw [← he, bytes_ofList_length]
  rcases hlen with rfl | hlen
  · have hc' : numericToken.accept c = true := hc
    simp [utf8Len, numeric_char_one_byte hc']
  · have allAscii : ∀ x ∈ c :: tail, x.utf8Size = 1 := by
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact numeric_char_one_byte hc
      · exact numeric_char_one_byte (htail x hx)
    have hn : c :: tail ≠ [] := by simp
    have last := allAscii ((c :: tail).getLast hn) (List.getLast_mem hn)
    have eq := congrArg utf8Len (List.dropLast_concat_getLast hn)
    rw [Grammar.utf8Len_append] at eq
    simp only [utf8Len, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Nat.add_zero, last] at eq
    change utf8Len ((c :: tail).dropLast) < 18 at hlen
    simp only [utf8Len, List.map_cons, List.sum_cons] at hlen ⊢
    omega

/-- On the lexer's actual output the checked integer producer agrees with the panic-free
checker used in the parser. -/
theorem numeric_checker_run_eq {d : String} {s stop : Stream} {t : String}
    (h : (expectNonterminal d (token numericToken)).run s = (.ok t, stop))
    (id : IntegerSetting) : checkIntegerRun id t = .ok (checkInteger id t) := by
  have hf := fractionalMinutesRun_eq t (numeric_bytes_le h)
  cases id <;> simp [checkIntegerRun, checkInteger, hf]

private theorem settingsVec_produced {O : Oracles} {D : Descriptions} {s s' : Stream}
    {ms : List SettingsModifier}
    (h : (parseVec settingsModifierMany D.settingsModifier (settingsModifier O D)).run s =
      (.ok ms, s')) : AllProduced ms := by
  obtain ⟨first, mid, hf, hl⟩ := run_bind_eq_ok.mp h
  obtain ⟨_, hf⟩ := tryNonterminal_value hf
  have init : AllProduced [first] := by simpa [AllProduced] using settingsModifier_produced O D hf
  have inv := loop_invariant (whileMaybeBody_progressive
      (trySyntax_consumes settingsModifierMany.sep)
      (parseListBody settingsModifierMany.limit D.settingsModifier (settingsModifier O D)) id)
    AllProduced (fun r _ => match r with | .ok ms => AllProduced ms | .error _ => True)
    (by
      intro st s st' stop hst hrun
      obtain ⟨opt, _, _, hrun⟩ := run_bind_eq_ok.mp hrun
      cases opt with
      | none => simp at hrun
      | some _ =>
        simp only [parseListBody] at hrun
        split at hrun
        · simp at hrun
        · obtain ⟨m, _, hm, hrun⟩ := run_bind_eq_ok.mp hrun
          obtain ⟨_, hm⟩ := expectNonterminal_value hm
          simp only [run_pure, Prod.mk.injEq, Except.ok.injEq, Step.next.injEq] at hrun
          rw [← hrun.1]
          intro v hv
          rcases List.mem_append.mp hv with hv | hv
          · exact hst v hv
          · simp only [List.mem_singleton] at hv
            subst v
            exact settingsModifier_produced O D hm)
    (by
      intro st s ms stop hst hrun
      obtain ⟨opt, _, _, hrun⟩ := run_bind_eq_ok.mp hrun
      cases opt with
      | none =>
        simp only [run_pure, Prod.mk.injEq, Except.ok.injEq, Step.done.injEq] at hrun
        exact hrun.1 ▸ hst
      | some _ =>
        simp only [parseListBody] at hrun
        split at hrun
        · simp at hrun
        · obtain ⟨_, _, _, hrun⟩ := run_bind_eq_ok.mp hrun
          simp at hrun)
    (by intros; trivial) [first] mid init
  unfold whileMaybe at hl
  rw [hl] at inv
  exact inv

private theorem anchored_bind_ok {anchor : Stream} {p : AParser anchor α}
    {f : α → AParser anchor β} {s stop : Stream} {b : β}
    (h : (p >>= f).run s = (.ok b, stop)) :
    ∃ a mid, p.run s = (.ok a, mid) ∧ (f a).run mid = (.ok b, stop) := by
  rw [AParser.run_bind] at h
  rcases e : p.run s with ⟨r, mid⟩
  cases r with
  | error _ => rw [e] at h; cases h
  | ok a => exact ⟨a, mid, rfl, by simpa only [e] using h⟩

private theorem anchored_pure_value {anchor s stop : Stream} {a b : α}
    (h : (pure a : AParser anchor α).run s = (.ok b, stop)) : a = b :=
  Except.ok.inj (Prod.mk.inj h).1

private def DirectiveProduced : Directive → Prop
  | .defaults ms _ => AllProduced ms
  | _ => True

private theorem getDirective_produced (O : Oracles) (D : Descriptions) (key : Spec UserSpecifier)
    {anchor s stop : Stream} {d : Directive}
    (h : (getDirective O D key anchor).run s = (.ok d, stop)) : DirectiveProduced d := by
  unfold getDirective at h
  split at h
  · split at h
    any_goals
      obtain ⟨_, _, _, h⟩ := anchored_bind_ok h
      rw [← anchored_pure_value h]
      trivial
    split at h
    · obtain ⟨_, _, _, h⟩ := anchored_bind_ok h
      dsimp only at h
      split at h <;>
        obtain ⟨scope, _, _, h⟩ := anchored_bind_ok h <;>
        obtain ⟨ms, _, hms, h⟩ := anchored_bind_ok h <;>
        rw [← anchored_pure_value h] <;>
        obtain ⟨_, hms⟩ := expectNonterminal_value hms <;>
        exact settingsVec_produced hms
    · simp at h
  · simp at h

private def SudoProduced : Sudo → Prop
  | .decl d => DirectiveProduced d
  | _ => True

private theorem include_produced (O : Oracles) (D : Descriptions) {s stop : Stream} {a : Sudo}
    (h : (parseInclude O D).run s = (.ok a, stop)) : SudoProduced a := by
  unfold parseInclude at h
  obtain ⟨_, _, _, h⟩ := run_bind_eq_ok.mp h
  obtain ⟨_, _, _, h⟩ := run_bind_eq_ok.mp h
  split at h
  · obtain ⟨⟨_, _⟩, _, _, h⟩ := run_bind_eq_ok.mp h
    rw [← pure_value h]
    trivial
  · obtain ⟨⟨_, _⟩, _, _, h⟩ := run_bind_eq_ok.mp h
    rw [← pure_value h]
    trivial
  · simp at h

private theorem hash_produced (O : Oracles) (D : Descriptions) {s stop : Stream} {a : Sudo}
    (h : (sudoHash O D).run s = (.ok a, stop)) : SudoProduced a := by
  unfold sudoHash at h
  obtain ⟨_, _, _, h⟩ := run_bind_eq_ok.mp h
  split at h
  · obtain ⟨comma, _, _, h⟩ := run_bind_eq_ok.mp h
    cases comma <;> simp only [Bool.false_eq_true, ite_false, ite_true, run_bind, run_pure] at h
    all_goals
      repeat' split at h
      all_goals simp only [Prod.mk.injEq, Except.ok.injEq] at h
      all_goals (cases h.1 <;> trivial)
  · obtain ⟨r, mid, hi, h⟩ := run_bind_eq_ok.mp h
    cases r with
    | ok x =>
      rw [← pure_value h]
      simp only [run_observe, Prod.mk.injEq, Except.ok.injEq] at hi
      exact include_produced O D (Prod.ext hi.1 hi.2)
    | error e =>
      obtain ⟨_, _, _, h⟩ := run_bind_eq_ok.mp h
      rw [← pure_value h]
      trivial

private theorem main_produced (O : Oracles) (D : Descriptions) {anchor s stop : Stream}
    {a : Sudo} (h : (sudoMain O D anchor).run s = (.ok a, stop)) : SudoProduced a := by
  unfold sudoMain at h
  obtain ⟨_, _, _, h⟩ := anchored_bind_ok h
  split at h
  · obtain ⟨_, _, _, h⟩ := anchored_bind_ok h
    obtain ⟨_, _, _, h⟩ := anchored_bind_ok h
    rw [← anchored_pure_value h]
    trivial
  · obtain ⟨_, _, _, h⟩ := anchored_bind_ok h
    split at h
    · rw [← anchored_pure_value h]
      trivial
    · dsimp only at h
      obtain ⟨d?, mid, hd, h⟩ := anchored_bind_ok h
      cases d? with
      | none =>
        obtain ⟨_, _, _, h⟩ := anchored_bind_ok h
        rw [← anchored_pure_value h]
        trivial
      | some d =>
        simp only at h
        split at h
        · simp only [AParser.run_lift, run_fatalFrom] at h
          cases h
        · simp only [AParser.run_pure, Prod.mk.injEq, Except.ok.injEq] at h
          rw [← h.1]
          change DirectiveProduced d
          rw [AParser.run_maybe] at hd
          rcases hp : (getDirective O D _ anchor).run _ with ⟨r, end_⟩
          rw [hp] at hd
          cases r with
          | error e => cases e <;> simp [Syntax.maybe] at hd
          | ok q =>
            have eq : q = d := by simpa [Syntax.maybe] using congrArg Prod.fst hd
            exact getDirective_produced O D _ (eq ▸ hp)

private theorem sudo_produced (O : Oracles) (D : Descriptions) {s stop : Stream} {a : Sudo}
    (h : (sudo O D).run s = (.ok a, stop)) : SudoProduced a := by
  unfold sudo at h
  obtain ⟨_, _, _, h⟩ := run_bind_eq_ok.mp h
  split at h
  · exact include_produced O D h
  · obtain ⟨_, _, _, h⟩ := run_bind_eq_ok.mp h
    split at h
    · exact hash_produced O D h
    · exact main_produced O D (by simpa only [run_anchored] using h)

/-! ## File recovery and collection -/

private def ItemProduced : Parsed Sudo → Prop
  | .ok a => SudoProduced a
  | .error _ => True

private theorem finish_produced {r : Parsed Sudo} {stop : Stream} (hr : ItemProduced r)
    {item : Parsed Sudo} (hi : item ∈ (Recovery.finish r stop).1) : ItemProduced item := by
  by_cases hn : (Recovery.afterComment stop).peek = some '\n'
  · simp only [Recovery.finish, hn, ite_true, List.mem_singleton] at hi
    exact hi ▸ hr
  · cases r <;> simp [Recovery.finish, hn] at hi
    · exact hi ▸ hr
    · rcases hi with rfl | rfl
      · exact hr
      · trivial

private theorem trace_produced {O : Oracles} {D : Descriptions} {s stop : Stream}
    {items : List (Parsed Sudo)} (h : Recovery.Trace D.sudo (sudo O D) s items stop) :
    ∀ item ∈ items, ItemProduced item := by
  induction h with
  | eof _ => simp
  | @line start r mid tail stop more hp trace ih =>
    have hr : ItemProduced r := by
      cases r with
      | error _ => trivial
      | ok a =>
        obtain ⟨_, hp⟩ := expectNonterminal_value hp
        exact sudo_produced O D hp
    intro item hi
    rcases List.mem_append.mp hi with hf | ht
    · exact finish_produced hr hf
    · exact ih item ht

private theorem parsed_produced {D : Descriptions} {O : Oracles} {src : List Char}
    {items : List (Parsed Sudo)} (h : parseSudoersWith D O src = .ok items) :
    ∀ item ∈ items, ItemProduced item := by
  obtain ⟨out, hout, _⟩ := parseLines_ok D.sudo (sudo O D) (Stream.new src)
  simp only [parseSudoersWith, hout] at h
  split at h
  · cases h
  · have e : out = items := Except.ok.inj h
    subst items
    have eq : (parseLines D.sudo (sudo O D)).run (Stream.new src) =
        (.ok out, ((parseLines D.sudo (sudo O D)).run (Stream.new src)).2) :=
      Prod.ext hout rfl
    exact trace_produced ((Recovery.parseLines_iff_trace ..).mp eq)

/-- Each Defaults modifier in an item emitted by the line driver came from the DSL, even
if that item precedes a separate terminator diagnostic. -/
theorem parseSudoersWith_defaults_produced {D : Descriptions} {O : Oracles} {src : List Char}
    {items : List (Parsed Sudo)} (h : parseSudoersWith D O src = .ok items)
    {ms : List SettingsModifier} {scope : ConfigScope}
    (hi : .ok (.decl (.defaults ms scope)) ∈ items) {m : SettingsModifier} (hm : m ∈ ms) :
    Produced m :=
  parsed_produced h _ hi m hm

private def EntriesProduced (entries : List (σ × List SettingsModifier)) : Prop :=
  ∀ entry ∈ entries, AllProduced entry.2

private def CollectedProduced (c : Analysis.Collected) : Prop :=
  EntriesProduced c.nonCommand ∧ EntriesProduced c.command

private theorem entries_append {entries : List (σ × List SettingsModifier)}
    {entry : σ × List SettingsModifier} (he : EntriesProduced entries)
    (hm : AllProduced entry.2) : EntriesProduced (entries ++ [entry]) := by
  intro x hx
  rcases List.mem_append.mp hx with hx | hx
  · exact he x hx
  · simp only [List.mem_singleton] at hx
    exact hx ▸ hm

private theorem collectItem_produced {acc out : Analysis.Collected} {item : Parsed Sudo}
    (ha : CollectedProduced acc) (hi : ItemProduced item)
    (h : Analysis.collectItem acc item = some out) : CollectedProduced out := by
  cases item with
  | error status =>
    cases status <;> simp [Analysis.collectItem] at h
    subst out
    exact ha
  | ok a =>
    cases a with
    | decl d =>
      cases d with
      | defaults ms scope =>
        have hm : AllProduced ms := hi
        cases scope <;> simp [Analysis.collectItem] at h <;> subst out
        all_goals first
          | exact ⟨entries_append ha.1 hm, ha.2⟩
          | exact ⟨ha.1, entries_append ha.2 hm⟩
      | _ => simp [Analysis.collectItem] at h <;> subst out <;> exact ha
    | _ => simp [Analysis.collectItem] at h <;> subst out <;> exact ha

private theorem collectFrom_produced {items : List (Parsed Sudo)} {acc out : Analysis.Collected}
    (ha : CollectedProduced acc) (hi : ∀ item ∈ items, ItemProduced item)
    (h : Analysis.collectFrom acc items = some out) : CollectedProduced out := by
  induction items generalizing acc with
  | nil =>
    simp [Analysis.collectFrom] at h
    exact h ▸ ha
  | cons item items ih =>
    cases e : Analysis.collectItem acc item with
    | none => simp [Analysis.collectFrom, List.foldlM_cons, e] at h
    | some next =>
      have hn := collectItem_produced ha (hi item (by simp)) e
      apply ih hn (fun a ha => hi a (List.mem_cons_of_mem _ ha))
      simpa [Analysis.collectFrom, List.foldlM_cons, e] using h

private theorem collect_produced {items : List (Parsed Sudo)} {c : Analysis.Collected}
    (hi : ∀ item ∈ items, ItemProduced item) (h : Analysis.collect items = some c) :
    CollectedProduced c :=
  collectFrom_produced ⟨by simp [EntriesProduced], by simp [EntriesProduced]⟩ hi h

/-! ## The two scope passes -/

private theorem selected_produced {entries : List (σ × List SettingsModifier)}
    (he : EntriesProduced entries) (select : σ × List SettingsModifier → List SettingsModifier)
    (subset : ∀ entry m, m ∈ select entry → m ∈ entry.2) :
    AllProduced (entries.flatMap select) := by
  intro m hm
  obtain ⟨entry, hm₁, hm₂⟩ := List.mem_flatMap.mp hm
  exact he entry hm₁ m (subset entry m hm₂)

private theorem settingsInForce_reachable {U G : Type} (O : Oracle U G)
    (aliases : AliasTable) (req : Request U G) {c : Analysis.Collected}
    (hc : CollectedProduced c) (s : Settings) (hs : Reachable s) :
    Reachable (Analysis.settingsInForce O aliases c req s) := by
  unfold Analysis.settingsInForce
  apply Analysis.reachable_applyModifiers
  · apply Analysis.reachable_applyModifiers hs
    unfold Analysis.nonCommandModifiers
    dsimp only
    apply selected_produced hc.1
    rintro ⟨scope, mods⟩ m hm
    cases scope <;> dsimp only at hm ⊢
    all_goals (first | exact hm | (split at hm <;> simp_all))
  · unfold Analysis.commandModifiers
    dsimp only
    apply selected_produced hc.2
    rintro ⟨scope, mods⟩ m hm
    split at hm
    · exact hm
    · cases hm

/-- For a successful reference parse and local collection, settings selected by the two
scope passes are reachable from the table defaults, in the order used by `settingsInForce`. -/
theorem settingsInForce_reachable_of_text {U G : Type} (O : Oracle U G) (req : Request U G)
    {env : Oracles} {src : List Char} {items : List (Parsed Sudo)} {c : Analysis.Collected}
    (hp : parseSudoers env src = .ok items) (hc : Analysis.collect items = some c) :
    Reachable (Analysis.settingsInForce O (Analysis.policyOf c).aliases c req Settings.default) :=
  settingsInForce_reachable O _ req (collect_produced (parsed_produced hp) hc) _ .default

/-- Effective settings are in range on parsed include-free text. Fatal diagnostic records
are allowed: recovery never invents a modifier, and any accepted prefix is still used. -/
theorem settingsInForce_inRange_of_text {U G : Type} (O : Oracle U G) (req : Request U G)
    {env : Oracles} {src : List Char} {items : List (Parsed Sudo)}
    (hp : parseSudoers env src = .ok items) (hlocal : ∀ i ∈ items, Analysis.LocalItem i) :
    ∃ c, Analysis.collect items = some c ∧
      InRange (Analysis.settingsInForce O (Analysis.policyOf c).aliases c req Settings.default) := by
  obtain ⟨c, hc⟩ := (Analysis.collectFrom_some_iff {} items).mpr hlocal
  exact ⟨c, hc, reachable_inRange (settingsInForce_reachable_of_text O req hp hc)⟩

/-- Successful include-free parses satisfy the range theorem without a separate rejection
premise: the reference line driver never emits `Reject`. -/
theorem settingsInForce_inRange_of_includeFree_text {U G : Type} (O : Oracle U G)
    (req : Request U G) {env : Oracles} {src : List Char} {items : List (Parsed Sudo)}
    (hp : parseSudoers env src = .ok items)
    (noFiles : ∀ path span, .ok (.include path span) ∉ items ∧ .ok (.includeDir path span) ∉ items) :
    ∃ c, Analysis.collect items = some c ∧
      InRange (Analysis.settingsInForce O (Analysis.policyOf c).aliases c req Settings.default) := by
  apply settingsInForce_inRange_of_text O req hp
  intro item hi
  cases item with
  | error e =>
    cases e with
    | reject => exact (parseSudoers_ne_reject env src items hp _ hi rfl).elim
    | fatal _ _ => trivial
  | ok a =>
    cases a with
    | «include» path span => exact (noFiles path span).1 hi
    | includeDir path span => exact (noFiles path span).2 hi
    | _ => trivial

end SudoersSpec.Settings
