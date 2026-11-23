import SudoersSpec.Grammar.PermissionNames

namespace SudoersSpec.Grammar

open SudoersSpec.Syntax

/-- The only following marks used by the canonical command lists. -/
def CommandMark (d : Char) : Prop := d = ',' ∨ d = ':' ∨ d = '\n'

abbrev CommandBoundary (_ : Bool) (r : List Char) : Prop :=
  ∀ d, r.head? = some d → CommandMark d

theorem CommandMark.ws {d : Char} (hd : CommandMark d) : blank d = false ∧ d ≠ '\\' := by
  rcases hd with rfl | rfl | rfl <;> decide

theorem CommandBoundary.ws {b : Bool} {r : List Char} (h : CommandBoundary b r) : WsStop r := by
  intro d hd ha
  obtain ⟨h₁, h₂⟩ := (h d hd).ws
  exact ha.elim (fun he => by rw [h₁] at he; cases he) h₂

theorem CommandBoundary.neEq {b : Bool} {r : List Char} (h : CommandBoundary b r) :
    NextNot (· = '=') r := by
  intro d hd he
  subst d
  rcases h '=' hd with h | h | h <;> contradiction

private theorem commandStop {O : Oracles} (hO : PermissionLexical O.char) {b : Bool} {r : List Char}
    (hr : CommandBoundary b r) : EscStop (metaToken O.char (commandToken O))
      (metaToken O.char (commandToken O)).accept r := by
  intro d hd ha
  have hc := hr d hd
  have hAscii : d.toNat < 128 := by rcases hc with rfl | rfl | rfl <;> decide
  have hu := hO.host.upper_ascii d hAscii
  change (((SimpleCommand.accept O.char d || d == ' ' || d == '\t') || O.char.isUppercase d) = true) ∨
    (true = true ∧ d = '\\') at ha
  rw [hu, SimpleCommand.accept] at ha
  rcases hc with rfl | rfl | rfl
  · have : SimpleCommand.escaped ',' = true := by decide
    simp [this, show isAsciiUppercase ',' = false by decide] at ha
  · have : SimpleCommand.escaped ':' = true := by decide
    simp [this, show isAsciiUppercase ':' = false by decide] at ha
  · simp [hO.ctrl_newline, show isAsciiUppercase '\n' = false by decide] at ha

/-- Canonical `Args` word sequence. The empty exact list and a nonempty prefix list
have different terminal sentinels. -/
def argWords : Args → List String
  | .prefix [] => []
  | .prefix as => as ++ ["*"]
  | .exact [] => ["\"\""]
  | .exact as => as

def argumentLayout (as : List String) : List Char := as.flatMap (fun a => ' ' :: a.toList)

private theorem layout_cons (x : String) (xs : List String) :
    argumentLayout (x :: xs) = ' ' :: (" ".intercalate (x :: xs)).toList := by
  induction xs generalizing x with
  | nil => simp [argumentLayout]
  | cons y ys ih =>
    simp only [argumentLayout, List.flatMap_cons, String.intercalate_cons_cons, String.toList_append,
      List.cons_append]
    simpa [argumentLayout, List.append_assoc] using congrArg (fun cs => ' ' :: x.toList ++ cs) (ih y)

private theorem argsText (a : Args) : (PermissionPrint.args a).toList = argumentLayout (argWords a) := by
  cases a with
  | «prefix» as =>
    cases as with
    | nil => rfl
    | cons x xs =>
      have e := layout_cons x xs
      simp only [PermissionPrint.args, argWords, String.toList_append, argumentLayout, List.flatMap_append]
      rw [show List.flatMap (fun a : String => ' ' :: a.toList) (x :: xs) =
        ' ' :: (" ".intercalate (x :: xs)).toList from e]
      rfl
  | «exact» as =>
    cases as with
    | nil => rfl
    | cons x xs =>
      simp only [PermissionPrint.args, argWords, String.toList_append]
      exact (layout_cons x xs).symm

/-- The physical command pathname is a nonempty whitespace-free absolute path, does
not use the directory shorthand, and denotes the same pattern under this snapshot. -/
structure CommandPathValue (O : Oracles) (p : String) : Prop where
  absolute : p.toList.head? = some '/'
  notDir : p.toList.getLast? ≠ some '/'
  oneWord : ∀ d ∈ p.toList, O.char.isWhitespace d = false
  stable : O.fs.canonicalize p = .err ∨ O.fs.canonicalize p = .ok p
  glob : O.glob.compile p = none

/-- The argument words are literal single words, not glob/regex input or literal
sentinels; the decoded constructor must reproduce the intended exact/prefix shape. -/
structure CommandArgsValue (O : Oracles) (args : Args) : Prop where
  words : ∀ s ∈ argWords args, s.toList ≠ [] ∧ ∀ d ∈ s.toList, O.char.isWhitespace d = false
  sentinel : Command.argPattern ((argWords args).map String.toList) = .ok args

/-- The lexer condition is per value and checked at both the bare boundary and
before the inter-group space (which is read into a command token). -/
structure CommandValue (O : Oracles) (cmd : Command) : Prop where
  path : CommandPathValue O cmd.pattern
  args : CommandArgsValue O cmd.args
  lexeme : ∀ b, LiteralLexeme (metaToken O.char (commandToken O))
    ((PermissionPrint.command cmd).toList ++ gap b)

private theorem splitWord (f : Char → Bool) (w : List Char)
    (h : ∀ d ∈ w, f d = false) :
    splitWhen f w = [w] := by
  induction w with
  | nil => rfl
  | cons d ds ih =>
    rw [splitWhen, h d (by simp), ih (fun c hc => h c (List.mem_cons_of_mem _ hc))]
    rfl

private theorem splitWordSpace {f : Char → Bool} (hf : f ' ' = true)
    (w tail : List Char) (h : ∀ d ∈ w, f d = false) :
    splitWhen f (w ++ ' ' :: tail) = w :: splitWhen f tail := by
  induction w with
  | nil => simp [splitWhen, hf]
  | cons d ds ih =>
    simp only [List.cons_append, splitWhen, h d (by simp), Bool.false_eq_true, ite_false]
    rw [ih (fun c hc => h c (List.mem_cons_of_mem _ hc))]

private theorem splitCommandWords {O : CharOracle} (hs : O.isWhitespace ' ' = true)
    (b : Bool) (w : List Char) (ws : List String)
    (hw : w ≠ []) (hw' : ∀ d ∈ w, O.isWhitespace d = false)
    (hws : ∀ s ∈ ws, s.toList ≠ [] ∧ ∀ d ∈ s.toList, O.isWhitespace d = false) :
    splitWhitespace O ((w ++ argumentLayout ws) ++ gap b) = w :: ws.map String.toList := by
  induction ws generalizing w with
  | nil =>
    cases b with
    | false => simp [splitWhitespace, argumentLayout, gap, splitWord _ w hw', hw]
    | true => simp [splitWhitespace, argumentLayout, gap, splitWordSpace hs w [] hw', hw, splitWhen]
  | cons a as ih =>
    have hwa := hws a (by simp)
    have hrest := ih a.toList hwa.1 hwa.2 (fun x hx => hws x (List.mem_cons_of_mem _ hx))
    simp only [argumentLayout, List.flatMap_cons, List.append_assoc, List.cons_append] at *
    unfold splitWhitespace at hrest ⊢
    rw [splitWordSpace hs w _ hw']
    simp only [List.filter_cons]
    have hbf : w.isEmpty = false := by cases w <;> simp_all
    simp only [hbf, Bool.not_false, ite_true, List.map_cons]
    exact congrArg (List.cons w) hrest

private theorem CommandPathValue.construct {O : Oracles} {p : String} (h : CommandPathValue O p) :
    SimpleCommand.construct O p.toList = .ok p := by
  have hp : ∃ xs, p.toList = '/' :: xs := by
    rcases he : p.toList with _ | ⟨x, xs⟩
    · have hp := h.absolute; rw [he] at hp; cases hp
    · have hp := h.absolute
      rw [he] at hp
      cases hp
      exact ⟨xs, rfl⟩
  obtain ⟨xs, hx⟩ := hp
  have eq1 : p.toList ≠ "list".toList := by rw [hx]; intro h; cases h
  have eq2 : p.toList ≠ "sudoedit".toList := by rw [hx]; intro h; cases h
  have eq3 : ("sha".toList.isPrefixOf p.toList) = false := by rw [hx]; rfl
  have eq4 : (p.toList.getLast? == some '/') = false := by simpa using h.notDir
  have hv := h.absolute
  simp only [SimpleCommand.construct, beq_eq_false_iff_ne.mpr eq1,
    beq_eq_false_iff_ne.mpr eq2, Bool.or_self, Bool.false_eq_true, ite_false,
    eq3, hv, eq4]
  rcases h.stable with he | he <;>
    simp [he, SimpleCommand.compile, String.ofList_toList, h.glob]

private theorem CommandValue.construct {O : Oracles} (hO : PermissionLexical O.char)
    {cmd : Command} (h : CommandValue O cmd) (b : Bool) :
    (metaToken O.char (commandToken O)).construct ((PermissionPrint.command cmd).toList ++ gap b) =
      .ok (.only cmd) := by
  have hne : cmd.pattern.toList ≠ [] := by intro e; have := h.path.absolute; simp [e] at this
  have hw := splitCommandWords hO.space b cmd.pattern.toList (argWords cmd.args) hne h.path.oneWord h.args.words
  have hs : ((PermissionPrint.command cmd).toList ++ gap b).head? = some '/' := by
    simp [PermissionPrint.command, String.toList_append, List.head?_append, h.path.absolute]
  have ht {xs : List Char} (hx : xs.head? = some '/') : (trimEnd O.char xs).head? = some '/' := by
    have hslash : O.char.isWhitespace '/' = false :=
      (hO.host.ws_ascii '/' (by decide)).trans (by decide)
    cases xs with
    | nil => cases hx
    | cons x tail =>
      have he : x = '/' := Option.some.inj hx
      subst x
      have reverseDrop (t : List Char) : (t ++ ['/']).dropWhile O.char.isWhitespace =
          t.dropWhile O.char.isWhitespace ++ ['/'] := by
        induction t with
        | nil => simp [hslash]
        | cons c t ih => by_cases hh : O.char.isWhitespace c = true <;> simp [hh, ih]
      simp [trimEnd, reverseDrop, List.reverse_cons, List.reverse_append]
  have htrim := ht hs
  have rv1 : trimEnd O.char ((PermissionPrint.command cmd).toList ++ gap b) ≠ "ALL".toList := by
    intro eq; rw [eq] at htrim; cases htrim
  have rv2 : startsWithPred (trimEnd O.char ((PermissionPrint.command cmd).toList ++ gap b))
      AliasName.accept1st = false := by
    cases he : trimEnd O.char ((PermissionPrint.command cmd).toList ++ gap b) with
    | nil => rw [he] at htrim; cases htrim
    | cons d ds => rw [he] at htrim; cases htrim; rfl
  have hlist : cmd.pattern ≠ "list" := by intro e; have hp := h.path.absolute; rw [e] at hp; cases hp
  change Meta.construct O.char (commandToken O) _ = _
  simp only [Meta.construct, beq_eq_false_iff_ne.mpr rv1, rv2, Bool.false_and,
    Bool.false_eq_true, ite_false]
  rw [show (commandToken O).construct = Command.construct O from rfl]
  simp only [Command.construct, PermissionPrint.command, String.toList_append, argsText, hw,
    h.path.construct, h.args.sentinel, beq_eq_false_iff_ne.mpr hlist, Bool.false_and,
    Bool.false_eq_true, ite_false]

/-- A usable command alias must not be captured by a command tag or reserved keyword.
The predicate is separate from any parser effect. -/
def FreeCommandAlias (name : String) : Prop :=
  name ∉ ["ALL", "EXEC", "NOEXEC", "SETENV", "NOSETENV", "PASSWD", "NOPASSWD", "CWD",
    "INTERCEPT", "CHROOT", "TIMEOUT", "NOTBEFORE", "NOTAFTER", "ROLE", "TYPE", "LOG_INPUT",
    "NOLOG_INPUT", "LOG_OUTPUT", "NOLOG_OUTPUT", "MAIL", "NOMAIL", "FOLLOW", "NOFOLLOW",
    "NOINTERCEPT", "APPARMOR_PROFILE"]

def CommandMemberValue (O : Oracles) : Meta Command → Prop
  | .only c => CommandValue O c
  | .all => ∀ b, LiteralValue (metaToken O.char (commandToken O)) ("ALL".toList ++ gap b) .all
  | .alias s => AliasShape s.toList ∧ utf8Len s.toList.dropLast < 255 ∧ FreeCommandAlias s ∧
    ∀ b, LiteralValue (metaToken O.char (commandToken O)) (s.toList ++ gap b) (.alias s)

abbrev commandText := PermissionPrint.metaItem PermissionPrint.command

theorem commandMemberStart {O : Oracles} {m : Meta Command} (h : CommandMemberValue O m) :
    MemberStart (commandText m) := by
  have fromChar {s : String} {d : Char} (hd : s.toList.head? = some d)
      (hc : Hostname.accept d = true) : MemberStart s := NameStart.member ⟨d, hd, hc⟩
  cases m with
  | all => exact fromChar (d := 'A') rfl (by decide)
  | alias s =>
    obtain ⟨d, ds, he, hd, _⟩ := h.1
    have hh : s.toList.head? = some d := by rw [he]; rfl
    exact fromChar hh (by simp [Hostname.accept, isAsciiAlphanumeric, hd])
  | only c =>
    have e : (commandText (.only c)).toList.head? = some '/' := by
      simp [commandText, PermissionPrint.metaItem, PermissionPrint.command, String.toList_append,
        List.head?_append, h.path.absolute]
    refine ⟨⟨'/', e, by decide, by decide, by decide, by decide⟩, ?_⟩
    intro r d hd hbang
    rw [List.head?_append, e] at hd
    cases hbang
    cases hd

private theorem aliasBare {s : String} (h : AliasShape s.toList) (hl : utf8Len s.toList.dropLast < 255)
    {b : Bool} {r : List Char} (hr : CommandBoundary b r) :
    NontermG AliasNameG (s.toList ++ gap b) s r := by
  refine ⟨s.toList, gap b, rfl, ⟨h, hl, ?_, String.ofList_toList.symm⟩, ?_⟩
  · intro d hd ha
    cases b with
    | false =>
      have he := hr d hd
      rcases he with rfl | rfl | rfl <;> contradiction
    | true =>
      have he : ' ' = d := Option.some.inj hd
      subst d
      contradiction
  · cases b
    · exact hr.ws.nil
    · exact .stop (by simp [gap, blank]) hr.ws

private theorem tagAliasG {O : Oracles} {s : String} {r : List Char} {b : Bool}
    (hs : AliasShape s.toList) (hl : utf8Len s.toList.dropLast < 255) (h : FreeCommandAlias s)
    (hr : CommandBoundary b r) : TagProbeG (CleanMetaTagG O) (s.toList ++ gap b) (some (.alias s)) r := by
  apply nonterm (OptG.some ?_) hr.ws
  refine ⟨⟨s, s.toList ++ gap b, [], (1, 1), by simp, aliasBare hs hl hr, ?_⟩, trivial⟩
  unfold TagRhsG
  split
  all_goals first | exact ⟨rfl, rfl, hr.neEq⟩ | exact False.elim (h (by simp))

private theorem tagAllG {O : Oracles} {r : List Char} {b : Bool} (hr : CommandBoundary b r) :
    TagProbeG (CleanMetaTagG O) ("ALL".toList ++ gap b) (some .all) r := by
  have h : NontermG AliasNameG ("ALL".toList ++ gap b) "ALL" r := aliasBare aliasShape_ALL (by decide) hr
  exact nonterm (.some ⟨⟨"ALL", "ALL".toList ++ gap b, [], (1, 1), by simp, h, pureG _ r⟩, trivial⟩) hr.ws

private theorem noTag {O : Oracles} {c r : List Char} {d : Char} (he : (c ++ r).head? = some d)
    (hd : d = '!' ∨ d = '/') : TagProbeG (CleanMetaTagG O) [] none (c ++ r) := by
  have hn : NextNot (fun x => AliasName.accept1st x = true) (c ++ r) := by
    intro x hx ha
    rw [he] at hx
    have e := Option.some.inj hx
    subst x
    rcases hd with rfl | rfl <;> contradiction
  have hw : WsStop (c ++ r) := by
    intro x hx ha
    rw [he] at hx
    have e := Option.some.inj hx
    subst x
    rcases hd with rfl | rfl <;> exact (by decide : ¬ (blank _ = true ∨ _ = '\\')) ha
  exact nonterm (.none ⟨rfl, hn⟩) hw

private theorem commandTok {O : Oracles} (hO : PermissionLexical O.char) {m : Meta Command}
    (hm : CommandMemberValue O m) {b : Bool} {r : List Char} (hr : CommandBoundary b r) :
    NontermG (CommandTokenG O) ((commandText m).toList ++ gap b) m r := by
  apply nonterm _ hr.ws
  have hs := commandStop hO hr
  cases m with
  | all => exact (hm b).derives hs
  | only c => exact ((hm.lexeme b).withValue (hm.construct hO b)).derives hs
  | alias n => exact (hm.2.2.2 b).derives hs

private theorem qualifiedCommandText {O : Oracles} (hO : PermissionLexical O.char) {q : Spec Command}
    (hm : CommandMemberValue O q.who) {b : Bool} {r : List Char} (hr : CommandBoundary b r) :
    NontermG (QualifiedCommandG O) ((PermissionPrint.spec PermissionPrint.command q).toList ++ gap b) q r := by
  have hs := commandMemberStart hm
  exact nonterm (qualifyPrinted (f := commandText) hs.start (hs.notBang _)
    (commandTok hO hm hr) q rfl) hr.ws

/-- Canonical command with already-read tags, before wrapping in an entry. -/
theorem commandLast_grammar {O : Oracles} (hO : PermissionLexical O.char) (mods : List Modifier)
    {q : Spec Command} (hs : CommandMemberValue O q.who) {b : Bool} {r : List Char} (hr : CommandBoundary b r) :
    SeqG (TagLoopG (CleanMetaTagG O) mods)
        (fun | .inl ms => MapG (NontermG (QualifiedCommandG O)) (fun cmd => ⟨ms, cmd⟩)
             | .inr cs => PureG cs)
      ((PermissionPrint.spec PermissionPrint.command q).toList ++ gap b) ⟨mods, q⟩ r := by
  cases q with
  | allow m =>
    cases m with
    | all => exact ⟨_, [], .inr ⟨mods, .allow .all⟩, (List.append_nil _).symm,
        .all (tagAllG hr), pureG _ r⟩
    | alias s => exact ⟨_, [], .inr ⟨mods, .allow (.alias s)⟩, (List.append_nil _).symm,
        .alias (tagAliasG hs.1 hs.2.1 hs.2.2.1 hr), pureG _ r⟩
    | only cmd =>
      have hc : ((PermissionPrint.spec PermissionPrint.command (.allow (.only cmd))).toList ++ gap b ++ r).head? = some '/' := by
        simp [PermissionPrint.spec, PermissionPrint.qualified, PermissionPrint.metaItem,
          PermissionPrint.command, String.toList_append, List.head?_append, hs.path.absolute]
      exact ⟨[], _, .inl mods, rfl, .stop (noTag hc (.inr rfl)), mapG (qualifiedCommandText hO hs hr)⟩
  | forbid m =>
    have hc : ((PermissionPrint.spec PermissionPrint.command (.forbid m)).toList ++ gap b ++ r).head? = some '!' := by
      simp [PermissionPrint.spec, PermissionPrint.qualified, String.toList_append]
    exact ⟨[], _, .inl mods, rfl, .stop (noTag hc (.inl rfl)), mapG (qualifiedCommandText hO hs hr)⟩

/-! ## Supported modifiers -/

def supportedModifier (m : Modifier) : Prop := (PermissionPrint.modifier m).isSome = true

structure CommandSpecValue (O : Oracles) (a : CommandSpec) : Prop where
  count : a.mods.length ≤ 127
  supported : ∀ m ∈ a.mods, supportedModifier m
  command : CommandMemberValue O a.cmd.who

private theorem tagPrint {O : Oracles} {m : Modifier} {s : String} {r : List Char}
    (hs : PermissionPrint.modifier m = some s) (hr : WsStop r) :
    TagProbeG (CleanMetaTagG O) (s.toList ++ [' ']) (some (.only m)) r := by
  have key {key : String} (hna : AliasShape key.toList)
      (hl : utf8Len key.toList.dropLast < 255)
      (hg : TagRhsG O ⟨(1, 1), posAfter key.toList (1, 1)⟩ key [':', ' '] (.only m) r)
      (he : s.toList = key.toList ++ [':']) :
      TagProbeG (CleanMetaTagG O) (s.toList ++ [' ']) (some (.only m)) r := by
    have hfree : SpanFreeTag (.only m) := by cases m <;> simp [PermissionPrint.modifier, SpanFreeTag] at hs ⊢
    have g : AliasNameG key.toList key (':' :: ' ' :: r) :=
      ⟨hna, hl, NextNot.cons_iff.mpr (by decide), String.ofList_toList.symm⟩
    have hname := nonterm g (NextNot.cons_iff.mpr (by decide))
    exact nonterm (OptG.some ⟨⟨key, key.toList, [':', ' '], (1, 1),
      by simp [he, List.append_assoc], hname, hg⟩, hfree⟩) hr
  cases m <;> simp only [PermissionPrint.modifier, Option.some.injEq, reduceCtorEq] at hs
  all_goals first | contradiction | subst s
  all_goals
    first
      | exact key (key := "EXEC") (by decide) (by decide) ⟨(), ⟨[' '], rfl, .stop (by decide) hr⟩, rfl⟩ rfl
      | exact key (key := "NOEXEC") (by decide) (by decide) ⟨(), ⟨[' '], rfl, .stop (by decide) hr⟩, rfl⟩ rfl
      | exact key (key := "SETENV") (by decide) (by decide) ⟨(), ⟨[' '], rfl, .stop (by decide) hr⟩, rfl⟩ rfl
      | exact key (key := "NOSETENV") (by decide) (by decide) ⟨(), ⟨[' '], rfl, .stop (by decide) hr⟩, rfl⟩ rfl
      | exact key (key := "PASSWD") (by decide) (by decide) ⟨(), ⟨[' '], rfl, .stop (by decide) hr⟩, rfl⟩ rfl
      | exact key (key := "NOPASSWD") (by decide) (by decide) ⟨(), ⟨[' '], rfl, .stop (by decide) hr⟩, rfl⟩ rfl

private theorem modifierStart {m : Modifier} {s : String} (h : PermissionPrint.modifier m = some s) :
    SurfaceStart s := by
  cases m <;> simp only [PermissionPrint.modifier, Option.some.injEq, reduceCtorEq] at h
  all_goals first | contradiction | subst s; refine ⟨_, rfl, ?_, ?_, ?_, ?_⟩ <;> decide

private theorem cmdSpecCons {m : Modifier} {ms : List Modifier} {q : Spec Command}
    {s : String} (h : PermissionPrint.modifier m = some s) :
    PermissionPrint.commandSpec ⟨m :: ms, q⟩ = s ++ " " ++ PermissionPrint.commandSpec ⟨ms, q⟩ := by
  have hn : ms.filterMap PermissionPrint.modifier ++ [PermissionPrint.spec PermissionPrint.command q] ≠ [] := by simp
  simp only [PermissionPrint.commandSpec, List.filterMap_cons, h, List.cons_append]
  rw [String.intercalate_cons_of_ne_nil hn]

private theorem surfaceAppend {s : String} (hs : SurfaceStart s) (t : String) : SurfaceStart (s ++ t) := by
  obtain ⟨d, hd, hb, he, hc, hcol⟩ := hs
  exact ⟨d, by simp [String.toList_append, List.head?_append, hd], hb, he, hc, hcol⟩

theorem commandSpec_start {O : Oracles} {a : CommandSpec} (h : CommandSpecValue O a) :
    SurfaceStart (PermissionPrint.commandSpec a) := by
  rcases a with ⟨ms, q⟩
  cases ms with
  | nil => exact memberPrinted_start (commandMemberStart h.command)
  | cons m ms =>
    cases he : PermissionPrint.modifier m with
    | none => have hp := h.supported m (by simp); simp [supportedModifier, he] at hp
    | some s => rw [cmdSpecCons he]; exact surfaceAppend (surfaceAppend (modifierStart he) " ") _

theorem commandSpec_neParen {O : Oracles} {a : CommandSpec} (h : CommandSpecValue O a) :
    (PermissionPrint.commandSpec a).toList.head? ≠ some '(' := by
  rcases a with ⟨ms, q⟩
  cases ms with
  | nil =>
    simp only [PermissionPrint.commandSpec, List.filterMap_nil, List.nil_append,
      String.intercalate_singleton]
    cases q with
    | forbid _ =>
      simp [PermissionPrint.spec, PermissionPrint.qualified, String.toList_append]
    | allow m =>
      cases m with
      | all => decide
      | alias n =>
        obtain ⟨d, ds, he, hd, _⟩ := h.command.1
        change n.toList.head? ≠ some '('
        rw [he]
        intro eq
        have eq' := Option.some.inj eq
        subst d
        contradiction
      | only c =>
        change (PermissionPrint.command c).toList.head? ≠ some '('
        simp [PermissionPrint.command, String.toList_append, List.head?_append, h.command.path.absolute]
  | cons m ms =>
    cases he : PermissionPrint.modifier m with
    | none => have hp := h.supported m (by simp); simp [supportedModifier, he] at hp
    | some s =>
      rw [cmdSpecCons he]
      cases m <;> simp only [PermissionPrint.modifier, Option.some.injEq, reduceCtorEq] at he
      all_goals first | contradiction | subst s; simp [String.toList_append]

theorem commandSpec_value {O : Oracles} (hO : PermissionLexical O.char) {a : CommandSpec}
    (h : CommandSpecValue O a) {b : Bool} {r : List Char} (hr : CommandBoundary b r) :
    NontermG (CleanCommandSpecG O) ((PermissionPrint.commandSpec a).toList ++ gap b) a r := by
  rcases a with ⟨ms, q⟩
  apply nonterm _ hr.ws
  have build : ∀ done left : List Modifier, done.length + left.length ≤ 127 →
      (∀ m ∈ left, supportedModifier m) →
      SeqG (TagLoopG (CleanMetaTagG O) done)
        (fun | .inl ms => MapG (NontermG (QualifiedCommandG O)) (fun cmd => ⟨ms, cmd⟩)
             | .inr cs => PureG cs)
        ((PermissionPrint.commandSpec ⟨left, q⟩).toList ++ gap b) ⟨done ++ left, q⟩ r := by
    intro done left
    induction left generalizing done with
    | nil =>
      intro _ _
      simpa [PermissionPrint.commandSpec] using commandLast_grammar hO done h.command hr
    | cons m ms ih =>
      intro hlen hs
      cases he : PermissionPrint.modifier m with
      | none => have hp := hs m (by simp); simp [supportedModifier, he] at hp
      | some s =>
        have hms : ∀ m ∈ ms, supportedModifier m := fun m hm => hs m (List.mem_cons_of_mem _ hm)
        have hlen' : (done ++ [m]).length + ms.length ≤ 127 := by
          simp at hlen ⊢; omega
        obtain ⟨x, y, a, hxy, hx, hy⟩ := ih (done ++ [m]) hlen' hms
        have hstart := commandSpec_start (O := O) (a := ⟨ms, q⟩)
          ⟨by change ms.length ≤ 127; simp at hlen; omega, hms, h.command⟩
        have hw : WsStop (x ++ (y ++ r)) := by
          rw [← List.append_assoc, ← hxy, List.append_assoc]
          exact (hstart.append _).1
        have hprobe := tagPrint (O := O) he hw
        have ht := TagLoopG.modifier hprobe (by omega : (done ++ [m]).length ≤ 127) hx
        rw [cmdSpecCons he, String.toList_append, String.toList_append]
        refine ⟨(s.toList ++ [' ']) ++ x, y, a, ?_, ht, ?_⟩
        · rw [List.append_assoc, hxy, ← List.append_assoc]
          rfl
        · simpa [List.append_assoc] using hy
  exact build [] ms (by simpa using h.count) h.supported

end SudoersSpec.Grammar
