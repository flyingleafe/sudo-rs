import SudoersSpec.Grammar.PermissionPrint

namespace SudoersSpec.Grammar

open SudoersSpec.Syntax

/-- Nonempty `Many` contents; optional list positions use `ks = [] ∨ BoundedItems ...`. -/
def BoundedItems (P : α → Prop) (ks : List α) : Prop :=
  ks ≠ [] ∧ ks.length ≤ 127 ∧ ∀ k ∈ ks, P k

/-- The delimiters must stay out of the Unicode token classes. Limits and command-path
normalization are checked per value, not assumed of the whole oracle. -/
structure PermissionLexical (O : CharOracle) : Prop where
  host : HostOracle O
  alnum_ascii : ∀ c, c.toNat < 128 → O.isAlphanumeric c = isAsciiAlphanumeric c
  ctrl_newline : O.isControl '\n' = true
  space : O.isWhitespace ' ' = true

/-- A literal's lexical checks when its value is proved separately. -/
structure LiteralLexeme (T : TokenSpec α) (cs : List Char) : Prop where
  ne : cs ≠ []
  first : ∀ d, cs.head? = some d → T.accept1st d = true
  tail : ∀ d ∈ cs.drop 1, T.accept d = true
  noEscape : '\\' ∉ cs
  bytes : utf8Len cs.dropLast < T.maxLen

/-- The semantic test is the token constructor on the literal's value text; it
does not execute a stream parser. -/
structure LiteralValue (T : TokenSpec α) (cs : List Char) (a : α) : Prop extends LiteralLexeme T cs where
  value : T.construct cs = .ok a

theorem LiteralLexeme.withValue {T : TokenSpec α} {cs : List Char} {a : α}
    (h : LiteralLexeme T cs) (v : T.construct cs = .ok a) : LiteralValue T cs a :=
  ⟨h, v⟩

private theorem literalTail {T : TokenSpec α} {cs r : List Char}
    (h : ∀ d ∈ cs, T.accept d = true) (hn : '\\' ∉ cs) (hs : EscStop T T.accept r) :
    TokTail T cs cs r := by
  induction cs with
  | nil => exact .stop hs
  | cons d ds ih =>
    exact TokTail.cons (u := [d]) (.plain (h d (by simp)) (fun _ e => hn (e ▸ List.mem_cons_self)))
      (ih (fun c hc => h c (List.mem_cons_of_mem _ hc)) (fun hc => hn (List.mem_cons_of_mem _ hc)))

theorem LiteralValue.derives {T : TokenSpec α} {cs : List Char} {a : α} (h : LiteralValue T cs a)
    {r : List Char} (hr : EscStop T T.accept r) : TokenG T cs a r := by
  cases cs with
  | nil => exact False.elim (h.ne rfl)
  | cons x xs =>
    have hn : x ≠ '\\' := fun he => h.noEscape (he ▸ List.mem_cons_self)
    have hxs : '\\' ∉ xs := fun he => h.noEscape (List.mem_cons_of_mem _ he)
    have hlen : LenOK T.maxLen [x] xs := by
      apply (lenOK_iff _ _ _).2
      cases xs with
      | nil => exact .inl rfl
      | cons y ys => exact .inr (by simpa using h.bytes)
    exact TokenG.mk (u := [x]) (.plain (h.first x rfl) (fun _ => hn))
      (literalTail h.tail hxs hr) hlen h.value

/-- A string with a usable first character after a layout boundary. -/
def SurfaceStart (s : String) : Prop :=
  ∃ d, s.toList.head? = some d ∧ blank d = false ∧ d ≠ '\\' ∧ d ≠ ',' ∧ d ≠ ':'

abbrev WsStop := NextNot (fun d => blank d = true ∨ d = '\\')

abbrev gap (b : Bool) : List Char := if b then [' '] else []

/-- A bare-name delimiter or explicit preceding space. `endMark` is the boundary
set used by the canonical printer, not the larger grammar's follow set. -/
def endMark (d : Char) : Prop := d = ',' ∨ d = ':' ∨ d = ')' ∨ d = '\n' ∨ d = '='

def Boundary (b : Bool) (r : List Char) : Prop :=
  WsStop r ∧ (b = false → ∀ d, r.head? = some d → endMark d)

theorem Boundary.ws {b : Bool} {r : List Char} (h : Boundary b r) : Ws (gap b) r := by
  cases b
  · exact Ws.nil_iff.mpr h.1
  · exact Ws.stop (by simp [gap, blank]) h.1

theorem WsStop.nil {r : List Char} (h : WsStop r) : Ws [] r := Ws.nil_iff.mpr h

theorem SurfaceStart.append {s : String} (h : SurfaceStart s) (r : List Char) :
    WsStop (s.toList ++ r) ∧ NextNot (· = ',') (s.toList ++ r) ∧ NextNot (· = ':') (s.toList ++ r) := by
  obtain ⟨d, hd, hb, hbs, hc, hcol⟩ := h
  have h' : (s.toList ++ r).head? = some d := by simp [List.head?_append, hd]
  have same : ∀ x, (s.toList ++ r).head? = some x → x = d := fun x e => Option.some.inj (e.symm.trans h')
  refine ⟨?_, ?_, ?_⟩
  · intro x e
    rw [same x e]
    simp [hb, hbs]
  · intro x e; rw [same x e]; exact hc
  · intro x e; rw [same x e]; exact hcol

theorem WsStop.boundary {r : List Char} (h : WsStop r) : Boundary true r := ⟨h, by intro e; cases e⟩

theorem endMark.ws {d : Char} (h : endMark d) : blank d = false ∧ d ≠ '\\' := by
  rcases h with rfl | rfl | rfl | rfl | rfl <;> decide

theorem Boundary.cons {d : Char} (h : endMark d) (r : List Char) (b : Bool) : Boundary b (d :: r) := by
  obtain ⟨hb, hs⟩ := h.ws
  refine ⟨NextNot.cons_iff.mpr (by simp [hb, hs]), ?_⟩
  intro _ x e; cases e; exact h

theorem Boundary.gapHead {b : Bool} {r : List Char} (h : Boundary b r) {d : Char}
    (he : (gap b ++ r).head? = some d) : d = ' ' ∨ endMark d := by
  cases b with
  | false => exact .inr (h.2 rfl d he)
  | true => left; exact (Option.some.inj he).symm

theorem nonterm {G : Gram α} {c r : List Char} {a : α} (h : G c a r) (hw : WsStop r) :
    NontermG G c a r := ⟨c, [], by simp, h, hw.nil⟩

theorem takeGap {G : Gram α} {c r : List Char} {a : α} {b : Bool}
    (h : G c a (gap b ++ r)) (hr : Boundary b r) : NontermG G (c ++ gap b) a r :=
  ⟨c, gap b, rfl, h, hr.ws⟩

theorem mapG {G : Gram α} {f : α → β} {c r : List Char} {a : α}
    (h : G c a r) : MapG G f c (f a) r := ⟨a, h, rfl⟩

theorem seqG {G : Gram α} {H : α → Gram β} {c c' r : List Char} {a : α} {b : β}
    (h : G c a (c' ++ r)) (h' : H a c' b r) : SeqG G H (c ++ c') b r :=
  ⟨c, c', a, rfl, h, h'⟩

theorem pureG (a : α) (r : List Char) : PureG a [] a r := ⟨rfl, rfl⟩

def listText (sep : String) (f : α → String) (ks : List α) : List Char :=
  (sep.intercalate (ks.map f)).toList

private def tailText (sep : String) (f : α → String) : List α → List Char
  | [] => []
  | k :: ks => sep.toList ++ listText sep f (k :: ks)

private theorem listText_cons (sep : String) (f : α → String) (k : α) (ks : List α) :
    listText sep f (k :: ks) = (f k).toList ++ tailText sep f ks := by
  cases ks with
  | nil => simp [listText, tailText]
  | cons j js =>
    simp only [listText, tailText, List.map_cons, String.intercalate_cons_cons, String.toList_append]
    simp only [List.append_assoc]

/-- Canonical punctuation, whose separator includes its surrounding blanks as printed.
A preceding blank is consumed by the *earlier* element; a following blank by the separator. -/
structure ListSeparator where
  mark : Char
  before : Bool

namespace ListSeparator

def spelling (s : ListSeparator) : String := String.ofList (gap s.before ++ [s.mark, ' '])

abbrev comma : ListSeparator := ⟨',', false⟩
abbrev colon : ListSeparator := ⟨':', true⟩

end ListSeparator

/-- Assemble a canonical list from per-item certificates with lexical boundaries. The
certificate hypotheses are proved recursively from structural conditions on the items. -/
theorem canonicalList {G : Gram α} {P : α → Prop} {Follow : Bool → List Char → Prop}
    (f : α → String) (s : ListSeparator) (atSep : ∀ r, Follow s.before (s.mark :: ' ' :: r))
    (elem : ∀ k, P k → ∀ b r, Follow b r → NontermG G ((f k).toList ++ gap b) k r)
    (nonblank : ∀ k, P k → SurfaceStart (f k)) {ks : List α} (h : BoundedItems P ks)
    {r : List Char} {b : Bool} (hb : Follow b r) (hsep : NextNot (· = s.mark) r) :
    ListG G s.mark 127 (listText s.spelling f ks ++ gap b) ks r := by
  have tail : ∀ k ks, (∀ x ∈ k :: ks, P x) →
      NontermG G ((f k).toList ++ gap (if ks.isEmpty then b else s.before)) k
        ((if ks.isEmpty then [] else [s.mark, ' '] ++ listText s.spelling f ks ++ gap b) ++ r) ∧
      ListTail G s.mark (if ks.isEmpty then [] else [s.mark, ' '] ++ listText s.spelling f ks ++ gap b) ks r := by
    intro k ks
    induction ks generalizing k with
    | nil =>
      intro hh
      exact ⟨elem k (hh _ (by simp)) b r hb, .nil hsep⟩
    | cons j js ih =>
      intro hh
      obtain ⟨hj, ht⟩ := ih j (fun x hx => hh x (List.mem_cons_of_mem _ hx))
      constructor
      · exact elem k (hh _ (by simp)) _ _ (atSep _)
      · have hw : Ws [' '] (listText s.spelling f (j :: js) ++ gap b ++ r) := by
          apply Ws.stop (by simp [blank])
          rw [listText_cons, List.append_assoc, List.append_assoc]
          exact ((nonblank j (hh _ (by simp))).append _).1
        have shape : (f j).toList ++ gap (if js.isEmpty then b else s.before) ++
            (if js.isEmpty then [] else [s.mark, ' '] ++ listText s.spelling f js ++ gap b) =
            listText s.spelling f (j :: js) ++ gap b := by
          rw [listText_cons]
          cases js <;> simp [tailText, ListSeparator.spelling, String.toList_ofList, List.append_assoc]
        have hw' : Ws [' '] (((f j).toList ++ gap (if js.isEmpty then b else s.before)) ++
            (if js.isEmpty then [] else [s.mark, ' '] ++ listText s.spelling f js ++ gap b) ++ r) := by
          rwa [shape]
        have hs := ListTail.cons (sep := s.mark) hw' hj ht
        change ListTail G s.mark
          ([s.mark, ' '] ++ (listText s.spelling f (j :: js) ++ gap b)) (j :: js) r
        rw [← shape]
        simpa only [List.append_assoc, List.cons_append, List.nil_append] using hs
  obtain ⟨hne, hlen, hall⟩ := h
  cases ks with
  | nil => exact False.elim (hne rfl)
  | cons k ks =>
    obtain ⟨hg, ht⟩ := tail k ks hall
    have shape : (f k).toList ++ gap (if ks.isEmpty then b else s.before) ++
        (if ks.isEmpty then [] else [s.mark, ' '] ++ listText s.spelling f ks ++ gap b) =
        listText s.spelling f (k :: ks) ++ gap b := by
      rw [listText_cons]
      cases ks <;> simp [tailText, ListSeparator.spelling, String.toList_ofList, List.append_assoc]
    exact shape ▸ ListG.mk hg ht (.inr (by simp only [List.length_cons] at hlen; omega))

/-- A command consumes the blank before `:` if it has one; name tokens do not. This
weaker boundary class is therefore used only after trailing whitespace has been fixed. -/
theorem PermissionLexical.ascii_host {O : CharOracle} (hO : PermissionLexical O) {d : Char}
    (h : d.toNat < 128) : hostChar O d = Hostname.accept d := by
  unfold hostChar
  rw [hO.host.upper_ascii d h]
  cases he : isAsciiUppercase d <;> simp
  simp [Hostname.accept, isAsciiAlphanumeric, he]

end SudoersSpec.Grammar
