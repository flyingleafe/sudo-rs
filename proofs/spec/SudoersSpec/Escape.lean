/-!
# Argument escaping of `sudo -s` / `sudo -i`

With `-s` or `-i`, sudo-rs runs the shell as `shell -c LINE`, where `LINE` is built by `escaped`
in `src/common/command.rs` from the command line arguments: every byte of an argument that is
not an ASCII alphanumeric, `_`, `-` or `$` is preceded by a backslash, and the escaped arguments
are joined with one space.

This file specifies that function on byte lists and proves, for every input:

* `escapeArg_eq_flatMap`, `keep_iff`, `escapeArgs_eq_intercalate`: the exact
  characterization (each byte kept iff in the class, else prefixed by a backslash; arguments
  joined with one space);
* `escapeArgs_eq_iff`: the only two argument lists that give the same line are `[]` and `[[]]`
  (both give the empty line);
* `unescapeArgs_escapeArgs`: a reader that takes the byte after a backslash literally and ends
  an argument at every other space recovers the argument list from the line (for every list
  except `[[]]`, which reads back as `[]`); `escapeArg_wellEscaped`: inside an escaped argument
  every space and every backslash is preceded by an escaping backslash.

The reader is a model of the escaping grammar, not of a shell: `$` is deliberately left
unescaped, and a shell gives further meaning to some escaped bytes.

Bytes are `UInt8`; `SudoRsProofs/Escape.lean` proves the Aeneas extraction of `escaped` equal
to `escapeArgs`.
-/

namespace SudoersSpec.Escape

/-- `b' '`. -/
def space : UInt8 := 32

/-- `b'\\'`. -/
def backslash : UInt8 := 92

/-- `is_unescaped`: `b'0'..=b'9' | b'A'..=b'Z' | b'a'..=b'z' | b'_' | b'-' | b'$'`. -/
def keep (c : UInt8) : Bool :=
  (48 ≤ c && c ≤ 57) || (65 ≤ c && c ≤ 90) || (97 ≤ c && c ≤ 122) ||
    c == 95 || c == 45 || c == 36

/-- One byte of an argument in the line. -/
def escapeByte (c : UInt8) : List UInt8 :=
  if keep c then [c] else [backslash, c]

/-- One escaped argument (`escape_arg_into`). -/
def escapeArg : List UInt8 → List UInt8
  | [] => []
  | c :: cs => escapeByte c ++ escapeArg cs

/-- The line: the escaped arguments joined with one space (`escaped`). -/
def escapeArgs : List (List UInt8) → List UInt8
  | [] => []
  | [a] => escapeArg a
  | a :: b :: rest => escapeArg a ++ space :: escapeArgs (b :: rest)

/-! ## Exact characterization -/

set_option maxRecDepth 8192 in
/-- The kept bytes, as characters: the ASCII alphanumerics and `_`, `-`, `$`. -/
theorem keep_iff (c : UInt8) :
    keep c = true ↔
      ('0'.toNat ≤ c.toNat ∧ c.toNat ≤ '9'.toNat) ∨ ('A'.toNat ≤ c.toNat ∧ c.toNat ≤ 'Z'.toNat) ∨
      ('a'.toNat ≤ c.toNat ∧ c.toNat ≤ 'z'.toNat) ∨
      c.toNat = '_'.toNat ∨ c.toNat = '-'.toNat ∨ c.toNat = '$'.toNat := by
  have h : ∀ n : Nat, n < 256 → (keep (UInt8.ofNat n) = true ↔
      ('0'.toNat ≤ n ∧ n ≤ '9'.toNat) ∨ ('A'.toNat ≤ n ∧ n ≤ 'Z'.toNat) ∨
      ('a'.toNat ≤ n ∧ n ≤ 'z'.toNat) ∨ n = '_'.toNat ∨ n = '-'.toNat ∨ n = '$'.toNat) := by
    decide
  have := h c.toNat c.toNat_lt
  rwa [UInt8.ofNat_toNat] at this

/-- Exactly 65 of the 256 byte values are kept (10 digits, 52 letters, `_`, `-`, `$`). -/
theorem keep_count : ((List.range 256).filter fun n => keep (UInt8.ofNat n)).length = 65 := by
  decide

theorem keep_space : keep space = false := by decide
theorem keep_backslash : keep backslash = false := by decide

/-- Each byte is kept iff `keep`, otherwise preceded by a backslash. -/
theorem escapeArg_eq_flatMap (a : List UInt8) :
    escapeArg a = a.flatMap fun c => if keep c then [c] else [backslash, c] := by
  induction a with
  | nil => rfl
  | cons c cs ih => simp [escapeArg, ih, escapeByte]

theorem escapeArg_append (a b : List UInt8) : escapeArg (a ++ b) = escapeArg a ++ escapeArg b := by
  induction a with
  | nil => rfl
  | cons c cs ih => simp [escapeArg, ih]

theorem escapeArg_length (a : List UInt8) :
    (escapeArg a).length = a.length + (a.filter fun c => !keep c).length := by
  induction a with
  | nil => rfl
  | cons c cs ih =>
    simp only [escapeArg, escapeByte, List.length_append, ih, List.filter_cons]
    cases keep c <;> simp <;> omega

/-- The line joins the escaped arguments with one space. -/
theorem escapeArgs_eq_intercalate (as : List (List UInt8)) :
    escapeArgs as = [space].intercalate (as.map escapeArg) := by
  match as with
  | [] => rfl
  | [a] => simp [escapeArgs]
  | a :: b :: rest =>
    rw [escapeArgs, escapeArgs_eq_intercalate (b :: rest)]
    simp [List.intercalate_cons_cons]

/-- The line of `a :: rest`: `a`, then each further argument preceded by a space (the loop of
`escaped`). -/
theorem escapeArgs_cons (a : List UInt8) (rest : List (List UInt8)) :
    escapeArgs (a :: rest) = escapeArg a ++ rest.flatMap (fun b => space :: escapeArg b) := by
  induction rest generalizing a with
  | nil => simp [escapeArgs]
  | cons b bs ih => rw [escapeArgs, ih]; simp

theorem escapeArg_eq_nil_iff (a : List UInt8) : escapeArg a = [] ↔ a = [] := by
  cases a with
  | nil => simp [escapeArg]
  | cons c cs => simp [escapeArg, escapeByte]; split <;> simp

theorem escapeArgs_eq_nil_iff (as : List (List UInt8)) :
    escapeArgs as = [] ↔ as = [] ∨ as = [[]] := by
  match as with
  | [] => simp [escapeArgs]
  | [a] => simp [escapeArgs, escapeArg_eq_nil_iff]
  | a :: b :: rest => simp [escapeArgs]

/-! ## No unescaped space or backslash inside an argument -/

/-- A byte list made of tokens `c` with `keep c` and `\c` with any `c`. Since neither a space
nor a backslash is kept, every space and backslash in it is the second byte of a `\c` token. -/
inductive WellEscaped : List UInt8 → Prop
  | nil : WellEscaped []
  | lit {c : UInt8} {rest : List UInt8} : keep c = true → WellEscaped rest → WellEscaped (c :: rest)
  | esc (c : UInt8) {rest : List UInt8} : WellEscaped rest → WellEscaped (backslash :: c :: rest)

theorem escapeArg_wellEscaped (a : List UInt8) : WellEscaped (escapeArg a) := by
  induction a with
  | nil => exact .nil
  | cons c cs ih =>
    simp only [escapeArg, escapeByte]
    split
    · exact .lit (by assumption) ih
    · exact .esc c ih

/-! ## Reading the line back -/

/-- Put `c` in front of the first argument. -/
def consHead (c : UInt8) : List (List UInt8) → List (List UInt8)
  | [] => [[c]]
  | a :: as => (c :: a) :: as

/-- Read a line into arguments: a backslash takes the next byte literally, any other space ends
an argument, any other byte belongs to the current argument. Never empty. A trailing lone
backslash (absent from escaped lines) is read as itself. -/
def unescapeAux : List UInt8 → List (List UInt8)
  | [] => [[]]
  | [c] => if c = space then [[], []] else [[c]]
  | c :: d :: rest =>
    if c = backslash then consHead d (unescapeAux rest)
    else if c = space then [] :: unescapeAux (d :: rest)
    else consHead c (unescapeAux (d :: rest))

/-- The argument list of a line; the empty line has none. -/
def unescapeArgs : List UInt8 → List (List UInt8)
  | [] => []
  | s => unescapeAux s

theorem unescapeAux_ne_nil (s : List UInt8) : unescapeAux s ≠ [] := by
  match s with
  | [] => simp [unescapeAux]
  | [c] => simp only [unescapeAux]; split <;> simp
  | c :: d :: rest =>
    simp only [unescapeAux]
    split
    · cases unescapeAux rest <;> simp [consHead]
    · split
      · simp
      · cases unescapeAux (d :: rest) <;> simp [consHead]

theorem unescapeAux_space (t : List UInt8) : unescapeAux (space :: t) = [] :: unescapeAux t := by
  cases t with
  | nil => simp [unescapeAux]
  | cons d rest => simp [unescapeAux, show space ≠ backslash by decide]

theorem unescapeAux_lit {c : UInt8} (hc : keep c = true) (t : List UInt8) :
    unescapeAux (c :: t) = consHead c (unescapeAux t) := by
  have hb : c ≠ backslash := by rintro rfl; simp [keep_backslash] at hc
  have hs : c ≠ space := by rintro rfl; simp [keep_space] at hc
  cases t with
  | nil => simp [unescapeAux, hs, consHead]
  | cons d rest => simp [unescapeAux, hb, hs]

theorem unescapeAux_esc (c : UInt8) (t : List UInt8) :
    unescapeAux (backslash :: c :: t) = consHead c (unescapeAux t) := by
  simp [unescapeAux]

/-- Put `a` in front of the first argument. -/
def prepend (a : List UInt8) : List (List UInt8) → List (List UInt8)
  | [] => [a]
  | b :: bs => (a ++ b) :: bs

theorem unescapeAux_escapeArg_append (a rest : List UInt8) :
    unescapeAux (escapeArg a ++ rest) = prepend a (unescapeAux rest) := by
  induction a with
  | nil =>
    simp only [escapeArg, List.nil_append]
    cases h : unescapeAux rest with
    | nil => exact absurd h (unescapeAux_ne_nil rest)
    | cons b bs => simp [prepend]
  | cons c cs ih =>
    simp only [escapeArg, escapeByte]
    split
    · simp only [List.cons_append, List.nil_append]
      rw [unescapeAux_lit (by assumption), ih]
      cases unescapeAux rest <;> rfl
    · simp only [List.cons_append, List.nil_append]
      rw [unescapeAux_esc, ih]
      cases unescapeAux rest <;> rfl

theorem unescapeAux_escapeArgs {as : List (List UInt8)} (h : as ≠ []) :
    unescapeAux (escapeArgs as) = as := by
  match as with
  | [a] =>
    have := unescapeAux_escapeArg_append a []
    simpa [escapeArgs, unescapeAux, prepend] using this
  | a :: b :: rest =>
    rw [escapeArgs, unescapeAux_escapeArg_append, unescapeAux_space,
      unescapeAux_escapeArgs (as := b :: rest) (by simp)]
    simp [prepend]

/-- Reading the line gives back the arguments, for every list except `[[]]` (whose line is
empty, like that of `[]`). -/
theorem unescapeArgs_escapeArgs {as : List (List UInt8)} (h : as ≠ [[]]) :
    unescapeArgs (escapeArgs as) = as := by
  by_cases h0 : as = []
  · subst h0; rfl
  · have hne : escapeArgs as ≠ [] := by
      rw [Ne, escapeArgs_eq_nil_iff]; simp [h0, h]
    have := unescapeAux_escapeArgs h0
    cases hs : escapeArgs as with
    | nil => exact absurd hs hne
    | cons x xs => rw [hs] at this; exact this

/-! ## The only collision -/

/-- Two argument lists give the same line iff they are equal or are `[]` and `[[]]`. -/
theorem escapeArgs_eq_iff (as bs : List (List UInt8)) :
    escapeArgs as = escapeArgs bs ↔
      as = bs ∨ (as = [] ∧ bs = [[]]) ∨ (as = [[]] ∧ bs = []) := by
  constructor
  · intro h
    by_cases ha : as = [[]]
    · subst ha
      have : escapeArgs bs = [] := by rw [← h]; rfl
      rcases (escapeArgs_eq_nil_iff bs).1 this with hb | hb <;> simp [hb]
    · by_cases hb : bs = [[]]
      · subst hb
        have : escapeArgs as = [] := h
        rcases (escapeArgs_eq_nil_iff as).1 this with ha' | ha' <;> simp_all
      · left
        rw [← unescapeArgs_escapeArgs ha, h, unescapeArgs_escapeArgs hb]
  · rintro (rfl | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> rfl

/-- Injectivity away from the one collision. -/
theorem escapeArgs_injective {as bs : List (List UInt8)} (ha : as ≠ [[]]) (hb : bs ≠ [[]])
    (h : escapeArgs as = escapeArgs bs) : as = bs := by
  rw [← unescapeArgs_escapeArgs ha, h, unescapeArgs_escapeArgs hb]

/-- A single argument is recovered from its escaped form. -/
theorem escapeArg_injective {a b : List UInt8} (h : escapeArg a = escapeArg b) : a = b := by
  have := escapeArgs_eq_iff [a] [b]
  simp only [escapeArgs] at this
  rcases this.1 h with h | ⟨h, _⟩ | ⟨h, _⟩ <;> simp_all

/-! ## Examples -/

/-- `["a", "b c"]` gives `a b\ c`. -/
example : escapeArgs [[97], [98, 32, 99]] = [97, 32, 98, 92, 32, 99] := by decide
/-- `["", "x"]` gives ` x`; `["a", "", "b"]` gives `a  b`. -/
example : escapeArgs [[], [120]] = [32, 120] := by decide
example : escapeArgs [[97], [], [98]] = [97, 32, 32, 98] := by decide
example : unescapeArgs [97, 32, 98, 92, 32, 99] = [[97], [98, 32, 99]] := by decide

end SudoersSpec.Escape
