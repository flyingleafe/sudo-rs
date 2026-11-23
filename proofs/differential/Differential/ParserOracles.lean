import SudoersSpec.Syntax.Oracles

/-!
# Test oracles for the parser dump (`proofs/parser/DUMP.md` sections 4 and 5)

The reference parser takes its environment as `Oracles`. For the comparison with the Rust dump
they are instantiated as follows:

* characters: the table that the Rust test `write_char_table` writes (`charOracleOfTable`);
* file system: a model of the documented fixture tree (`fixtureCanonicalize`); every other path
  does not exist (the corpus puts its command paths under `/sudoers-nx/`; cases that name an
  existing host path are listed by the Rust harness in `<OUT>.hostdep`);
* glob compilation: the error rule of `glob::Pattern::new` stated in DUMP.md (`globCompile`);
* `{:?}`: never reached (a NUL character is a control character, which no token that reaches
  `SudoString::new` or `SudoPath::try_from` accepts); `quote` stands in.
-/

namespace Differential.ParserOracles

open SudoersSpec.Syntax

/-! ## Character classes -/

/-- Membership in a sorted array of disjoint inclusive ranges (binary search). -/
def inRanges (rs : Array (Nat × Nat)) (n : Nat) : Bool := Id.run do
  let mut lo := 0
  let mut hi := rs.size
  for _ in [0:64] do
    if lo < hi then
      let mid := (lo + hi) / 2
      let (a, b) := rs[mid]!
      if n < a then hi := mid
      else if n > b then lo := mid + 1
      else return true
  return false

/-- Parse a hexadecimal number. -/
def hexNat? (s : String) : Option Nat :=
  if s.isEmpty then none else
  s.toList.foldl (fun acc c => do
    let v ← acc
    let d ← if '0' ≤ c && c ≤ '9' then some (c.toNat - '0'.toNat)
      else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 'a'.toNat + 10) else none
    some (v * 16 + d)) (some 0)

/-- The `CharOracle` of a character-class table (DUMP.md section 4). -/
def charOracleOfTable (text : String) : Except String CharOracle := do
  let mut tbl : List (String × Array (Nat × Nat)) := []
  for line in text.splitOn "\n" do
    match line.splitOn " " with
    | [name, a, b] =>
      if name == "unicode" then continue
      let some a := hexNat? a | throw s!"bad line {line}"
      let some b := hexNat? b | throw s!"bad line {line}"
      let cur := (tbl.lookup name).getD #[]
      tbl := (name, cur.push (a, b)) :: tbl.filter (·.1 != name)
    | [_, _] => continue
    | [""] => continue
    | _ => throw s!"bad line {line}"
  let get (n : String) : Array (Nat × Nat) := (tbl.lookup n).getD #[]
  let al := get "alphanumeric"
  let up := get "uppercase"
  let nu := get "numeric"
  let co := get "control"
  let ws := get "whitespace"
  return {
    isAlphanumeric := fun c => inRanges al c.toNat
    isUppercase := fun c => inRanges up c.toNat
    isNumeric := fun c => inRanges nu c.toNat
    isControl := fun c => inRanges co c.toNat
    isWhitespace := fun c => inRanges ws c.toNat }

/-! ## The fixture file system -/

def fixtureRoot : String := "/tmp/sudo-rs-parser-dump-fixture"

/-- A node of the modelled file system. -/
inductive Node where
  | dir
  | file
  | symlink (target : String)
  deriving DecidableEq

/-- The modelled tree: `/`, `/tmp` and the fixture of DUMP.md section 5. -/
def tree : List (String × Node) :=
  [("/", .dir), ("/tmp", .dir), (fixtureRoot, .dir),
   (fixtureRoot ++ "/bin", .dir), (fixtureRoot ++ "/bin/tool", .file),
   (fixtureRoot ++ "/bin/alias", .symlink "tool"), (fixtureRoot ++ "/link", .symlink "bin"),
   (fixtureRoot ++ "/sub", .dir), (fixtureRoot ++ "/incdir", .dir),
   (fixtureRoot ++ "/include", .file)]

/-- `Path::components` of an absolute path, as `none` (root), `some ".."` or `some name`;
empty and `.` components are dropped. -/
def components (p : String) : List String :=
  (p.splitOn "/").filter (fun c => c != "" && c != ".")

def joinPath (dir name : String) : String := if dir == "/" then "/" ++ name else dir ++ "/" ++ name

def parentDir (dir : String) : String :=
  match (components dir).dropLast with
  | [] => "/"
  | cs => "/" ++ "/".intercalate cs

/-- `realpath`: resolve the components `cs` from the canonical directory `cur`. -/
def resolve : Nat → String → List String → Option String
  | 0, _, _ => none
  | _, cur, [] => some cur
  | fuel + 1, cur, c :: cs =>
    match tree.lookup cur with
    | some .dir =>
      if c == ".." then resolve fuel (parentDir cur) cs
      else
        let cand := joinPath cur c
        match tree.lookup cand with
        | none => none
        | some (.symlink t) => resolve fuel cur (components t ++ cs)
        | some _ => resolve fuel cand cs
    | _ => none

def realpath (p : String) : Option String :=
  if p.startsWith "/" then resolve 64 "/" (components p) else none

/-- `common::resolve::canonicalize` on the modelled tree: the canonical parent joined with the
file name (a final `..` has none), and the result must exist. -/
def fixtureCanonicalize (p : String) : Canonical :=
  let cs := components p
  if !p.startsWith "/" then .err
  else if cs.isEmpty then .ok p
  else
    let parent := "/" ++ "/".intercalate cs.dropLast
    match realpath parent with
    | none => .err
    | some canon =>
      let last := cs.getLast!
      let recon := if last == ".." then canon else joinPath canon last
      match realpath recon with
      | some _ => .ok recon
      | none => .err

/-! ## glob 0.3.4 -/

/-- The error rule of `glob::Pattern::new` (DUMP.md section 5). -/
def globCheck (cs : Array Char) : Nat → Nat → Option GlobError
  | 0, _ => none
  | fuel + 1, i =>
    let n := cs.size
    if i ≥ n then none else
    match cs[i]! with
    | '*' =>
      let old := i
      let rec skip (f : Nat) (j : Nat) : Nat := match f with
        | 0 => j
        | f + 1 => if j < n && cs[j]! == '*' then skip f (j + 1) else j
      let i := skip n i
      let count := i - old
      if count > 2 then some ⟨old + 2, "wildcards are either regular `*` or recursive `**`"⟩
      else if count == 2 then
        if i == 2 || cs[i - count - 1]! == '/' then
          if i < n && cs[i]! == '/' then globCheck cs fuel (i + 1)
          else if i == n then none
          else some ⟨i, "recursive wildcards must form a single path component"⟩
        else some ⟨old - 1, "recursive wildcards must form a single path component"⟩
      else globCheck cs fuel i
    | '[' =>
      let findClose (from_ : Nat) : Option Nat := (cs.toList.drop from_).findIdx? (· == ']')
      if i + 4 ≤ n && cs[i + 1]! == '!' then
        match findClose (i + 3) with
        | some j => globCheck cs fuel (i + j + 4)
        | none => some ⟨i, "invalid range pattern"⟩
      else if i + 3 ≤ n && cs[i + 1]! != '!' then
        match findClose (i + 2) with
        | some j => globCheck cs fuel (i + j + 3)
        | none => some ⟨i, "invalid range pattern"⟩
      else some ⟨i, "invalid range pattern"⟩
    | _ => globCheck cs fuel (i + 1)

def globCompile (p : String) : Option GlobError :=
  globCheck p.toList.toArray (p.length + 1) 0

/-- The oracle bundle of the comparison. -/
def oracles (char : CharOracle) (debug : String → String) : Oracles where
  char := char
  fs := ⟨fixtureCanonicalize⟩
  glob := ⟨globCompile⟩
  fmt := ⟨debug, debug⟩

end Differential.ParserOracles
