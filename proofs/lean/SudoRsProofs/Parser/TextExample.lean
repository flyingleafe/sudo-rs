import SudoRsProofs.Parser.Examples
import SudoRsProofs.Parser.EndToEnd

/-!
# `text_to_authorization` on one concrete sudoers file

The include-free end-to-end theorem is applied to the ordinary text

```
Defaults !use_pty
alice ALL = (root) NOPASSWD: ALL
```

with a fixture of three synthetic accounts (`alice`, `bob`, `root`, each with its own primary
group), the host `box`, the invoking account `alice` and two resolved requests. The target user
and group are fixed, while the command is an arbitrary opaque `std.path.Path`:

* `alice` asks to run as `root` with group `root`. The run of the extracted
  `analyze_text`, `Sudoers::check` and `Judgement::authorization` reports no diagnostic.
  Its flags are `NOPASSWD` together with the implicit `SETENV` of `ALL`. It returns `Allowed`
  with `must_authenticate = false`, `use_pty = false` (from the `Defaults` line) and
  `trust_environment = true` (`text_allows`).
* `alice` asks to run as `bob` with group `bob`. The runas list `(root)` excludes `bob`, so
  the same run returns no flags and `Forbidden` (`text_refuses`).

The concrete outcomes are not assumed. `domain_eval`, `allowed_eval` and `refused_eval` evaluate
the independent reference (`SudoersSpec.Syntax.parseSudoers`, `collect`, `orderAliases`,
`settingsInForce`, `authorize`, `authorization`) on this text by definitional unfolding
(`rfl`, rechecked by the kernel). The general theorem then transfers them to the
extracted run.

Discharged here: the input-room bound, the `LocalFile` domain (no include, collection budget, no
item that needs a diagnostic path; read off the reference parse), the host-name length, the
`InstOracle` agreement of the fixture's `UnixUser`/`UnixGroup`/`PartialEq` instances, and
`SudoRsHosts`. Policy well-formedness, Defaults provenance and settings ranges are already
discharged inside `text_to_authorization`.

The remaining hypotheses are only the primitive agreements about opaque models. No proof
discharges them:

* `P2Oracle A E`: the Rust Unicode wrappers, `canonicalize`, `compile_pattern` and `os_string`
  at the parser boundary agree with the reference oracles `E`;
* `Latin1Agrees E.char`: the reference character oracle is `CharOracle.latin1` below
  `U+0100`, which `proofs/spec/SudoersSpec/Syntax/README.md` records as compared with the
  pinned `rustc` (the same condition as `Parser/Examples.lean`);
* `Analysis.RenderAgrees`: the opaque diagnostic renderer;
* `GlobOracle A (acctOracle g)`: the opaque glob matcher and the `OsString` abstraction. The
  file says `ALL`, so the reference never queries `g`, and `g` and `A` are arbitrary.

Their joint satisfiability is not proved in Lean. They concern opaque constants. The accounts are
a finite fixture, not NSS, and nothing here executes a binary. The fixture follows
`NonVacuity.lean`, but its users carry names because the file names `alice` and `root`.
-/

open Aeneas Aeneas.Std Result sudo_rs
open SudoersSpec

namespace SudoRsProofs.Parser.TextExample

/-! ## Generic glue: from a `TextAgreement` run to reference observations -/

/-- `(mustAuthenticate, usePty, trustEnvironment)` of an allowed authorization. -/
def allowedView {σ : Type} : SudoersSpec.Authorization σ → Option (Bool × Bool × Bool)
  | .allowed a r => some (a.mustAuthenticate, r.usePty, r.trustEnvironment)
  | .forbidden => none

/-- The reference authorization of `authorizationOfText` for collected items. -/
def refAuthorization {U G : Type} (O : SudoersSpec.Oracle U G) (req : SudoersSpec.Request U G)
    (c : SudoersSpec.Analysis.Collected) : SudoersSpec.Authorization Settings.StrSet :=
  SudoersSpec.authorization
    (SudoersSpec.Analysis.settingsInForce O (SudoersSpec.Analysis.policyOf c).aliases c req
      Settings.Settings.default).toDefaults
    (SudoersSpec.authorize O (SudoersSpec.Analysis.policyOf c) req)

/-- What the example observes: diagnostic messages, decision, and the allowed terms. -/
abbrev Outcome := List String × Option SudoersSpec.Tag × Option (Bool × Bool × Bool)

def outcomeOf {U G : Type} (O : SudoersSpec.Oracle U G) (req : SudoersSpec.Request U G)
    (c : SudoersSpec.Analysis.Collected) : Outcome :=
  (c.diagnostics.map Prod.snd ++ (SudoersSpec.Analysis.orderAliases c.written).2,
    SudoersSpec.authorize O (SudoersSpec.Analysis.policyOf c) req,
    allowedView (Settings.observeAuthorization (refAuthorization O req c)))

/-- The reference outcome of a text: parse, collect, then `outcomeOf`. -/
def referenceOutcome {U G : Type} (E : Syntax.Oracles) (O : SudoersSpec.Oracle U G)
    (src : List Char) (req : SudoersSpec.Request U G) : Option Outcome :=
  (Syntax.parseSudoers E src).toOption.bind fun items =>
    (SudoersSpec.Analysis.collect items).map (outcomeOf O req)

section Glue

variable {U G UG : Type} {A : GlobAbs} {E : Syntax.Oracles} {O : SudoersSpec.Oracle U G}
  {ui : system.interface.UnixUser U UG} {eqi : core.cmp.PartialEq U U}
  {gi : system.interface.UnixGroup G} {path : std.path.Path} {source : Option std.path.PathBuf}
  {src : Slice Char} {invoker : U} {host : system.Hostname} {req : sudoers.Request U G UG}
  {x : FileRun}

/-- The reference outcome on the run's own text is the outcome of the run's collected items. -/
theorem referenceOutcome_of_run (h : TextAgreement A E O ui eqi gi path source src invoker host req x) :
    referenceOutcome E O src.val (absRequest A invoker host req) =
      some (outcomeOf O (absRequest A invoker host req) x.collected) := by
  unfold referenceOutcome
  rw [h.parsed]
  exact congrArg (Option.map (outcomeOf O (absRequest A invoker host req))) h.collected

/-- The extracted terms, observed, are the reference terms of the run's collected items. -/
theorem terms_of_run (h : TextAgreement A E O ui eqi gi path source src invoker host req x) :
    Settings.observeAuthorization (absAuthorization x.terms) =
      Settings.observeAuthorization (refAuthorization O (absRequest A invoker host req) x.collected) := by
  have e : (SudoersSpec.Analysis.authorizationOfText E O src.val (absRequest A invoker host req)).map
      Settings.observeAuthorization =
      some (Settings.observeAuthorization (refAuthorization O (absRequest A invoker host req) x.collected)) := by
    simp [SudoersSpec.Analysis.authorizationOfText, h.parsed, Except.toOption, h.collected,
      refAuthorization]
  exact Option.some.inj (h.result.symm.trans e)

/-- No collected diagnostic and no sanitizer message: the real analyzer's vector is empty. -/
theorem clean_of_messages (h : TextAgreement A E O ui eqi gi path source src invoker host req x)
    (hm : x.collected.diagnostics.map Prod.snd ++
      (SudoersSpec.Analysis.orderAliases x.collected.written).2 = []) :
    x.diagnostics.val = [] :=
  List.map_eq_nil_iff.mp (h.policy.messages.trans hm)

end Glue

/-- Reading the allowed view back on the extracted `Authorization`. -/
theorem allowed_of_view (t : sudoers.policy.Authorization sudoers.policy.Restrictions)
    (ht : allowedView (Settings.observeAuthorization (absAuthorization t)) = some (false, false, true)) :
    ∃ a r, t = .Allowed a r ∧ a.must_authenticate = false ∧ r.use_pty = false ∧
      r.trust_environment = true := by
  cases t with
  | Allowed a r =>
    have hv : (a.must_authenticate, r.use_pty, r.trust_environment) = (false, false, true) :=
      Option.some.inj ht
    simp only [Prod.mk.injEq] at hv
    exact ⟨a, r, rfl, hv.1, hv.2.1, hv.2.2⟩
  | Forbidden => simp [allowedView, Settings.observeAuthorization, absAuthorization] at ht

/-! ## The fixture -/

theorem fitsUsize {n : Nat} (h : n ≤ 4294967295) : n ≤ Usize.max :=
  h.trans Usize.cMax_bound_concrete.1

/-- Three synthetic accounts; each one's primary group is the group of the same name. -/
inductive Acct where
  | alice
  | bob
  | root
  deriving DecidableEq

def Acct.login : Acct → String
  | .alice => "alice"
  | .bob => "bob"
  | .root => "root"

/-- The uid of an account, which is also the gid of its primary group. -/
def Acct.uid : Acct → U32
  | .alice => 1000#u32
  | .bob => 1001#u32
  | .root => 0#u32

def acctGroups : system.interface.UnixGroup Acct where
  as_gid grp := ok grp.uid
  try_as_name _ := ok none

/-- Every account is a member of exactly its own primary group. -/
def acctUsers : system.interface.UnixUser Acct Acct where
  UnixGroupInst := acctGroups
  has_name u s := ok (decide (s.val = sudo_rs.stringBytes u.login))
  has_uid u n := ok (u.uid == n)
  is_root u := ok (decide (u = .root))
  in_group_by_name _ _ := ok false
  in_group_by_gid u n := ok (u.uid == n)
  group u := ok u

def acctEq : core.cmp.PartialEq Acct Acct where
  eq u v := ok (decide (u = v))
  ne u v := ok (!decide (u = v))

/-- The oracle of the fixture. The glob predicate is a parameter; the example's file never
queries it. -/
def acctOracle (g : String → String → Bool) : SudoersSpec.Oracle Acct Acct where
  hasName u n := decide (n = u.login)
  hasUid u n := u.uid.val == n
  isRoot u := decide (u = .root)
  inGroupByName _ _ := false
  inGroupByGid u n := u.uid.val == n
  userEq u v := decide (u = v)
  asGid grp := grp.uid.val
  tryAsName _ := none
  globMatches := g
  hostMatches := (· == ·)

theorem acctInstOracle (g : String → String → Bool) :
    InstOracle acctUsers acctEq acctGroups (acctOracle g) where
  has_name u s n hs := by
    show ok (decide (s.val = sudo_rs.stringBytes u.login)) = ok (decide (n = u.login))
    rw [hs]
    exact congrArg ok (decide_eq_decide.mpr stringBytes_inj)
  has_uid _ _ := by simp [acctUsers, acctOracle, UScalar.eq_equiv]
  is_root _ := rfl
  in_group_by_name _ _ := rfl
  in_group_by_gid _ _ := by simp [acctUsers, acctOracle, UScalar.eq_equiv]
  eq _ _ := rfl
  ne _ _ := rfl
  as_gid _ := by simp [acctGroups, acctOracle]
  try_as_name _ := by
    simp [acctGroups, acctOracle]
    rfl

def boxHost : system.Hostname := ⟨"box"⟩

theorem boxHost_fits : Fits boxHost.inner := by
  change 3 ≤ Usize.max
  exact fitsUsize (by decide)

/-- A resolved request: the target user, that user's primary group, a command path and no
arguments. -/
def textRequest (target : Acct) (cmd : std.path.Path) : sudoers.Request Acct Acct Acct :=
  ⟨target, target, cmd, .from [] (by decide)⟩

/-- The sudoers text as the character slice `Sudoers::read` passes to `analyze_text`. -/
def textSrc : Slice Char :=
  Slice.from "Defaults !use_pty\nalice ALL = (root) NOPASSWD: ALL\n".toList (by
    have : "Defaults !use_pty\nalice ALL = (root) NOPASSWD: ALL\n".toList.length = 51 := by decide
    rw [this]; scalar_tac)

theorem textRoom : 1 + 2 * textSrc.val.length ≤ Usize.max := by
  have : textSrc.val.length = 51 := by
    simp only [textSrc, Slice.from_val]; decide
  rw [this]; scalar_tac

/-- The `NOPASSWD` tag of the line, with the implicit `SETENV` of a literal `ALL`. -/
def nopasswdAll : SudoersSpec.Tag := { authenticate := .nopasswd, env := .setenv }

/-! ## The reference side, evaluated -/

/-- The reference parser with `latin1` below `U+0100`, equal to `E` under `Latin1Agrees`. -/
def latinEnv (E : Syntax.Oracles) : Syntax.Oracles := ⟨latin1Below E.char, E.fs, E.glob, E.fmt⟩

theorem latinEnv_eq {E : Syntax.Oracles} (h : Latin1Agrees E.char) : latinEnv E = E := by
  obtain ⟨c, fs, gl, fm⟩ := E
  exact congrArg (fun ch => (⟨ch, fs, gl, fm⟩ : Syntax.Oracles)) (latin1Below_eq (O := c) h)

/-- Neither include, nor parse error, nor ignored tag. -/
def Plain : SudoRsProofs.Parser.Analysis.Item → Bool
  | .error _ => false
  | .ok (.spec r) => (SudoersSpec.Analysis.ignoredSpans r).isEmpty
  | .ok (.decl _) => true
  | .ok (.include _ _) => false
  | .ok (.includeDir _ _) => false
  | .ok .lineComment => true

/-- The `LocalFile` domain, decided on reference items. -/
def domainOK (items : List SudoRsProofs.Parser.Analysis.Item) : Bool :=
  items.all Plain && decide ((items.map SudoRsProofs.Parser.Analysis.Ref.itemSize).sum ≤ 64)

theorem localFile_of_domain {path : std.path.Path} {source : Option std.path.PathBuf}
    {items : List SudoRsProofs.Parser.Analysis.Item} (h : domainOK items = true) :
    SudoRsProofs.Parser.Analysis.LocalFile path source items := by
  simp only [domainOK, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  obtain ⟨plain, size⟩ := h
  refine ⟨fun p span => ⟨fun hm => ?_, fun hm => ?_⟩, size.trans (fitsUsize (by decide)), ?_⟩
  · have hp := plain _ hm
    simp [Plain] at hp
  · have hp := plain _ hm
    simp [Plain] at hp
  · intro i hi hn
    have hp := plain i hi
    rcases i with s | line
    · simp [Plain] at hp
    · cases line with
      | spec r =>
        simp only [Plain, List.isEmpty_iff] at hp
        exact False.elim (hn hp)
      | _ => exact False.elim hn

set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
/-- The reference parse of the text is in the `LocalFile` domain (whatever the oracles above
`U+00FF` and the file-system, glob and formatting oracles are). -/
theorem domain_eval (E : Syntax.Oracles) :
    (Syntax.parseSudoers (latinEnv E) textSrc.val).toOption.map domainOK = some true := by
  simp only [textSrc, Slice.from_val]; rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
/-- Reference outcome of `alice` as `root:root`: no message, `NOPASSWD` + implicit `SETENV`,
allowed without authentication, `use_pty` off, environment trusted. -/
theorem allowed_eval (E : Syntax.Oracles) (g : String → String → Bool) (A : GlobAbs)
    (cmd : std.path.Path) :
    referenceOutcome (latinEnv E) (acctOracle g) textSrc.val
        (absRequest A .alice boxHost (textRequest .root cmd)) =
      some ([], some nopasswdAll, some (false, false, true)) := by
  simp only [textSrc, Slice.from_val, textRequest, absRequest]; rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
/-- Reference outcome of `alice` as `bob:bob`: no message, denied. -/
theorem refused_eval (E : Syntax.Oracles) (g : String → String → Bool) (A : GlobAbs)
    (cmd : std.path.Path) :
    referenceOutcome (latinEnv E) (acctOracle g) textSrc.val
        (absRequest A .alice boxHost (textRequest .bob cmd)) =
      some ([], none, none) := by
  simp only [textSrc, Slice.from_val, textRequest, absRequest]; rfl

theorem textLocalFile {E : Syntax.Oracles} (latin1 : Latin1Agrees E.char) (path : std.path.Path)
    (source : Option std.path.PathBuf) (items : List SudoRsProofs.Parser.Analysis.Item)
    (hp : Syntax.parseSudoers E textSrc.val = .ok items) :
    SudoRsProofs.Parser.Analysis.LocalFile path source items := by
  have ev := domain_eval E
  rw [latinEnv_eq latin1, hp] at ev
  exact localFile_of_domain (Option.some.inj ev)

/-! ## The instantiation -/

/-- `text_to_authorization` on the text, with every non-primitive hypothesis discharged. -/
theorem textRun {A : GlobAbs} {E : Syntax.Oracles} {g : String → String → Bool}
    (parserEnv : P2Oracle A E) (latin1 : Latin1Agrees E.char)
    (render : SudoRsProofs.Parser.Analysis.RenderAgrees) (hG : GlobOracle A (acctOracle g))
    (path : std.path.Path) (source : Option std.path.PathBuf) (target : Acct) (cmd : std.path.Path) :
    ∃ x, TextAgreement A E (acctOracle g) acctUsers acctEq acctGroups path source textSrc .alice
      boxHost (textRequest target cmd) x :=
  text_to_authorization parserEnv render (acctInstOracle g) hG (fun _ _ => rfl) path source textSrc
    textRoom (textLocalFile latin1 path source) .alice boxHost boxHost_fits (textRequest target cmd)

/-- **Allowed.** The extracted analyzer, `check` and `authorization` on the text for `alice`
running as `root:root`: clean diagnostics, `NOPASSWD` with the implicit `SETENV` of `ALL`, and
`Allowed` without authentication, without a pty (the text's `Defaults !use_pty`) and with the
environment trusted. -/
theorem text_allows {A : GlobAbs} {E : Syntax.Oracles} {g : String → String → Bool}
    (parserEnv : P2Oracle A E) (latin1 : Latin1Agrees E.char)
    (render : SudoRsProofs.Parser.Analysis.RenderAgrees) (hG : GlobOracle A (acctOracle g))
    (path : std.path.Path) (source : Option std.path.PathBuf) (cmd : std.path.Path) :
    ∃ x, TextAgreement A E (acctOracle g) acctUsers acctEq acctGroups path source textSrc .alice
        boxHost (textRequest .root cmd) x ∧
      x.diagnostics.val = [] ∧
      x.judgement.flags.map absTag = some nopasswdAll ∧
      ∃ a r, x.terms = .Allowed a r ∧ a.must_authenticate = false ∧ r.use_pty = false ∧
        r.trust_environment = true := by
  obtain ⟨x, h⟩ := textRun parserEnv latin1 render hG path source .root cmd
  have ev := allowed_eval E g A cmd
  rw [latinEnv_eq latin1, referenceOutcome_of_run h] at ev
  have hv := Option.some.inj ev
  have hmsgs : x.collected.diagnostics.map Prod.snd ++
      (SudoersSpec.Analysis.orderAliases x.collected.written).2 = [] :=
    congrArg (fun d : Outcome => d.1) hv
  have hfl : SudoersSpec.authorize (acctOracle g) (SudoersSpec.Analysis.policyOf x.collected)
      (absRequest A .alice boxHost (textRequest .root cmd)) = some nopasswdAll :=
    congrArg (fun d : Outcome => d.2.1) hv
  have hview : allowedView (Settings.observeAuthorization (refAuthorization (acctOracle g)
      (absRequest A .alice boxHost (textRequest .root cmd)) x.collected)) = some (false, false, true) :=
    congrArg (fun d : Outcome => d.2.2) hv
  exact ⟨x, h, clean_of_messages h hmsgs, h.flags.trans hfl,
    allowed_of_view x.terms ((congrArg allowedView (terms_of_run h)).trans hview)⟩

/-- **Refused.** The same text and invoking user, asking for `bob:bob`: the runas list `(root)`
does not contain `bob`, so the run has no flags and returns `Forbidden`. -/
theorem text_refuses {A : GlobAbs} {E : Syntax.Oracles} {g : String → String → Bool}
    (parserEnv : P2Oracle A E) (latin1 : Latin1Agrees E.char)
    (render : SudoRsProofs.Parser.Analysis.RenderAgrees) (hG : GlobOracle A (acctOracle g))
    (path : std.path.Path) (source : Option std.path.PathBuf) (cmd : std.path.Path) :
    ∃ x, TextAgreement A E (acctOracle g) acctUsers acctEq acctGroups path source textSrc .alice
        boxHost (textRequest .bob cmd) x ∧
      x.diagnostics.val = [] ∧ x.judgement.flags = none ∧ x.terms = .Forbidden := by
  obtain ⟨x, h⟩ := textRun parserEnv latin1 render hG path source .bob cmd
  have ev := refused_eval E g A cmd
  rw [latinEnv_eq latin1, referenceOutcome_of_run h] at ev
  have hv := Option.some.inj ev
  have hmsgs : x.collected.diagnostics.map Prod.snd ++
      (SudoersSpec.Analysis.orderAliases x.collected.written).2 = [] :=
    congrArg (fun d : Outcome => d.1) hv
  have hfl : SudoersSpec.authorize (acctOracle g) (SudoersSpec.Analysis.policyOf x.collected)
      (absRequest A .alice boxHost (textRequest .bob cmd)) = none :=
    congrArg (fun d : Outcome => d.2.1) hv
  have hnone : x.judgement.flags = none := by
    have hf : x.judgement.flags.map absTag = none := h.flags.trans hfl
    cases e : x.judgement.flags with
    | none => rfl
    | some t =>
      rw [e] at hf
      simp at hf
  exact ⟨x, h, clean_of_messages h hmsgs, hnone, h.denied.mpr hfl⟩

end SudoRsProofs.Parser.TextExample
