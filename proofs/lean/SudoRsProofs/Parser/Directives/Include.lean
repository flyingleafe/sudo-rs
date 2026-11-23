import SudoRsProofs.Parser.Analysis.Abs
import SudoRsProofs.Parser.Directives.IncludeTokens
import SudoRsProofs.Parser.Directives.Keywords
import SudoRsProofs.Parser.PermissionLines.Common
import SudoRsProofs.Parser.Username

/-! Include dispatch and path parsing in the release extraction, with remote sudoers disabled. -/

open Aeneas Aeneas.Std Result SudoersSpec
open sudo_rs
open SudoersSpec.Syntax (Parser)

namespace SudoRsProofs.Parser

private theorem fatal_from_refines {T α : Type} (f : T → α)
    {pos : Usize × Usize} {s : CS} (hs : StreamOK s) {k : RKind} {k' : Syntax.ErrKind}
    (hk : KindRel k k') :
    Refines f (do
      let r ← sudoers.basic_parser.fatal_from T pos s k
      ok (r, s))
      ((Parser.fatalFrom (pos.1.val, pos.2.val) k').run (absStream s)) := by
  simp only [fatal_from_eq, bind_ok, Parser.run_fatalFrom, refines_ok_iff, ResultRel.err_err]
  exact ⟨StatusRel.from hk, hs, trivial⟩

private theorem option_char_eq_some (next : Option Char) (c : Char) :
    core.option.Option.Insts.CoreCmpPartialEqOption.eq
      sudo_rs.Char.Insts.CoreCmpPartialEqChar next (some c) = ok (next == some c) := by
  cases next <;> rfl

/-- Parse the path and retain the span from the directive keyword to the final cursor. -/
theorem include_path_refines {O : Syntax.Oracles} (hO : P2CharOracle O.char)
    (keyPos : Usize × Usize) {s : CS} (hs : StreamOK s) :
    Refines (fun z => (z.1, absSpan z.2)) (sudoers.ast.include_path s keyPos)
      ((Syntax.getPath O .release (keyPos.1.val, keyPos.2.val)).run (absStream s)) := by
  obtain ⟨s1, e1, h1, a1⟩ := eat_char_eq hs '"'
  simp only [sudoers.ast.include_path, Syntax.getPath, Parser.run_bind, Parser.run_eatChar, e1,
    bind_ok, uncurry_apply_pair, ← a1]
  cases ((absStream s).eatChar '"').1 with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte, get_pos_eq', bind_ok, Parser.run_bind,
      Parser.run_getPos, absStream_getPos]
    obtain ⟨r, s2, e2, hr, h2, a2⟩ :=
      expect_nonterminal_refines (include_path_parse_refines hO) include_path_description h1
    rcases hp : (Syntax.expectNonterminal Syntax.Descriptions.release.includePath
      (Syntax.token (Syntax.includePathToken O.char))).run (absStream s1) with ⟨r', t⟩
    simp only [e2, bind_ok, uncurry_apply_pair]
    rw [hp] at hr a2
    simp only at a2
    subst t
    rcases r with path | err <;> rcases r' with err' | path' <;> simp only [ResultRel] at hr
    · change path = path' at hr
      subst path'
      simp only [branch_Ok, bind_ok, Parser.run_peek]
      by_cases hn : (absStream s2).peek = some '\n'
      · simp [peek_eq, option_char_eq_some, hn, bne, Parser.run_bind, h2, absSpan]
      · have hbeq : ((absStream s2).peek == some '\n') = false := by simpa using hn
        simp only [peek_eq, bind_ok, option_char_eq_some, hbeq, Bool.false_eq_true, ↓reduceIte,
          bne, Bool.not_false]
        -- The bare path succeeded but the next character is not a newline.
        simpa only [Parser.run_bind, Parser.run_fatalFrom] using
          (fatal_from_refines (fun z : String × sudoers.basic_parser.Span => (z.1, absSpan z.2))
            (pos := (s1.line, s1.col)) h2 KindRel.quotesAroundFilenames)
    · simp [hr, h2]
  | true =>
    simp only [↓reduceIte, Parser.run_bind]
    obtain ⟨r, s2, e2, hr, h2, a2⟩ :=
      expect_nonterminal_refines (quoted_include_path_parse_refines hO) quoted_include_path_description h1
    rcases hp : (Syntax.expectNonterminal Syntax.Descriptions.release.quotedIncludePath
      (Syntax.token (Syntax.quotedIncludePathToken O.char))).run (absStream s1) with ⟨r', t⟩
    simp only [e2, bind_ok, uncurry_apply_pair]
    rw [hp] at hr a2
    simp only at a2
    subst t
    rcases r with path | err <;> rcases r' with err' | path' <;> simp only [ResultRel] at hr
    · change path = path' at hr
      subst path'
      obtain ⟨r3, s3, e3, hr3, h3, a3⟩ := expect_syntax_refines h2 '"'
      rcases hc : (Syntax.expectSyntax '"').run (absStream s2) with ⟨r3', t3⟩
      simp only [branch_Ok, e3, bind_ok, uncurry_apply_pair, hc]
      rw [hc] at hr3 a3
      simp only at a3
      subst t3
      rcases r3 with ⟨⟩ | err <;> rcases r3' with err' | ⟨⟩ <;> simp only [ResultRel] at hr3
      · simp [h3, absSpan]
      · simp [hr3, h3]
    · simp [hr, h2]

/-- With `unstable-remote-sudoers` disabled, the remote branch is always an unknown directive. -/
theorem parse_remote_refines (A : GlobAbs) (keyword : String) (keyPos : Usize × Usize)
    {s : CS} (hs : StreamOK s) :
    Refines (Analysis.absSudo A) (sudoers.ast.parse_remote keyword s keyPos)
      ((Parser.fatalFrom (keyPos.1.val, keyPos.2.val) .unknownDirective).run (absStream s)) := by
  unfold sudoers.ast.parse_remote
  exact fatal_from_refines (Analysis.absSudo A) hs KindRel.unknownDirective

private theorem include_keyword_value_bound {O : Syntax.Oracles} {s t : Syntax.Stream}
    {word : String} (h : (Syntax.tryNonterminal (Syntax.parseOption
      (Syntax.token (Syntax.usernameToken O)))).run s = (.ok (some word), t)) :
    word.utf8ByteSize ≤ Usize.max := by
  obtain ⟨key, s1, hk, htail⟩ := Parser.run_bind_eq_ok.mp h
  obtain ⟨_, _, _, hret⟩ := Parser.run_bind_eq_ok.mp htail
  simp only [Parser.run_pure, Prod.mk.injEq, Except.ok.injEq] at hret
  obtain ⟨rfl, _⟩ := hret
  simp only [Syntax.parseOption, Parser.run_maybe] at hk
  rcases ht : (Syntax.token (Syntax.usernameToken O)).run s with ⟨r, t'⟩
  rw [ht] at hk
  rcases r with (⟨sp, kind⟩ | _) | text <;> simp at hk
  have htext : text = word := hk.1
  subst text
  exact username_token_value_bound ht

/-- The release include production refines `Syntax.parseInclude` on every representable cursor. -/
theorem parse_include_refines {O : Syntax.Oracles} (A : GlobAbs) (hO : P2CharOracle O.char)
    {s : CS} (hs : StreamOK s) :
    Refines (Analysis.absSudo A) (sudoers.ast.parse_include s)
      ((Syntax.parseInclude O .release).run (absStream s)) := by
  obtain ⟨r, s1, er, hr, h1, a1⟩ :=
    try_nonterminal_refines (option_parse_refines (username_parse_refines hO)) hs
  rcases hk : (Syntax.tryNonterminal (Syntax.parseOption
    (Syntax.token (Syntax.usernameToken O)))).run (absStream s) with ⟨r', t⟩
  simp only [sudoers.ast.parse_include, Syntax.parseInclude, Parser.run_bind, Parser.run_getPos,
    absStream_getPos, get_pos_eq', er, bind_ok, uncurry_apply_pair, hk]
  rw [hk] at hr a1
  simp only at a1
  subst t
  rcases r with u | err <;> rcases r' with err' | key <;> simp only [ResultRel] at hr
  · cases u with
    | none =>
      cases key with
      | none =>
        simp only [branch_Ok, bind_ok]
        exact fatal_from_refines (Analysis.absSudo A) h1 KindRel.unknownDirective
      | some word => cases hr
    | some u =>
      cases key with
      | none => cases hr
      | some word =>
        change some u.str = some word at hr
        have hword := Option.some.inj hr
        have hbound := include_keyword_value_bound hk
        have heFile := equals_keyword_eq word "include" sudoers.ast.INCLUDE include_val hbound
        have heDir := equals_keyword_eq word "includedir" sudoers.ast.INCLUDEDIR includedir_val hbound
        simp only [branch_Ok, bind_ok, sudoers.tokens.sudo_string_text, hword, heFile, heDir]
        by_cases hf : word = "include" <;> first
        | rw [hf]
          simp only [beq_self_eq_true, ↓reduceIte]
        | by_cases hd : word = "includedir" <;> first
          | rw [hd]
            have hne : ("includedir" == "include") = false := rfl
            simp only [hne, beq_self_eq_true, Bool.false_eq_true, ↓reduceIte]
          | have hbf : (word == "include") = false := by simpa using hf
            have hbd : (word == "includedir") = false := by simpa using hd
            simp only [hbf, hbd, Bool.false_eq_true, ↓reduceIte]
            split <;> first
            | exact parse_remote_refines A word (s.line, s.col) h1
            | simp_all
        all_goals
          obtain ⟨pathResult, s2, e2, hr2, h2, a2⟩ := include_path_refines hO (s.line, s.col) h1
          rcases hp : (Syntax.getPath O .release (s.line.val, s.col.val)).run (absStream s1)
            with ⟨pathResult', t⟩
          simp only [Parser.run_bind, hp, e2, bind_ok, uncurry_apply_pair]
          rw [hp] at hr2 a2
          simp only at a2
          subst t
          rcases pathResult with ⟨path, span⟩ | st <;> rcases pathResult' with st' | ⟨path', span'⟩ <;>
            simp only [ResultRel, Prod.mk.injEq] at hr2
          · obtain ⟨rfl, rfl⟩ := hr2
            simp [Analysis.absSudo, h2]
          · simp [hr2, h2]
  · simp [hr, h1]

end SudoRsProofs.Parser
