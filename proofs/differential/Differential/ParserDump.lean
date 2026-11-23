import SudoersSpec.Syntax.Sudo
import SudoersSpec.Settings.Dump
import Differential.Quote
import Differential.ParserOracles

/-!
# The parser dump of the Lean reference parser (`proofs/parser/DUMP.md` section 1)

`dump O text` prints the result of `Syntax.parseSudoersWith Descriptions.test O` in the format
of `src/sudoers/test/parser_dump.rs` (a `cfg(test)` build: every description is `"elem"`).
-/

namespace Differential.ParserDump

open SudoersSpec SudoersSpec.Syntax
open Differential.Quote (quote)

def formatHeader : String := "parser-dump 2"

def list (f : α → String) (l : List α) : String := "[" ++ " ".intercalate (l.map f) ++ "]"
def span (s : Span) : String := s!"{s.start.1}:{s.start.2}-{s.stop.1}:{s.stop.2}"

def spec (f : α → String) : Spec α → String
  | .allow m => s!"(allow {metaS f m})"
  | .forbid m => s!"(forbid {metaS f m})"
where
  metaS (f : α → String) : Meta α → String
    | .all => "all"
    | .alias n => s!"(alias {quote n})"
    | .only x => s!"(only {f x})"

def specList (f : α → String) (l : SpecList α) : String := list (spec f) l

def ident : Identifier → String
  | .name n => s!"(name {quote n})"
  | .id n => s!"(id {n})"

def user : UserSpecifier → String
  | .user i => s!"(user {ident i})"
  | .group i => s!"(group {ident i})"
  | .nonunixGroup i => s!"(nonunix {ident i})"

def host (h : Hostname) : String := quote h

def command (c : Command) : String :=
  let (kind, args) := match c.args with
    | .prefix a => ("prefix", a)
    | .exact a => ("exact", a)
  s!"(cmd {quote c.pattern} ({kind} {list quote args}))"

def chdir : ChDir → String
  | .any => "any"
  | .path p => s!"(path {quote p})"

def modifier : Modifier → String
  | .passwd => "passwd" | .nopasswd => "nopasswd" | .setenv => "setenv"
  | .nosetenv => "nosetenv" | .exec => "exec" | .noexec => "noexec" | .noop => "noop"
  | .cwd c => s!"(cwd {chdir c})"
  | .apparmorProfile p => s!"(apparmor {quote p})"
  | .ignored s => s!"(ignored {span s})"

def runas : Option RunAs → String
  | none => "none"
  | some r => s!"(runas {specList user r.users} {specList ident r.groups})"

def entry (e : Option RunAs × CommandSpec) : String :=
  s!"(entry {runas e.1} {list modifier e.2.mods} {spec command e.2.cmd})"

def perm (p : SpecList Hostname × List (Option RunAs × CommandSpec)) : String :=
  s!"(perm {specList host p.1} {list entry p.2})"

def defs (f : α → String) (d : List (Def α)) : String :=
  list (fun d => s!"(def {quote d.name} {specList f d.items})") d

def scope : ConfigScope → String
  | .generic => "generic"
  | .host l => s!"(host {specList host l})"
  | .user l => s!"(user {specList user l})"
  | .runAs l => s!"(runas {specList user l})"
  | .command l => s!"(command {specList quote l})"

/-! ## Settings modifiers (DUMP.md section 3) -/

def listMode : Settings.ListMode → String
  | .Set => "set"
  | .Add => "add"
  | .Del => "del"

/-- The setting name and exact parsed payload, without applying the modifier. -/
def setting (m : Settings.SettingsModifier) : String :=
  s!"(setting {m.setting.name} {payload m})"
where
  payload : Settings.SettingsModifier → String
    | .always_query_group_plugin v | .always_set_home v | .env_reset v | .fqdn v | .ignore_dot v
    | .mail_badpass v | .match_group_by_gid v | .use_pty v | .visiblepw v | .pwfeedback v
    | .rootpw v | .targetpw v | .noexec v | .noninteractive_auth v | .log_allowed v | .log_denied v
    | .insults v | .setenv v | .umask_override v | .env_editor v => Settings.dumpBool v
    | .umask v | .passwd_tries v | .passwd_timeout v | .timestamp_timeout v => toString v
    | .lecture v => v.dump
    | .verifypw v => v.dump
    | .timestamp_type v => Settings.dumpTimestampType v
    | .editor v => quote v
    | .mailerpath v | .runcwd v | .apparmor_profile v | .secure_path v =>
        match v with
        | none => "none"
        | some s => s!"(some {quote s})"
    | .env_keep (mode, items) | .env_check (mode, items) | .env_delete (mode, items) =>
        s!"({listMode mode} {list quote items})"

#guard setting (.mailerpath none) == "(setting mailerpath none)"
#guard setting (.mailerpath (some "")) == "(setting mailerpath (some \"\"))"

def sudo : Sudo → String
  | .spec p => s!"(spec {specList user p.users} {list perm p.permissions})"
  | .decl (.userAlias d) => s!"(user_alias {defs user d})"
  | .decl (.hostAlias d) => s!"(host_alias {defs host d})"
  | .decl (.cmndAlias d) => s!"(cmnd_alias {defs command d})"
  | .decl (.runasAlias d) => s!"(runas_alias {defs user d})"
  | .decl (.defaults mods s) => s!"(defaults {scope s} {list setting mods})"
  | .include p s => s!"(include {quote p} {span s})"
  | .includeDir p s => s!"(includedir {quote p} {span s})"
  | .lineComment => "comment"

def record : Parsed Sudo → String
  | .ok s => "ok " ++ sudo s
  | .error (.fatal sp k) => s!"fatal {span sp} {quote k.render}"
  | .error .reject => "reject"

/-- The dump of a text: one record per item, or the single record `panic "message"`. -/
def dump (O : Oracles) (text : String) : String :=
  match parseSudoersWith .test O text.toList with
  | .ok items => String.join (items.map fun i => record i ++ "\n")
  | .error msg => s!"panic {quote msg}\n"

end Differential.ParserDump
