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

/-! ## Settings (DUMP.md section 3), on the shared model `SudoersSpec.Settings` -/

/-- `[(name value) ...]` of `Settings::dump_fields`. -/
def fields (s : Settings.Settings) : String :=
  "[" ++ " ".intercalate (s.dumpFields.map fun (n, v) => s!"({n} {v})") ++ "]"

/-- How base B sets a field (`BASE_B` in `parser_dump.rs`). -/
inductive BaseB where
  | flag
  | negate
  | text (v : String)
  | integer (v : String)
  | list (v : List String)

def baseBTable : List (String × BaseB) :=
  [("always_query_group_plugin", .flag), ("always_set_home", .flag), ("env_reset", .negate),
   ("fqdn", .flag), ("ignore_dot", .negate), ("lecture", .text "always"),
   ("mailerpath", .text "/b/mailer"), ("mail_badpass", .negate), ("match_group_by_gid", .flag),
   ("use_pty", .negate), ("visiblepw", .flag), ("pwfeedback", .negate), ("rootpw", .flag),
   ("targetpw", .flag), ("noexec", .flag), ("noninteractive_auth", .flag),
   ("log_allowed", .negate), ("log_denied", .negate), ("insults", .flag), ("setenv", .flag),
   ("runcwd", .text "/b/cwd"), ("apparmor_profile", .text "b_profile"),
   ("umask", .integer "077"), ("umask_override", .flag), ("passwd_tries", .integer "7"),
   ("secure_path", .text "/b/bin"), ("verifypw", .text "any"), ("passwd_timeout", .integer "2"),
   ("timestamp_timeout", .integer "3"), ("timestamp_type", .text "ppid"),
   ("editor", .text "/b/editor"), ("env_editor", .negate), ("env_keep", .list ["B_KEEP"]),
   ("env_check", .list ["B_CHECK"]), ("env_delete", .list ["B_DELETE"])]

/-- Base B: base A with the modifiers of `baseBTable` applied in order. -/
def baseB : Settings.Settings :=
  baseBTable.foldl (fun s (name, how) =>
    let m : Option Settings.SettingsModifier := match how, Settings.set name with
      | .negate, _ => Settings.negate name
      | .flag, some (.Flag f) => some f
      | .text v, some (.Text t) => Settings.checkText t v
      | .integer v, some (.Integer i) => Settings.checkInteger i v
      | .list v, some (.List l) => some (Settings.buildList l .Set v)
      | _, _ => none
    match m with
    | some m => m.apply s
    | none => s) Settings.Settings.default

/-- A settings modifier, by its effect on base A and base B. -/
def setting (m : Settings.SettingsModifier) : String :=
  s!"(setting {fields (m.apply Settings.Settings.default)} {fields (m.apply baseB)})"

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
