import SudoersSpec.Settings.Values
import SudoersSpec.Authorization

/-!
# The `Defaults` settings as data

Transcribes `src/defaults` (`mod.rs`, the table of the `defaults!` DSL, and what
`settings_dsl.rs` generates from it) one to one: the 35 settings, their kinds, the `Settings`
structure with its initial values, the modifiers of a `Defaults` entry and their effect, and the
functions the `Defaults` parser calls (`negate`, `set`, `check_integer`, `check_text`,
`build_list`).

Names and the order of constructors and fields are those of the Rust code (table order), so the
refinement proofs of `proofs/lean` only unfold. Rust `u64` values are `Nat`, `Box<str>` values
are `String`, the `HashSet<String>` lists are `StrSet` (below).
-/

namespace SudoersSpec.Settings

/-! ## String sets -/

/-- The value of a list setting (`HashSet<String>`), as a list of its elements. Two values are
the same set when they have the same elements (`StrSet.Equiv`). The operations follow the list
model of `HashSet` in `proofs/lean` (`insert` puts a new key first unless present, `remove`
filters), so that the refinement proofs hold with list equality; `applyList_equiv` shows that
the result as a set does not depend on the representation. -/
abbrev StrSet := List String

/-- `HashSet::insert`: add `x` unless present. -/
def StrSet.insert (s : StrSet) (x : String) : StrSet :=
  if s.contains x then s else x :: s

/-- `HashSet::remove`: drop `x`. -/
def StrSet.remove (s : StrSet) (x : String) : StrSet :=
  s.filter fun k => !(k == x)

/-- The same set: the same elements. -/
def StrSet.Equiv (a b : StrSet) : Prop := ∀ x, x ∈ a ↔ x ∈ b

/-! ## Settings, kinds, enumerations -/

/-- `defaults::Setting`: every setting, in table order. -/
inductive Setting where
  | always_query_group_plugin | always_set_home | env_reset | fqdn | ignore_dot | lecture
  | mailerpath | mail_badpass | match_group_by_gid | use_pty | visiblepw | pwfeedback | rootpw
  | targetpw | noexec | noninteractive_auth | log_allowed | log_denied | insults | setenv
  | runcwd | apparmor_profile | umask | umask_override | passwd_tries | secure_path | verifypw
  | passwd_timeout | timestamp_timeout | timestamp_type | editor | env_editor | env_keep
  | env_check | env_delete
  deriving DecidableEq, Repr

/-- `defaults::IntegerSetting`: the settings that take an integer. -/
inductive IntegerSetting where
  | umask | passwd_tries | passwd_timeout | timestamp_timeout
  deriving DecidableEq, Repr

/-- `defaults::TextSetting`: the settings that take a text or a keyword. -/
inductive TextSetting where
  | lecture | mailerpath | runcwd | apparmor_profile | secure_path | verifypw | timestamp_type
  | editor
  deriving DecidableEq, Repr

/-- `defaults::ListSetting`: the settings that are sets of strings. -/
inductive ListSetting where
  | env_keep | env_check | env_delete
  deriving DecidableEq, Repr

/-- `defaults::ListMode`: replace (`=`), add (`+=`), remove (`-=`). -/
inductive ListMode where
  | Set | Add | Del
  deriving DecidableEq, Repr

/-- `defaults::enums::lecture`. -/
inductive Lecture where
  | always | once | never
  deriving DecidableEq, Repr

/-- `defaults::enums::verifypw`. -/
inductive Verifypw where
  | all | always | any | never
  deriving DecidableEq, Repr

/-- `defaults::SYSTEM_EDITOR` on Linux. -/
def systemEditor : String := "/usr/bin/editor:/usr/bin/nano:/usr/bin/vi"

/-- `defaults::Settings`, field for field. `timestamp_type` is
`SudoersSpec.TimestampType` (`defaults::enums::timestamp_type`). -/
structure Settings where
  always_query_group_plugin : Bool
  always_set_home : Bool
  env_reset : Bool
  fqdn : Bool
  ignore_dot : Bool
  lecture : Lecture
  mailerpath : Option String
  mail_badpass : Bool
  match_group_by_gid : Bool
  use_pty : Bool
  visiblepw : Bool
  pwfeedback : Bool
  rootpw : Bool
  targetpw : Bool
  noexec : Bool
  noninteractive_auth : Bool
  log_allowed : Bool
  log_denied : Bool
  insults : Bool
  setenv : Bool
  runcwd : Option String
  apparmor_profile : Option String
  umask : Nat
  umask_override : Bool
  passwd_tries : Nat
  secure_path : Option String
  verifypw : Verifypw
  passwd_timeout : Nat
  timestamp_timeout : Nat
  timestamp_type : TimestampType
  editor : String
  env_editor : Bool
  env_keep : StrSet
  env_check : StrSet
  env_delete : StrSet
  deriving DecidableEq, Repr

/-- `impl Default for Settings`: the initial values of the table. The lists hold the table's
strings in table order (Rust collects them into a `HashSet`; the set is the same). -/
def Settings.default : Settings where
  always_query_group_plugin := false
  always_set_home := false
  env_reset := true
  fqdn := false
  ignore_dot := true
  lecture := .never
  mailerpath := none
  mail_badpass := true
  match_group_by_gid := false
  use_pty := true
  visiblepw := false
  pwfeedback := true
  rootpw := false
  targetpw := false
  noexec := false
  noninteractive_auth := false
  log_allowed := true
  log_denied := true
  insults := false
  setenv := false
  runcwd := none
  apparmor_profile := none
  umask := 0o022
  umask_override := false
  passwd_tries := 3
  secure_path := none
  verifypw := .all
  passwd_timeout := 5 * 60
  timestamp_timeout := 15 * 60
  timestamp_type := .tty
  editor := systemEditor
  env_editor := true
  env_keep := ["COLORS", "DISPLAY", "HOSTNAME", "KRB5CCNAME", "LS_COLORS", "PATH", "PS1", "PS2",
    "XAUTHORITY", "XAUTHORIZATION", "XDG_CURRENT_DESKTOP"]
  env_check := ["COLORTERM", "LANG", "LANGUAGE", "LC_*", "LINGUAS", "TERM", "TZ"]
  env_delete := ["IFS", "CDPATH", "LOCALDOMAIN", "RES_OPTIONS", "HOSTALIASES", "NLSPATH",
    "PATH_LOCALE", "LD_*", "_RLD*", "TERMINFO", "TERMINFO_DIRS", "TERMPATH", "TERMCAP", "ENV",
    "BASH_ENV", "PS4", "GLOBIGNORE", "BASHOPTS", "SHELLOPTS", "JAVA_TOOL_OPTIONS", "PERLIO_DEBUG",
    "PERLLIB", "PERL5LIB", "PERL5OPT", "PERL5DB", "FPATH", "NULLCMD", "READNULLCMD", "ZDOTDIR",
    "TMPPREFIX", "PYTHONHOME", "PYTHONPATH", "PYTHONINSPECT", "PYTHONUSERBASE", "RUBYLIB",
    "RUBYOPT", "*=()*"]

/-! ## Modifiers -/

/-- `defaults::SettingsModifier`: one entry of a `Defaults` line. For every setting the new
value; for a list the change (mode and items). -/
inductive SettingsModifier where
  | always_query_group_plugin (v : Bool)
  | always_set_home (v : Bool)
  | env_reset (v : Bool)
  | fqdn (v : Bool)
  | ignore_dot (v : Bool)
  | lecture (v : Lecture)
  | mailerpath (v : Option String)
  | mail_badpass (v : Bool)
  | match_group_by_gid (v : Bool)
  | use_pty (v : Bool)
  | visiblepw (v : Bool)
  | pwfeedback (v : Bool)
  | rootpw (v : Bool)
  | targetpw (v : Bool)
  | noexec (v : Bool)
  | noninteractive_auth (v : Bool)
  | log_allowed (v : Bool)
  | log_denied (v : Bool)
  | insults (v : Bool)
  | setenv (v : Bool)
  | runcwd (v : Option String)
  | apparmor_profile (v : Option String)
  | umask (v : Nat)
  | umask_override (v : Bool)
  | passwd_tries (v : Nat)
  | secure_path (v : Option String)
  | verifypw (v : Verifypw)
  | passwd_timeout (v : Nat)
  | timestamp_timeout (v : Nat)
  | timestamp_type (v : TimestampType)
  | editor (v : String)
  | env_editor (v : Bool)
  | env_keep (v : ListMode × List String)
  | env_check (v : ListMode × List String)
  | env_delete (v : ListMode × List String)
  deriving DecidableEq, Repr

/-- `apply_list`: `Set` builds a new set from the items, `Add` inserts them, `Del` removes them,
each in item order. -/
def applyList (s : StrSet) : ListMode × List String → StrSet
  | (.Set, items) => items.foldl StrSet.insert []
  | (.Add, items) => items.foldl StrSet.insert s
  | (.Del, items) => items.foldl StrSet.remove s

/-- `SettingsModifier::apply`: write the field of the variant. -/
def SettingsModifier.apply : SettingsModifier → Settings → Settings
  | .always_query_group_plugin v, s => { s with always_query_group_plugin := v }
  | .always_set_home v, s => { s with always_set_home := v }
  | .env_reset v, s => { s with env_reset := v }
  | .fqdn v, s => { s with fqdn := v }
  | .ignore_dot v, s => { s with ignore_dot := v }
  | .lecture v, s => { s with lecture := v }
  | .mailerpath v, s => { s with mailerpath := v }
  | .mail_badpass v, s => { s with mail_badpass := v }
  | .match_group_by_gid v, s => { s with match_group_by_gid := v }
  | .use_pty v, s => { s with use_pty := v }
  | .visiblepw v, s => { s with visiblepw := v }
  | .pwfeedback v, s => { s with pwfeedback := v }
  | .rootpw v, s => { s with rootpw := v }
  | .targetpw v, s => { s with targetpw := v }
  | .noexec v, s => { s with noexec := v }
  | .noninteractive_auth v, s => { s with noninteractive_auth := v }
  | .log_allowed v, s => { s with log_allowed := v }
  | .log_denied v, s => { s with log_denied := v }
  | .insults v, s => { s with insults := v }
  | .setenv v, s => { s with setenv := v }
  | .runcwd v, s => { s with runcwd := v }
  | .apparmor_profile v, s => { s with apparmor_profile := v }
  | .umask v, s => { s with umask := v }
  | .umask_override v, s => { s with umask_override := v }
  | .passwd_tries v, s => { s with passwd_tries := v }
  | .secure_path v, s => { s with secure_path := v }
  | .verifypw v, s => { s with verifypw := v }
  | .passwd_timeout v, s => { s with passwd_timeout := v }
  | .timestamp_timeout v, s => { s with timestamp_timeout := v }
  | .timestamp_type v, s => { s with timestamp_type := v }
  | .editor v, s => { s with editor := v }
  | .env_editor v, s => { s with env_editor := v }
  | .env_keep v, s => { s with env_keep := applyList s.env_keep v }
  | .env_check v, s => { s with env_check := applyList s.env_check v }
  | .env_delete v, s => { s with env_delete := applyList s.env_delete v }

/-- The setting a modifier changes. -/
def SettingsModifier.setting : SettingsModifier → Setting
  | .always_query_group_plugin _ => .always_query_group_plugin
  | .always_set_home _ => .always_set_home
  | .env_reset _ => .env_reset
  | .fqdn _ => .fqdn
  | .ignore_dot _ => .ignore_dot
  | .lecture _ => .lecture
  | .mailerpath _ => .mailerpath
  | .mail_badpass _ => .mail_badpass
  | .match_group_by_gid _ => .match_group_by_gid
  | .use_pty _ => .use_pty
  | .visiblepw _ => .visiblepw
  | .pwfeedback _ => .pwfeedback
  | .rootpw _ => .rootpw
  | .targetpw _ => .targetpw
  | .noexec _ => .noexec
  | .noninteractive_auth _ => .noninteractive_auth
  | .log_allowed _ => .log_allowed
  | .log_denied _ => .log_denied
  | .insults _ => .insults
  | .setenv _ => .setenv
  | .runcwd _ => .runcwd
  | .apparmor_profile _ => .apparmor_profile
  | .umask _ => .umask
  | .umask_override _ => .umask_override
  | .passwd_tries _ => .passwd_tries
  | .secure_path _ => .secure_path
  | .verifypw _ => .verifypw
  | .passwd_timeout _ => .passwd_timeout
  | .timestamp_timeout _ => .timestamp_timeout
  | .timestamp_type _ => .timestamp_type
  | .editor _ => .editor
  | .env_editor _ => .env_editor
  | .env_keep _ => .env_keep
  | .env_check _ => .env_check
  | .env_delete _ => .env_delete

/-- `defaults::SettingKind`: how a setting takes its value. -/
inductive SettingKind where
  | Flag (m : SettingsModifier)
  | Integer (s : IntegerSetting)
  | Text (s : TextSetting)
  | List (s : ListSetting)
  deriving DecidableEq, Repr

/-! ## The name table -/

/-- The name of a setting (`stringify!` of the table entry, also the `Settings` field). -/
def Setting.name : Setting → String
  | .always_query_group_plugin => "always_query_group_plugin"
  | .always_set_home => "always_set_home"
  | .env_reset => "env_reset"
  | .fqdn => "fqdn"
  | .ignore_dot => "ignore_dot"
  | .lecture => "lecture"
  | .mailerpath => "mailerpath"
  | .mail_badpass => "mail_badpass"
  | .match_group_by_gid => "match_group_by_gid"
  | .use_pty => "use_pty"
  | .visiblepw => "visiblepw"
  | .pwfeedback => "pwfeedback"
  | .rootpw => "rootpw"
  | .targetpw => "targetpw"
  | .noexec => "noexec"
  | .noninteractive_auth => "noninteractive_auth"
  | .log_allowed => "log_allowed"
  | .log_denied => "log_denied"
  | .insults => "insults"
  | .setenv => "setenv"
  | .runcwd => "runcwd"
  | .apparmor_profile => "apparmor_profile"
  | .umask => "umask"
  | .umask_override => "umask_override"
  | .passwd_tries => "passwd_tries"
  | .secure_path => "secure_path"
  | .verifypw => "verifypw"
  | .passwd_timeout => "passwd_timeout"
  | .timestamp_timeout => "timestamp_timeout"
  | .timestamp_type => "timestamp_type"
  | .editor => "editor"
  | .env_editor => "env_editor"
  | .env_keep => "env_keep"
  | .env_check => "env_check"
  | .env_delete => "env_delete"

/-- Every setting in table order. -/
def Setting.all : List Setting :=
  [.always_query_group_plugin, .always_set_home, .env_reset, .fqdn, .ignore_dot, .lecture,
    .mailerpath, .mail_badpass, .match_group_by_gid, .use_pty, .visiblepw, .pwfeedback, .rootpw,
    .targetpw, .noexec, .noninteractive_auth, .log_allowed, .log_denied, .insults, .setenv,
    .runcwd, .apparmor_profile, .umask, .umask_override, .passwd_tries, .secure_path, .verifypw,
    .passwd_timeout, .timestamp_timeout, .timestamp_type, .editor, .env_editor, .env_keep,
    .env_check, .env_delete]

/-- `setting_at`: the setting at position `index` of the table, with its name. -/
def settingAt (index : Nat) : Option (String × Setting) :=
  Setting.all[index]?.map fun s => (s.name, s)

/-- `setting_named`: the first setting of the table whose name is `name`. -/
def settingNamed (name : String) : Option Setting :=
  Setting.all.find? fun s => s.name == name

/-! ## Negation and kinds -/

/-- The arm of `negate` for a setting: the explicit negation `(!= v)` of the table, else `false`
for a flag and the empty set for a list (`(Set, [])`), else none. -/
def Setting.negation : Setting → Option SettingsModifier
  | .always_query_group_plugin => some (.always_query_group_plugin false)
  | .always_set_home => some (.always_set_home false)
  | .env_reset => some (.env_reset false)
  | .fqdn => some (.fqdn false)
  | .ignore_dot => some (.ignore_dot false)
  | .lecture => some (.lecture .never)
  | .mailerpath => some (.mailerpath none)
  | .mail_badpass => some (.mail_badpass false)
  | .match_group_by_gid => some (.match_group_by_gid false)
  | .use_pty => some (.use_pty false)
  | .visiblepw => some (.visiblepw false)
  | .pwfeedback => some (.pwfeedback false)
  | .rootpw => some (.rootpw false)
  | .targetpw => some (.targetpw false)
  | .noexec => some (.noexec false)
  | .noninteractive_auth => some (.noninteractive_auth false)
  | .log_allowed => some (.log_allowed false)
  | .log_denied => some (.log_denied false)
  | .insults => some (.insults false)
  | .setenv => some (.setenv false)
  | .runcwd => some (.runcwd none)
  | .apparmor_profile => some (.apparmor_profile none)
  | .umask => some (.umask 0o777)
  | .umask_override => some (.umask_override false)
  | .passwd_tries => none
  | .secure_path => some (.secure_path none)
  | .verifypw => some (.verifypw .never)
  | .passwd_timeout => some (.passwd_timeout 0)
  | .timestamp_timeout => some (.timestamp_timeout 0)
  | .timestamp_type => none
  | .editor => none
  | .env_editor => some (.env_editor false)
  | .env_keep => some (.env_keep (.Set, []))
  | .env_check => some (.env_check (.Set, []))
  | .env_delete => some (.env_delete (.Set, []))

/-- The arm of `set` for a setting: a flag carries the modifier that sets it. -/
def Setting.kind : Setting → SettingKind
  | .always_query_group_plugin => .Flag (.always_query_group_plugin true)
  | .always_set_home => .Flag (.always_set_home true)
  | .env_reset => .Flag (.env_reset true)
  | .fqdn => .Flag (.fqdn true)
  | .ignore_dot => .Flag (.ignore_dot true)
  | .lecture => .Text .lecture
  | .mailerpath => .Text .mailerpath
  | .mail_badpass => .Flag (.mail_badpass true)
  | .match_group_by_gid => .Flag (.match_group_by_gid true)
  | .use_pty => .Flag (.use_pty true)
  | .visiblepw => .Flag (.visiblepw true)
  | .pwfeedback => .Flag (.pwfeedback true)
  | .rootpw => .Flag (.rootpw true)
  | .targetpw => .Flag (.targetpw true)
  | .noexec => .Flag (.noexec true)
  | .noninteractive_auth => .Flag (.noninteractive_auth true)
  | .log_allowed => .Flag (.log_allowed true)
  | .log_denied => .Flag (.log_denied true)
  | .insults => .Flag (.insults true)
  | .setenv => .Flag (.setenv true)
  | .runcwd => .Text .runcwd
  | .apparmor_profile => .Text .apparmor_profile
  | .umask => .Integer .umask
  | .umask_override => .Flag (.umask_override true)
  | .passwd_tries => .Integer .passwd_tries
  | .secure_path => .Text .secure_path
  | .verifypw => .Text .verifypw
  | .passwd_timeout => .Integer .passwd_timeout
  | .timestamp_timeout => .Integer .timestamp_timeout
  | .timestamp_type => .Text .timestamp_type
  | .editor => .Text .editor
  | .env_editor => .Flag (.env_editor true)
  | .env_keep => .List .env_keep
  | .env_check => .List .env_check
  | .env_delete => .List .env_delete

/-- `negate`: the modifier of `!name`, if the setting exists and can be negated. -/
def negate (name : String) : Option SettingsModifier :=
  (settingNamed name).bind Setting.negation

/-- `set`: the kind of the setting called `name`. -/
def set (name : String) : Option SettingKind :=
  (settingNamed name).map Setting.kind

/-! ## Checkers -/

/-- `check_integer`: `passwd_tries` is a decimal `u64` in `0..=1000`; `umask` is `octal_mode`;
the timeouts are `fractional_minutes` (the panic-free value; `checkIntegerRun` has the panics). -/
def checkInteger : IntegerSetting → String → Option SettingsModifier
  | .umask, t => (octalMode t).map .umask
  | .passwd_tries, t => (integerInRange t 10 0 1000).map .passwd_tries
  | .passwd_timeout, t => (fractionalMinutes t).map .passwd_timeout
  | .timestamp_timeout, t => (fractionalMinutes t).map .timestamp_timeout

/-- `check_integer` with the panics of `fractional_minutes`. -/
def checkIntegerRun : IntegerSetting → String → Outcome (Option SettingsModifier)
  | .passwd_timeout, t =>
    match fractionalMinutesRun t with
    | .ok r => .ok (r.map .passwd_timeout)
    | .panic => .panic
  | .timestamp_timeout, t =>
    match fractionalMinutesRun t with
    | .ok r => .ok (r.map .timestamp_timeout)
    | .panic => .panic
  | id, t => .ok (checkInteger id t)

/-- `check_text`: a keyword setting accepts exactly its keys (case-sensitive); a text setting
takes any text. -/
def checkText : TextSetting → String → Option SettingsModifier
  | .lecture, t =>
    match t with
    | "always" => some (.lecture .always)
    | "once" => some (.lecture .once)
    | "never" => some (.lecture .never)
    | _ => none
  | .mailerpath, t => some (.mailerpath (some t))
  | .runcwd, t => some (.runcwd (some t))
  | .apparmor_profile, t => some (.apparmor_profile (some t))
  | .secure_path, t => some (.secure_path (some t))
  | .verifypw, t =>
    match t with
    | "all" => some (.verifypw .all)
    | "always" => some (.verifypw .always)
    | "any" => some (.verifypw .any)
    | "never" => some (.verifypw .never)
    | _ => none
  | .timestamp_type, t =>
    match t with
    | "tty" => some (.timestamp_type .tty)
    | "ppid" => some (.timestamp_type .ppid)
    | _ => none
  | .editor, t => some (.editor t)

/-- `build_list`. -/
def buildList : ListSetting → ListMode → List String → SettingsModifier
  | .env_keep, mode, items => .env_keep (mode, items)
  | .env_check, mode, items => .env_check (mode, items)
  | .env_delete, mode, items => .env_delete (mode, items)

/-! ## The link to `SudoersSpec.authorization` -/

/-- The Defaults values `Judgement::authorization` and `Settings::to_auth` read. -/
def Settings.toDefaults (s : Settings) : SudoersSpec.Defaults StrSet where
  usePty := s.use_pty
  pwfeedback := s.pwfeedback
  rootpw := s.rootpw
  targetpw := s.targetpw
  noexec := s.noexec
  noninteractiveAuth := s.noninteractive_auth
  logAllowed := s.log_allowed
  setenv := s.setenv
  runcwd := s.runcwd
  umask := s.umask
  umaskOverride := s.umask_override
  passwdTries := s.passwd_tries
  securePath := s.secure_path
  passwdTimeout := s.passwd_timeout
  timestampTimeout := s.timestamp_timeout
  timestampType := s.timestamp_type
  envKeep := s.env_keep
  envCheck := s.env_check

/-- The initial values of `SudoersSpec.Defaults` are those of the table. -/
theorem toDefaults_default :
    Settings.default.toDefaults =
      { envKeep := Settings.default.env_keep, envCheck := Settings.default.env_check } := rfl

end SudoersSpec.Settings
