import SudoRsProofs.Authorization
import SudoersSpec.Settings.Properties

/-!
# Abstraction of the extracted `defaults` data to `SudoersSpec.Settings`

`Box<str>` values are read as text with `stringOfStr` (as in `absDefaults`), `u64` values by
`.val`, and the extracted `HashSet<String>` (a list of keys) is taken as it is. The `Setting`
and kind enumerations correspond constructor for constructor.

String lemmas: the bytes of a `toStr` literal and of a `String` (`toStr_val`), and reading back
the text of a `&str` that holds the bytes of a `String` (`stringOfStr_of_val`).
-/

open Aeneas Aeneas.Std Result

namespace SudoRsProofs.Defaults

open SudoersSpec.Settings (StrSet)

/-! ## Strings -/

theorem byteArray_toList_eq (bs : ByteArray) : bs.toList = bs.data.toList := by
  have key : ∀ (i : Nat) (r : List UInt8), i ≤ bs.size →
      ByteArray.toList.loop bs i r = r.reverse ++ bs.data.toList.drop i := by
    intro i r hi
    fun_induction ByteArray.toList.loop bs i r with
    | case1 i r h ih =>
      rw [ih (by omega)]
      have hlt : i < bs.data.toList.length := by rw [Array.length_toList]; exact h
      rw [List.drop_eq_getElem_cons hlt]
      simp only [ByteArray.get!, List.reverse_cons, List.append_assoc, List.singleton_append,
        Array.getElem_toList]
      rw [getElem!_pos bs.data i (by simpa using hlt)]
    | case2 i r h =>
      have : bs.data.toList.length ≤ i := by rw [Array.length_toList]; exact Nat.le_of_not_lt h
      simp [List.drop_eq_nil_of_le this]
  unfold ByteArray.toList
  simpa using key 0 [] (Nat.zero_le _)

/-- The bytes of a string literal of the extracted code are its UTF-8 bytes. -/
theorem toStr_val (s : String) (h) : (toStr s h).val = sudo_rs.stringBytes s := by
  simp only [toStr, Slice.from_val, sudo_rs.stringBytes, byteArray_toList_eq]
  apply List.map_congr_left
  intro x _
  rfl

/-- Reading back a `&str` that holds the bytes of a text gives the text. -/
theorem stringOfStr_of_val {t : Str} {n : String} (h : t.val = sudo_rs.stringBytes n) :
    sudo_rs.stringOfStr t = n := by
  unfold sudo_rs.stringOfStr
  rw [h]
  have : (sudo_rs.stringBytes n).map (fun u => UInt8.ofNat u.val) = n.toByteArray.data.toList := by
    simp only [sudo_rs.stringBytes, List.map_map]
    conv => rhs; rw [← List.map_id n.toByteArray.data.toList]
    apply List.map_congr_left
    intro b _
    exact UInt8.ofNat_toNat
  rw [this]
  simp only [Array.toArray_toList]
  exact String.fromUTF8Lossy_toByteArray

/-- Equality of a `&str` holding the bytes of `n` with a literal. -/
theorem str_eq_toStr_iff {t : Str} {n : String} (h : t.val = sudo_rs.stringBytes n) (lit : String)
    (hl) : t = toStr lit hl ↔ n = lit := by
  constructor
  · intro e
    have := congrArg Slice.val e
    rw [h, toStr_val] at this
    exact stringBytes_inj.mp this
  · rintro rfl
    apply Slice.ext
    rw [h, toStr_val]

/-! ## Enumerations -/

def absLecture : sudo_rs.defaults.enums.lecture → SudoersSpec.Settings.Lecture
  | .always => .always | .once => .once | .never => .never

def absVerifypw : sudo_rs.defaults.enums.verifypw → SudoersSpec.Settings.Verifypw
  | .all => .all | .always => .always | .any => .any | .never => .never

def absListMode : sudo_rs.defaults.ListMode → SudoersSpec.Settings.ListMode
  | .Set => .Set | .Add => .Add | .Del => .Del

def absIntegerSetting : sudo_rs.defaults.IntegerSetting → SudoersSpec.Settings.IntegerSetting
  | .umask => .umask | .passwd_tries => .passwd_tries | .passwd_timeout => .passwd_timeout
  | .timestamp_timeout => .timestamp_timeout

def absTextSetting : sudo_rs.defaults.TextSetting → SudoersSpec.Settings.TextSetting
  | .lecture => .lecture | .mailerpath => .mailerpath | .runcwd => .runcwd
  | .apparmor_profile => .apparmor_profile | .secure_path => .secure_path
  | .verifypw => .verifypw | .timestamp_type => .timestamp_type | .editor => .editor

def absListSetting : sudo_rs.defaults.ListSetting → SudoersSpec.Settings.ListSetting
  | .env_keep => .env_keep | .env_check => .env_check | .env_delete => .env_delete

/-- The extracted `Setting` of a spec `Setting`. -/
def concSetting : SudoersSpec.Settings.Setting → sudo_rs.defaults.Setting
  | .always_query_group_plugin => .always_query_group_plugin
  | .always_set_home => .always_set_home
  | .env_reset => .env_reset
  | .fqdn => .fqdn
  | .ignore_dot => .ignore_dot
  | .lecture => .lecture
  | .mailerpath => .mailerpath
  | .mail_badpass => .mail_badpass
  | .match_group_by_gid => .match_group_by_gid
  | .use_pty => .use_pty
  | .visiblepw => .visiblepw
  | .pwfeedback => .pwfeedback
  | .rootpw => .rootpw
  | .targetpw => .targetpw
  | .noexec => .noexec
  | .noninteractive_auth => .noninteractive_auth
  | .log_allowed => .log_allowed
  | .log_denied => .log_denied
  | .insults => .insults
  | .setenv => .setenv
  | .runcwd => .runcwd
  | .apparmor_profile => .apparmor_profile
  | .umask => .umask
  | .umask_override => .umask_override
  | .passwd_tries => .passwd_tries
  | .secure_path => .secure_path
  | .verifypw => .verifypw
  | .passwd_timeout => .passwd_timeout
  | .timestamp_timeout => .timestamp_timeout
  | .timestamp_type => .timestamp_type
  | .editor => .editor
  | .env_editor => .env_editor
  | .env_keep => .env_keep
  | .env_check => .env_check
  | .env_delete => .env_delete

/-! ## Settings and modifiers -/

/-- The extracted `Settings` as a spec value. -/
def absSettings (s : sudo_rs.defaults.Settings) : SudoersSpec.Settings.Settings where
  always_query_group_plugin := s.always_query_group_plugin
  always_set_home := s.always_set_home
  env_reset := s.env_reset
  fqdn := s.fqdn
  ignore_dot := s.ignore_dot
  lecture := absLecture s.lecture
  mailerpath := s.mailerpath.map sudo_rs.stringOfStr
  mail_badpass := s.mail_badpass
  match_group_by_gid := s.match_group_by_gid
  use_pty := s.use_pty
  visiblepw := s.visiblepw
  pwfeedback := s.pwfeedback
  rootpw := s.rootpw
  targetpw := s.targetpw
  noexec := s.noexec
  noninteractive_auth := s.noninteractive_auth
  log_allowed := s.log_allowed
  log_denied := s.log_denied
  insults := s.insults
  setenv := s.setenv
  runcwd := s.runcwd.map sudo_rs.stringOfStr
  apparmor_profile := s.apparmor_profile.map sudo_rs.stringOfStr
  umask := s.umask.val
  umask_override := s.umask_override
  passwd_tries := s.passwd_tries.val
  secure_path := s.secure_path.map sudo_rs.stringOfStr
  verifypw := absVerifypw s.verifypw
  passwd_timeout := s.passwd_timeout.val
  timestamp_timeout := s.timestamp_timeout.val
  timestamp_type := absTimestampType s.timestamp_type
  editor := sudo_rs.stringOfStr s.editor
  env_editor := s.env_editor
  env_keep := s.env_keep
  env_check := s.env_check
  env_delete := s.env_delete

/-- **`absDefaults` factors through the settings model.** -/
theorem absDefaults_eq (s : sudo_rs.defaults.Settings) :
    absDefaults s = (absSettings s).toDefaults := rfl

def absChange (v : sudo_rs.defaults.ListMode × alloc.vec.Vec String) :
    SudoersSpec.Settings.ListMode × List String :=
  (absListMode v.1, v.2.val)

/-- The extracted modifier as a spec modifier. -/
def absModifier : sudo_rs.defaults.SettingsModifier → SudoersSpec.Settings.SettingsModifier
  | .always_query_group_plugin v => .always_query_group_plugin v
  | .always_set_home v => .always_set_home v
  | .env_reset v => .env_reset v
  | .fqdn v => .fqdn v
  | .ignore_dot v => .ignore_dot v
  | .lecture v => .lecture (absLecture v)
  | .mailerpath v => .mailerpath (v.map sudo_rs.stringOfStr)
  | .mail_badpass v => .mail_badpass v
  | .match_group_by_gid v => .match_group_by_gid v
  | .use_pty v => .use_pty v
  | .visiblepw v => .visiblepw v
  | .pwfeedback v => .pwfeedback v
  | .rootpw v => .rootpw v
  | .targetpw v => .targetpw v
  | .noexec v => .noexec v
  | .noninteractive_auth v => .noninteractive_auth v
  | .log_allowed v => .log_allowed v
  | .log_denied v => .log_denied v
  | .insults v => .insults v
  | .setenv v => .setenv v
  | .runcwd v => .runcwd (v.map sudo_rs.stringOfStr)
  | .apparmor_profile v => .apparmor_profile (v.map sudo_rs.stringOfStr)
  | .umask v => .umask v.val
  | .umask_override v => .umask_override v
  | .passwd_tries v => .passwd_tries v.val
  | .secure_path v => .secure_path (v.map sudo_rs.stringOfStr)
  | .verifypw v => .verifypw (absVerifypw v)
  | .passwd_timeout v => .passwd_timeout v.val
  | .timestamp_timeout v => .timestamp_timeout v.val
  | .timestamp_type v => .timestamp_type (absTimestampType v)
  | .editor v => .editor (sudo_rs.stringOfStr v)
  | .env_editor v => .env_editor v
  | .env_keep v => .env_keep (absChange v)
  | .env_check v => .env_check (absChange v)
  | .env_delete v => .env_delete (absChange v)

def absKind : sudo_rs.defaults.SettingKind → SudoersSpec.Settings.SettingKind
  | .Flag m => .Flag (absModifier m)
  | .Integer s => .Integer (absIntegerSetting s)
  | .Text s => .Text (absTextSetting s)
  | .List s => .List (absListSetting s)

end SudoRsProofs.Defaults
