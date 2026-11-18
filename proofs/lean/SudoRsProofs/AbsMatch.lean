import SudoRsProofs.Abs

/-!
# Abstractions and hypotheses for the matchers

The matchers of `src/sudoers/mod.rs` (`match_user`, `match_group`, `match_group_alias`,
`match_token`, `match_command`, `in_group`, `match_identifier`) only call:
* the methods of the `UnixUser` / `UnixGroup` traits and `PartialEq` on users, which reach the
  operating system (generic instances in the extracted code);
* the opaque glob matcher `glob.Pattern.matches_path_with`.

The specification abstracts both by an `SudoersSpec.Oracle`. This file
* abstracts the extracted syntax (`Identifier`, `UserSpecifier`, commands, `RunAs`, hostnames)
  to the specification types;
* states, as two bundled hypotheses, what it means for the Rust instances to be pure and total
  and to agree with an oracle: `InstOracle` (users and groups) and `GlobOracle` (glob matching,
  through an abstraction `GlobAbs` of the opaque `Pattern`, `Path`, `OsString`).

The oracle is stated directly over the Rust user and group types (the abstraction of users and
groups is the identity). This loses no generality: any oracle on abstract users composed with an
abstraction function is an oracle on the Rust types.
-/

open Aeneas Aeneas.Std Result

namespace SudoRsProofs

/-! ## Syntax -/

/-- `ast.rs` `Identifier`: a name (`SudoString`, modelled by its text) or a `#id` (`u32`). -/
def absIdentifier : sudo_rs.sudoers.ast.Identifier → SudoersSpec.Identifier
  | .Name s => .name s.str
  | .ID n => .id n.val

/-- `ast.rs` `UserSpecifier`. -/
def absUserSpecifier : sudo_rs.sudoers.ast.UserSpecifier → SudoersSpec.UserSpecifier
  | .User i => .user (absIdentifier i)
  | .Group i => .group (absIdentifier i)
  | .NonunixGroup i => .nonunixGroup (absIdentifier i)

/-- `ast.rs` `RunAs`: the user list and the group list. -/
def absRunAs (r : sudo_rs.sudoers.ast.RunAs) : SudoersSpec.RunAs :=
  ⟨absSpecList absUserSpecifier r.users.val, absSpecList absIdentifier r.groups.val⟩

/-- `system::Hostname` (the current host): its text. -/
def absSysHostname (h : sudo_rs.system.Hostname) : SudoersSpec.Hostname := h.inner

/-- How the opaque types of command matching are read as text. `glob.Pattern`,
`std.path.Path` and `std.ffi.os_str.OsString` are opaque in the model; the spec takes the
command pattern, the command path and the arguments as strings. -/
structure GlobAbs where
  /-- The source text of a compiled glob pattern. -/
  pat : glob.Pattern → String
  /-- The command path. -/
  path : std.path.Path → String
  /-- A command argument. -/
  os : std.ffi.os_str.OsString → String

/-- `tokens.rs` `Args`. -/
def absArgs (A : GlobAbs) : sudo_rs.sudoers.tokens.Args → SudoersSpec.Args
  | .Prefix v => .prefix (v.val.map A.os)
  | .Exact v => .exact (v.val.map A.os)

/-- `tokens.rs` `Command = (SimpleCommand, Args)`, with `SimpleCommand = glob::Pattern`. -/
def absCommand (A : GlobAbs) (c : glob.Pattern × sudo_rs.sudoers.tokens.Args) :
    SudoersSpec.Command :=
  ⟨A.pat c.1, absArgs A c.2⟩

/-- The request of `check_permission(.., am_user, on_host, request)` as a spec request. -/
def absRequest {U G UG : Type} (A : GlobAbs) (amUser : U) (onHost : sudo_rs.system.Hostname)
    (req : sudo_rs.sudoers.Request U G UG) : SudoersSpec.Request U G where
  invokingUser := amUser
  host := absSysHostname onHost
  targetUser := req.user
  targetGroup := req.group
  command := A.path req.command
  arguments := req.arguments.val.map A.os

/-! ## Side conditions: names that fit in memory

The closures dereference the `SudoString` of a name (`SudoString::deref`, modelled by
`strOfString`, which fails on strings longer than `usize::MAX` bytes; no Rust string is). The
matcher theorems therefore hold for the items whose names fit. -/

/-- The name of an identifier fits in memory. -/
def IdentFits : sudo_rs.sudoers.ast.Identifier → Prop
  | .Name s => Fits s.str
  | .ID _ => True

/-- The names `match_user` / `match_group_alias` dereference fit in memory: the identifier of a
plain user specifier (`%group` names are passed as a `CStr`, never dereferenced). -/
def UserSpecFits : sudo_rs.sudoers.ast.UserSpecifier → Prop
  | .User i => IdentFits i
  | .Group _ => True
  | .NonunixGroup _ => True

/-! ## The oracle hypotheses -/

/-- The `MatchOptions` built by `match_command`: `MatchOptions { require_literal_separator:
true, ..MatchOptions::new() }` (glob 0.3.4 defaults otherwise). -/
def matchCommandOptions : sudo_rs.glob.MatchOptions :=
  { case_sensitive := true, require_literal_separator := true,
    require_literal_leading_dot := false }

/-- **The user/group instances are pure, total, and agree with the oracle `O`.**
`uInst` is the `UnixUser` instance of the user type `U`, `eqInst` its `PartialEq`, `gInst` the
`UnixGroup` instance of the group type `G`. Every method the decision calls returns `ok` with
the oracle's answer; text arguments are linked through their UTF-8 bytes, numeric ids through
their value. -/
structure InstOracle {U G UG : Type} (uInst : sudo_rs.system.interface.UnixUser U UG)
    (eqInst : core.cmp.PartialEq U U) (gInst : sudo_rs.system.interface.UnixGroup G)
    (O : SudoersSpec.Oracle U G) : Prop where
  /-- `UnixUser::has_name(&self, name: &str)`. -/
  has_name : ∀ (u : U) (s : Str) (n : String), s.val = sudo_rs.stringBytes n →
    uInst.has_name u s = ok (O.hasName u n)
  /-- `UnixUser::has_uid(&self, uid: UserId)`. -/
  has_uid : ∀ (u : U) (n : U32), uInst.has_uid u n = ok (O.hasUid u n.val)
  /-- `UnixUser::is_root(&self)`. -/
  is_root : ∀ u : U, uInst.is_root u = ok (O.isRoot u)
  /-- `UnixUser::in_group_by_name(&self, name: &CStr)`. -/
  in_group_by_name : ∀ (u : U) (c : core.ffi.c_str.CStr),
    uInst.in_group_by_name u c = ok (O.inGroupByName u c.str)
  /-- `UnixUser::in_group_by_gid(&self, gid: GroupId)`. -/
  in_group_by_gid : ∀ (u : U) (n : U32), uInst.in_group_by_gid u n = ok (O.inGroupByGid u n.val)
  /-- `PartialEq::eq` on users. -/
  eq : ∀ u v : U, eqInst.eq u v = ok (O.userEq u v)
  /-- `PartialEq::ne` on users. -/
  ne : ∀ u v : U, eqInst.ne u v = ok (!O.userEq u v)
  /-- `UnixGroup::as_gid(&self)`. -/
  as_gid : ∀ g : G, gInst.as_gid g ⦃ x => x.val = O.asGid g ⦄
  /-- `UnixGroup::try_as_name(&self) -> Option<&str>`. -/
  try_as_name : ∀ g : G,
    gInst.try_as_name g ⦃ o => o.map Slice.val = (O.tryAsName g).map sudo_rs.stringBytes ⦄

/-- **The glob matcher agrees with the oracle `O`**, read through the abstraction `A`, with the
options `match_command` uses; and distinct `OsString`s have distinct abstractions (the spec
compares arguments as strings, the Rust compares `OsString`s). -/
structure GlobOracle {U G : Type} (A : GlobAbs) (O : SudoersSpec.Oracle U G) : Prop where
  glob_matches : ∀ (pat : glob.Pattern) (path : std.path.Path),
    glob.Pattern.matches_path_with pat path matchCommandOptions =
      ok (O.globMatches (A.pat pat) (A.path path))
  os_inj : Function.Injective A.os

end SudoRsProofs
