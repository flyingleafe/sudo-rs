import SudoersSpec.Ast

/-!
# The abstract environment and the request

The decision never inspects the operating system directly: it only calls the methods of
the `UnixUser`/`UnixGroup` traits (`src/system/interface.rs`), `PartialEq` on users, and the
glob matcher of `match_command`. The spec takes all of them as an `Oracle` of decidable
(`Bool`-valued) predicates, so no OS or glob model is needed. The derived matchers below
(`matchUser`, `matchGroup`, ...) are transcriptions of the closures in `src/sudoers/mod.rs`.
-/

namespace SudoersSpec

/-- Decidable predicates the decision is parameterised by. -/
structure Oracle (User Group : Type) where
  /-- `UnixUser::has_name`. -/
  hasName : User → String → Bool
  /-- `UnixUser::has_uid`. -/
  hasUid : User → Nat → Bool
  /-- `UnixUser::is_root`. -/
  isRoot : User → Bool
  /-- `UnixUser::in_group_by_name`. -/
  inGroupByName : User → String → Bool
  /-- `UnixUser::in_group_by_gid`. -/
  inGroupByGid : User → Nat → Bool
  /-- `PartialEq for User` (used as `request.user != am_user` and `request.user == am_user`). -/
  userEq : User → User → Bool
  /-- `UnixGroup::as_gid`. -/
  asGid : Group → Nat
  /-- `UnixGroup::try_as_name`. -/
  tryAsName : Group → Option String
  /-- `glob::Pattern::matches_path_with` with `require_literal_separator`: does the command
  path match the (glob) pattern? -/
  globMatches : (pattern : String) → (path : String) → Bool
  /-- Does a host name in the policy match the current host name? sudo-rs (`match_token`)
  uses plain string equality, see `Oracle.SudoRsHosts`. -/
  hostMatches : (pattern : Hostname) → (host : Hostname) → Bool

/-- The host matcher that sudo-rs actually uses (`mod.rs` `match_token`). -/
def Oracle.SudoRsHosts (O : Oracle User Group) : Prop :=
  ∀ p h, O.hostMatches p h = (p == h)

/-- What the user asks for: `Sudoers::check(am_user, on_host, Request { user, group, command,
arguments })` with the invoking user and the host folded in. -/
structure Request (User Group : Type) where
  /-- `am_user`: the invoking user. -/
  invokingUser : User
  /-- `on_host`: the current host name. -/
  host : Hostname
  /-- `request.user`: the target (runas) user. -/
  targetUser : User
  /-- `request.group`: the target (runas) group. -/
  targetGroup : Group
  /-- `request.command`, already resolved to a path. -/
  command : String
  /-- `request.arguments`. -/
  arguments : List String

variable {User Group : Type} (O : Oracle User Group)

/-- `mod.rs` `match_identifier`. -/
def matchIdentifier (u : User) : Identifier → Bool
  | .name n => O.hasName u n
  | .id n => O.hasUid u n

/-- `mod.rs` `match_user`: does `u` match a user specifier? Non-unix groups never match. -/
def matchUser (u : User) : UserSpecifier → Bool
  | .user i => matchIdentifier O u i
  | .group (.name n) => O.inGroupByName u n
  | .group (.id n) => O.inGroupByGid u n
  | .nonunixGroup _ => false

/-- `mod.rs` `in_group`. -/
def inGroup (u : User) (g : Group) : Bool :=
  O.inGroupByGid u (O.asGid g)

/-- `mod.rs` `match_group`: does group `g` match an identifier of a runas group list? -/
def matchGroup (g : Group) : Identifier → Bool
  | .id n => O.asGid g == n
  | .name n => O.tryAsName g == some n

/-- `mod.rs` `match_group_alias`: matching a group against a `Runas_Alias` member. Only plain
identifiers are compared (as groups); `%group` members never match. -/
def matchGroupAlias (g : Group) : UserSpecifier → Bool
  | .user i => matchGroup O g i
  | _ => false

/-- `mod.rs` `match_token` generalised to `Oracle.hostMatches`. -/
def matchHost (host : Hostname) (pattern : Hostname) : Bool :=
  O.hostMatches pattern host

/-- Argument part of `mod.rs` `match_command`. -/
def argsMatch (args : List String) : Args → Bool
  | .prefix v => v.isPrefixOf args
  | .exact v => args == v

/-- `mod.rs` `match_command`. -/
def matchCommand (path : String) (args : List String) (c : Command) : Bool :=
  O.globMatches c.pattern path && argsMatch args c.args

end SudoersSpec
