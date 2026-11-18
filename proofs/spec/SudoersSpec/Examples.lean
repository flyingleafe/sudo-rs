import SudoersSpec.Theorems

/-!
# Executable examples

Concrete policies evaluated against the oracle of the Rust unit tests
(`src/sudoers/test/mod.rs`, `struct Named` and `dummy_cksum`): users and groups are names,
the uid/gid of a name is `dummy_cksum(name)`, every user is exactly in its own group, root is
the user called `root`. Each `#guard` mirrors one `pass!`/`FAIL!` of `permission_test`
(test file line numbers in the comments); the policies are the parsed form of the sudoers
lines quoted there. The glob matcher is a small model of `glob::Pattern` with
`require_literal_separator` (`*`, `?`, literal characters) that suffices for these patterns.
-/

namespace SudoersSpec.Examples

open SudoersSpec

/-- `dummy_cksum` from the Rust tests. -/
def cksum (name : String) : Nat :=
  if name = "root" then 0 else 1000 + name.foldl (fun x c => (x * 97 + c.toNat) % 1361) 0

/-- A model of `glob::Pattern::matches_path_with(require_literal_separator)` for `*`, `?`
and literal characters. -/
def globChars (p s : List Char) : Bool :=
  match p, s with
  | [], s => s.isEmpty
  | '*' :: ps, s =>
    globChars ps s || (match s with
      | c :: cs => c != '/' && globChars ('*' :: ps) cs
      | [] => false)
  | '?' :: ps, c :: cs => c != '/' && globChars ps cs
  | q :: ps, c :: cs => q == c && globChars ps cs
  | _ :: _, [] => false
termination_by (s.length, p.length)

/-- The oracle of `impl UnixUser for Named` / `impl UnixGroup for Named`. -/
def named : Oracle String String where
  hasName u n := u == n
  hasUid u n := cksum u == n
  isRoot u := u == "root"
  inGroupByName u n := u == n
  inGroupByGid u n := cksum u == n
  userEq u v := u == v
  asGid g := cksum g
  tryAsName g := some g
  globMatches pat path := globChars pat.toList path.toList
  hostMatches pat host := pat == host

theorem named_sudoRsHosts : named.SudoRsHosts := fun _ _ => rfl

/-! ## Building blocks for policies -/

def all {α : Type} : Spec α := .allow .all
def notAll {α : Type} : Spec α := .forbid .all
def al {α : Type} (n : String) : Spec α := .allow (.alias n)
def notAl {α : Type} (n : String) : Spec α := .forbid (.alias n)
/-- `name` in a user list. -/
def u (n : String) : Spec UserSpecifier := .allow (.only (.user (.name n)))
def notU (n : String) : Spec UserSpecifier := .forbid (.only (.user (.name n)))
/-- `#uid` in a user list. -/
def uid (n : Nat) : Spec UserSpecifier := .allow (.only (.user (.id n)))
/-- `%group` / `%#gid` in a user list. -/
def grp (n : String) : Spec UserSpecifier := .allow (.only (.group (.name n)))
def gidU (n : Nat) : Spec UserSpecifier := .allow (.only (.group (.id n)))
/-- `name` / `#gid` in a runas group list. -/
def g (n : String) : Spec Identifier := .allow (.only (.name n))
def gid (n : Nat) : Spec Identifier := .allow (.only (.id n))
def h (n : String) : Spec Hostname := .allow (.only n)
/-- A command without arguments (any arguments allowed). -/
def c (path : String) : Spec Command := .allow (.only ⟨path, .prefix []⟩)
def notC (path : String) : Spec Command := .forbid (.only ⟨path, .prefix []⟩)
/-- A command with exact arguments (`""` is `cx path []`). -/
def cx (path : String) (args : List String) : Spec Command := .allow (.only ⟨path, .exact args⟩)
/-- A command with leading arguments followed by `*`. -/
def cp (path : String) (args : List String) : Spec Command := .allow (.only ⟨path, .prefix args⟩)

/-- `(ALL:ALL)`. -/
def allAll : RunAs := ⟨[all], [all]⟩

/-- A command entry with an optional runas spec and tag modifiers. -/
def ent (runas : Option RunAs) (mods : List Modifier) (cmd : Spec Command) :
    Option RunAs × CommandSpec := (runas, ⟨mods, cmd⟩)

/-- `users ALL = entries`. -/
def line (users : SpecList UserSpecifier) (entries : List (Option RunAs × CommandSpec)) :
    PermissionSpec := ⟨users, [([all], entries)]⟩

/-- `users hosts = entries`. -/
def lineH (users : SpecList UserSpecifier) (hosts : SpecList Hostname)
    (entries : List (Option RunAs × CommandSpec)) : PermissionSpec := ⟨users, [(hosts, entries)]⟩

/-- `Sudoers::check(..).flags` for `invoking => (target, group), host; cmdline`. -/
def check (p : Policy) (invoking target group host cmdline : String) : Option Tag :=
  let words := (cmdline.splitOn " ").filter (· ≠ "")
  authorize named p
    { invokingUser := invoking, host := host, targetUser := target, targetGroup := group,
      command := words.headD "", arguments := words.tail }

def pol (rules : List PermissionSpec) (aliases : AliasTable := {}) : Policy := ⟨rules, aliases⟩

def allows (t : Option Tag) : Bool := t.isSome
def auth (t : Option Tag) : Option Authenticate := t.map (·.authenticate)

/-! ## Sanity checks of the test oracle -/

#guard cksum "user" = 1466                                         -- line 243
#guard globChars "/bin/hel*".toList "/bin/hello".toList
#guard !globChars "/bin/*".toList "/bin/sub/x".toList

/-! ## `permission_test` -/

-- 180-181: user ALL=(ALL:ALL) ALL
#guard !allows (check (pol [line [u "user"] [ent allAll [] all]]) "nobody" "root" "root" "server" "/bin/hello")
#guard allows (check (pol [line [u "user"] [ent allAll [] all]]) "user" "root" "root" "server" "/bin/hello")
-- 182-183: user ALL=(ALL:ALL) /bin/foo
#guard auth (check (pol [line [u "user"] [ent allAll [] (c "/bin/foo")]]) "user" "root" "root" "server" "/bin/foo") = some .none
#guard !allows (check (pol [line [u "user"] [ent allAll [] (c "/bin/foo")]]) "user" "root" "root" "server" "/bin/hello")
-- 184-186: tag overriding within one command
#guard auth (check (pol [line [u "user"] [ent allAll [.passwd] (c "/bin/foo")]]) "user" "root" "root" "server" "/bin/foo") = some .passwd
#guard auth (check (pol [line [u "user"] [ent allAll [.nopasswd, .passwd] (c "/bin/foo")]]) "user" "root" "root" "server" "/bin/foo") = some .passwd
#guard auth (check (pol [line [u "user"] [ent allAll [.passwd, .nopasswd] (c "/bin/foo")]]) "user" "root" "root" "server" "/bin/foo") = some .nopasswd
-- 187-189: tags distribute to the following commands only
def tagLine : Policy := pol [line [u "user"] [ent allAll [] (c "/bin/foo"), ent none [.nopasswd] (c "/bin/bar")]]
#guard auth (check tagLine "user" "root" "root" "server" "/bin/foo") = some .none
#guard auth (check tagLine "user" "root" "root" "server" "/bin/bar") = some .nopasswd
#guard auth (check (pol [line [u "user"] [ent allAll [.nopasswd] (c "/bin/foo"), ent none [] (c "/bin/bar")]]) "user" "root" "root" "server" "/bin/bar") = some .nopasswd
-- 190-193: CWD distributes and is overridden
#guard (check (pol [line [u "user"] [ent allAll [.cwd (.path "/")] (c "/bin/foo"), ent none [] (c "/bin/bar")]]) "user" "root" "root" "server" "/bin/bar").map (·.cwd) = some (some (.path "/"))
#guard (check (pol [line [u "user"] [ent allAll [.cwd (.path "/")] (c "/bin/foo"), ent none [.cwd .any] (c "/bin/bar")]]) "user" "root" "root" "server" "/bin/bar").map (·.cwd) = some (some .any)
#guard (check (pol [line [u "user"] [ent allAll [.cwd (.path "/bin"), .cwd .any] (c "/bin/foo")]]) "user" "root" "root" "server" "/bin/foo").map (·.cwd) = some (some .any)
#guard (check (pol [line [u "user"] [ent allAll [.cwd (.path "/usr/bin"), .nopasswd] (c "/bin/foo")]]) "user" "root" "root" "server" "/bin/foo") =
  some { authenticate := .nopasswd, cwd := some (.path "/usr/bin") }
-- 200-201: host lists
#guard allows (check (pol [lineH [u "user"] [h "server"] [ent allAll [] all]]) "user" "root" "root" "server" "/bin/hello")
#guard !allows (check (pol [lineH [u "user"] [h "laptop"] [ent allAll [] all]]) "user" "root" "root" "server" "/bin/hello")
-- 203-204: the last matching line wins
#guard allows (check (pol [line [u "user"] [ent none [] (notC "/bin/hello")], line [u "user"] [ent none [] (c "/bin/hello")]]) "user" "root" "root" "server" "/bin/hello")
#guard !allows (check (pol [line [u "user"] [ent none [] (c "/bin/hello")], line [u "user"] [ent none [] (notC "/bin/hello")]]) "user" "root" "root" "server" "/bin/hello")
-- 206-213: User_Alias GROUP=user1,user2 and GROUP=ALL,!user3
def groupPol (defn : SpecList UserSpecifier) : Policy :=
  pol [line [al "GROUP"] [ent none [] (c "/bin/hello")]] { user := [⟨"GROUP", defn⟩] }
#guard allows (check (groupPol [u "user1", u "user2"]) "user1" "root" "root" "server" "/bin/hello")
#guard allows (check (groupPol [u "user1", u "user2"]) "user2" "root" "root" "server" "/bin/hello")
#guard !allows (check (groupPol [u "user1", u "user2"]) "user3" "root" "root" "server" "/bin/hello")
#guard allows (check (groupPol [all, notU "user3"]) "user1" "root" "root" "server" "/bin/hello")
#guard !allows (check (groupPol [all, notU "user3"]) "user3" "root" "root" "server" "/bin/hello")
-- 214-236: argument patterns and globs
#guard allows (check (pol [line [u "user"] [ent none [] (cx "/bin/hello" ["arg"])]]) "user" "root" "root" "server" "/bin/hello arg")
#guard !allows (check (pol [line [u "user"] [ent none [] (cx "/bin/hello" ["arg"])]]) "user" "root" "root" "server" "/bin/hello boo")
#guard allows (check (pol [line [u "user"] [ent none [] (c "/bin/hello")]]) "user" "root" "root" "server" "/bin/hello boo")
#guard !allows (check (pol [line [u "user"] [ent none [] (cx "/bin/hello" [])]]) "user" "root" "root" "server" "/bin/hello boo")
#guard allows (check (pol [line [u "user"] [ent none [] (cx "/bin/hello" [])]]) "user" "root" "root" "server" "/bin/hello")
#guard allows (check (pol [line [u "user"] [ent none [] (c "/bin/hel*")]]) "user" "root" "root" "server" "/bin/help me")
#guard !allows (check (pol [line [u "user"] [ent none [] (cx "/bin/hel*" ["me"])]]) "user" "root" "root" "server" "/bin/help")
#guard allows (check (pol [line [u "user"] [ent none [] (cx "/bin/hel*" ["me"])]]) "user" "root" "root" "server" "/bin/help me")
#guard !allows (check (pol [line [u "user"] [ent none [] (cx "/bin/hel*" ["me"])]]) "user" "root" "root" "server" "/bin/help me please")
#guard allows (check (pol [line [u "user"] [ent none [] (cp "/bin/hel*" ["me"])]]) "user" "root" "root" "server" "/bin/help me please")
#guard allows (check (pol [line [u "user"] [ent none [] (cp "/bin/hel*" ["me", "please"])]]) "user" "root" "root" "server" "/bin/help me please")
-- 238-241: the NOPASSWD rule of `Sudoers::check`
#guard auth (check (pol [line [u "root"] [ent allAll [] (c "/bin/foo")]]) "root" "root" "root" "server" "/bin/foo") = some .nopasswd
#guard auth (check (pol [line [u "user"] [ent allAll [] (c "/bin/foo")]]) "user" "user" "user" "server" "/bin/foo") = some .nopasswd
#guard auth (check (pol [line [u "user"] [ent allAll [] (c "/bin/foo")]]) "user" "user" "root" "server" "/bin/foo") = some .none
-- 244-252: numeric user and group ids
#guard allows (check (pol [lineH [uid 1466] [h "server"] [ent allAll [] all]]) "user" "root" "root" "server" "/bin/hello")
#guard allows (check (pol [lineH [gidU 1466] [h "server"] [ent allAll [] all]]) "user" "root" "root" "server" "/bin/hello")
#guard !allows (check (pol [lineH [uid 1466] [h "server"] [ent allAll [] all]]) "root" "root" "root" "server" "/bin/hello")
#guard allows (check (pol [lineH [u "foo", uid 1234, uid 1466] [h "server"] [ent allAll [] all]]) "user" "root" "root" "server" "/bin/hello")
#guard !allows (check (pol [lineH [u "foo", uid 1234, uid 1366] [h "server"] [ent allAll [] all]]) "user" "root" "root" "server" "/bin/hello")
-- 253-262: runas user and group lists
#guard allows (check (pol [line [u "user"] [ent (some ⟨[all], [gid 1466]⟩) [] (c "/bin/foo")]]) "user" "root" "root" "server" "/bin/foo")
#guard !allows (check (pol [line [u "user"] [ent (some ⟨[all], [gid 1466]⟩) [] (c "/bin/foo")]]) "user" "root" "other" "server" "/bin/foo")
#guard allows (check (pol [line [u "user"] [ent (some ⟨[all], [gid 1466]⟩) [] (c "/bin/foo")]]) "user" "root" "user" "server" "/bin/foo")
#guard allows (check (pol [line [u "user"] [ent (some ⟨[u "root", u "user"], [all]⟩) [] (c "/bin/foo")]]) "user" "root" "wheel" "server" "/bin/foo")
#guard allows (check (pol [line [u "user"] [ent (some ⟨[u "root", u "user"], [all]⟩) [] (c "/bin/foo")]]) "user" "user" "wheel" "server" "/bin/foo")
#guard !allows (check (pol [line [u "user"] [ent (some ⟨[u "root", u "user"], [all]⟩) [] (c "/bin/foo")]]) "user" "sudo" "wheel" "server" "/bin/foo")
#guard !allows (check (pol [line [u "user"] [ent (some ⟨[uid 0], [g "wheel"]⟩) [] (c "/bin/foo")]]) "user" "sudo" "wheel" "server" "/bin/foo")
#guard allows (check (pol [line [u "user"] [ent (some ⟨[uid 0], [g "wheel"]⟩) [] (c "/bin/foo")]]) "user" "root" "root" "server" "/bin/foo")
#guard !allows (check (pol [line [u "user"] [ent (some ⟨[gidU 1466], [g "wheel"]⟩) [] (c "/bin/foo")]]) "user" "root" "root" "server" "/bin/foo")
#guard allows (check (pol [line [u "user"] [ent (some ⟨[gidU 1466], [g "wheel"]⟩) [] (c "/bin/foo")]]) "user" "user" "user" "server" "/bin/foo")
-- 265-275: singular runas spec, no runas spec, and "-g only"
#guard !allows (check (pol [line [u "user"] [ent (some ⟨[all], []⟩) [] (c "/bin/foo")]]) "user" "sudo" "wheel" "server" "/bin/foo")
#guard allows (check (pol [line [u "user"] [ent (some ⟨[all], []⟩) [] (c "/bin/foo")]]) "user" "sudo" "sudo" "server" "/bin/foo")
#guard !allows (check (pol [line [u "user"] [ent none [] (c "/bin/foo")]]) "user" "sudo" "sudo" "server" "/bin/foo")
#guard !allows (check (pol [line [u "user"] [ent none [] (c "/bin/foo")]]) "user" "sudo" "root" "server" "/bin/foo")
#guard !allows (check (pol [line [u "user"] [ent none [] (c "/bin/foo")]]) "user" "root" "sudo" "server" "/bin/foo")
#guard allows (check (pol [line [u "user"] [ent none [] (c "/bin/foo")]]) "user" "root" "root" "server" "/bin/foo")
#guard allows (check (pol [line [u "user"] [ent (some ⟨[u "sudo"], [g "sudo"]⟩) [] (c "/bin/foo")]]) "user" "user" "sudo" "server" "/bin/foo")
-- 278-282: runas specs distribute along the line until overridden
def twoRunas (mods : List Modifier) : Policy :=
  pol [line [u "user"] [ent (some ⟨[u "root"], []⟩) mods (c "/bin/ls"), ent (some ⟨[u "sudo"], []⟩) [] (c "/bin/true")]]
#guard allows (check (twoRunas []) "user" "root" "root" "server" "/bin/ls")
#guard auth (check (twoRunas [.nopasswd]) "user" "sudo" "sudo" "server" "/bin/true") = some .nopasswd
#guard !allows (check (twoRunas []) "user" "sudo" "sudo" "server" "/bin/ls")
#guard !allows (check (twoRunas []) "user" "root" "root" "server" "/bin/true")
#guard allows (check (pol [line [u "user"] [ent (some ⟨[u "root"], []⟩) [.nopasswd] (c "/bin/ls"), ent (some ⟨[u "sudo"], []⟩) [] (c "/bin/ls"), ent none [] (c "/bin/true")]]) "user" "sudo" "sudo" "server" "/bin/true")
-- 293-296: User_Alias FULLTIME=ALL,!marc
def fulltime (n : Nat) (users : SpecList UserSpecifier) : Policy :=
  pol [line users [ent none [] all]]
    { user := [⟨"FULLTIME", [all, if n % 2 = 1 then notU "marc" else u "marc"]⟩] }
#guard allows (check (fulltime 1 [al "FULLTIME"]) "user" "root" "root" "server" "/bin/bash")
#guard !allows (check (fulltime 1 [al "FULLTIME"]) "marc" "root" "root" "server" "/bin/bash")
#guard !allows (check (fulltime 1 [all, notAl "FULLTIME"]) "user" "root" "root" "server" "/bin/bash")
#guard allows (check (fulltime 3 [all, notAl "FULLTIME"]) "marc" "root" "root" "server" "/bin/bash")
-- 297-302: Host_Alias and Cmnd_Alias
def machine : AliasTable := { host := [⟨"MACHINE", [h "laptop", h "server"]⟩] }
#guard allows (check (pol [lineH [u "user"] [al "MACHINE"] [ent none [] all]] machine) "user" "root" "root" "server" "/bin/bash")
#guard allows (check (pol [lineH [u "user"] [al "MACHINE"] [ent none [] all]] machine) "user" "root" "root" "laptop" "/bin/bash")
#guard !allows (check (pol [lineH [u "user"] [al "MACHINE"] [ent none [] all]] machine) "user" "root" "root" "desktop" "/bin/bash")
def what : AliasTable := { cmnd := [⟨"WHAT", [c "/bin/dd", c "/bin/rm"]⟩] }
#guard allows (check (pol [line [u "user"] [ent none [] (al "WHAT")]] what) "user" "root" "root" "server" "/bin/rm")
#guard !allows (check (pol [line [u "user"] [ent none [] (al "WHAT")]] what) "user" "root" "root" "server" "/bin/bash")
-- 304-306: nested aliases (tables in processing order: B before A)
#guard allows (check (pol [line [al "A"] [ent none [] all]] { user := [⟨"B", [u "user"]⟩, ⟨"A", [al "B"]⟩] }) "user" "root" "root" "vm" "/bin/ls")
#guard allows (check (pol [lineH [all] [al "A"] [ent none [] all]] { host := [⟨"B", [h "vm"]⟩, ⟨"A", [al "B"]⟩] }) "user" "root" "root" "vm" "/bin/ls")
#guard allows (check (pol [line [all] [ent none [] (al "A")]] { cmnd := [⟨"B", [c "/bin/ls"]⟩, ⟨"A", [al "B"]⟩] }) "user" "root" "root" "vm" "/bin/ls")
-- 308-312: Runas_Alias TIME=%wheel,!!sudo
def time : AliasTable := { runas := [⟨"TIME", [grp "wheel", u "sudo"]⟩] }
#guard !allows (check (pol [line [u "user"] [ent (some ⟨[], []⟩) [] all]] time) "user" "sudo" "sudo" "vm" "/bin/ls")
#guard allows (check (pol [line [u "user"] [ent (some ⟨[al "TIME"], []⟩) [] all]] time) "user" "sudo" "sudo" "vm" "/bin/ls")
#guard !allows (check (pol [line [u "user"] [ent (some ⟨[], [al "TIME"]⟩) [] all]] time) "user" "sudo" "sudo" "vm" "/bin/ls")
#guard allows (check (pol [line [u "user"] [ent (some ⟨[], [al "TIME"]⟩) [] all]] time) "user" "user" "sudo" "vm" "/bin/ls")
#guard allows (check (pol [line [u "user"] [ent (some ⟨[al "TIME"], []⟩) [] all]] time) "user" "wheel" "wheel" "vm" "/bin/ls")
-- 317-318: the substitution-like alias mechanism (User_Alias FOO=!user)
def foo : AliasTable := { user := [⟨"FOO", [notU "user"]⟩] }
#guard !allows (check (pol [line [all, al "FOO"] [ent none [] all]] foo) "user" "root" "root" "vm" "/bin/ls")
#guard allows (check (pol [line [notAl "FOO"] [ent none [] all]] foo) "user" "root" "root" "vm" "/bin/ls")
-- 335-336: the `list` pseudo-command
#guard allows (check (pol [line [all] [ent allAll [] (c "/bin/ls"), ent none [] (c "list")]]) "user" "root" "root" "server" "list")
#guard !allows (check (pol [line [all] [ent allAll [] all, ent none [] (notC "list")]]) "user" "root" "root" "server" "list")

/-! ## Further behaviour pinned down by the spec -/

-- the implicit SETENV of a literal ALL, and NOSETENV overriding it
#guard (check (pol [line [u "user"] [ent allAll [] all]]) "user" "root" "root" "server" "/bin/sh").map (·.env) = some .setenv
#guard (check (pol [line [u "user"] [ent allAll [.nosetenv] all]]) "user" "root" "root" "server" "/bin/sh").map (·.env) = some .nosetenv
-- ... which does not distribute to later commands
#guard (check (pol [line [u "user"] [ent allAll [] all, ent none [] (c "/bin/sh")]]) "user" "root" "root" "server" "/bin/sh").map (·.env) = some .implicit
-- ... and is not given to ALL reached through a Cmnd_Alias
#guard (check (pol [line [u "user"] [ent allAll [] (al "EVERY")]] { cmnd := [⟨"EVERY", [all]⟩] }) "user" "root" "root" "server" "/bin/sh").map (·.env) = some .implicit
-- a negated user only makes its line inapplicable: an earlier grant survives
#guard allows (check (pol [line [u "marc"] [ent none [] (c "/bin/ls")], line [all, notU "marc"] [ent none [] notAll]]) "marc" "root" "root" "server" "/bin/ls")
-- running as oneself with a group outside the runas user list (only the group list is checked)
#guard allows (check (pol [line [u "user"] [ent (some ⟨[u "root"], [g "wheel"]⟩) [] (c "/bin/foo")]]) "user" "user" "wheel" "server" "/bin/foo")
-- an undefined alias never matches
#guard !allows (check (pol [line [al "NOPE"] [ent none [] all]]) "user" "root" "root" "server" "/bin/ls")
-- an entry whose runas spec rejects the request does not take part, so its `!` revokes nothing
#guard allows (check (pol [line [u "user"] [ent (some ⟨[u "root"], []⟩) [] (c "/bin/sh")],
  line [u "user"] [ent (some ⟨[u "bob"], []⟩) [] (notC "/bin/sh")]]) "user" "root" "root" "server" "/bin/sh")
-- runas specs and tags do not carry over a `:` to the next Host_List group
def colonLine : Policy :=
  pol [⟨[u "user"], [([h "host1"], [ent (some ⟨[u "bob"], []⟩) [.nopasswd] (c "/a")]),
    ([h "host2"], [ent none [] (c "/b")])]⟩]
#guard auth (check colonLine "user" "bob" "bob" "host1" "/a") = some .nopasswd
#guard !allows (check colonLine "user" "bob" "bob" "host2" "/b")
#guard auth (check colonLine "user" "root" "root" "host2" "/b") = some .none

/-! ## Kernel-checked examples

`decide` cannot unfold the well-founded recursions of `globChars` and `String.foldl` (used by
`cksum` for names other than `root`), so these use the same oracle with literal path
comparison (`namedExact`, which agrees with `named` on patterns without wildcards) and only
compute group ids of `root`. -/

def namedExact : Oracle String String := { named with globMatches := fun pat path => pat == path }

example : cksum "root" = 0 := by decide
example : authorize namedExact (pol []) ⟨"user", "server", "root", "root", "/bin/ls", []⟩ = none := by
  decide
example : authorize namedExact (pol [line [u "user"] [ent none [] (c "/bin/ls")]])
    ⟨"user", "server", "root", "root", "/bin/ls", []⟩ = some {} := by
  decide
example : authorize namedExact (pol [line [u "user"] [ent none [] (c "/bin/ls"), ent none [] (notC "/bin/ls")]])
    ⟨"user", "server", "root", "root", "/bin/ls", []⟩ = none := by
  decide
example : authorize namedExact (pol [line [u "root"] [ent (some allAll) [] all]])
    ⟨"root", "server", "root", "root", "/bin/sh", []⟩ = some { authenticate := .nopasswd, env := .setenv } := by
  decide
example : authorize namedExact (pol [line [notAl "FOO"] [ent none [] all]] foo)
    ⟨"user", "vm", "root", "root", "/bin/ls", []⟩ = some { env := .setenv } := by
  decide

end SudoersSpec.Examples
