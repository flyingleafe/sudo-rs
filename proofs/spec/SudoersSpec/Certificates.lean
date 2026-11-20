import SudoersSpec.RunasManual
import SudoersSpec.Examples

/-!
# Kernel-checked certificates

Concrete policies and requests, decided by the Lean kernel (`by decide`, no `native_decide`):
the expected behaviour (a), (b); findings F1-F5 of `proofs/differential/README.md` (c)-(g),
each with the property it violates; and one example per property P1-P9 of `Properties.lean`
showing that its hypotheses can hold (h).

The oracle is the one of `Examples.namedExact` (names compared as strings, literal command
paths) with two changes that the findings need: fixed uids and gids, including a second uid-0
account `toor` whose name is not `root`, and an explicit group-membership table. `is_root` is
`has_uid(0)`, as in `src/system/interface.rs`.

| user | uid | groups (gid) |   | group | gid |
|---|---|---|---|---|---|
| root | 0 | root (0), wheel (10) | | root | 0 |
| toor | 0 | root (0) | | wheel | 10 |
| alice | 1000 | alice (1000); `aliceWheel`: also wheel (10) | | alice | 1000 |
| bob | 1001 | bob (1001) | | bob | 1001 |
-/

namespace SudoersSpec.Certificates

open SudoersSpec SudoersSpec.Examples

def uidOf (u : String) : Nat :=
  if u == "root" then 0 else if u == "toor" then 0 else if u == "alice" then 1000
  else if u == "bob" then 1001 else 65534

def gidOf (g : String) : Nat :=
  if g == "root" then 0 else if g == "wheel" then 10 else if g == "alice" then 1000
  else if g == "bob" then 1001 else 65534

/-- Group membership: `(user, gid)`. -/
def members : List (String × Nat) := [("root", 0), ("root", 10), ("toor", 0), ("alice", 1000),
  ("bob", 1001)]

/-- The same with alice in wheel. -/
def membersAliceWheel : List (String × Nat) := ("alice", 10) :: members

def oracle (mem : List (String × Nat)) : Oracle String String where
  hasName u n := u == n
  hasUid u n := uidOf u == n
  isRoot u := uidOf u == 0
  inGroupByName u n := mem.any fun m => m.1 == u && m.2 == gidOf n
  inGroupByGid u n := mem.any fun m => m.1 == u && m.2 == n
  userEq u v := u == v
  asGid g := gidOf g
  tryAsName g := some g
  globMatches pat path := pat == path
  hostMatches pat host := pat == host

theorem oracle_sudoRsHosts (mem : List (String × Nat)) : (oracle mem).SudoRsHosts :=
  fun _ _ => rfl

/-- alice is not in wheel. -/
abbrev O₀ : Oracle String String := oracle members
/-- alice is in wheel. -/
abbrev OW : Oracle String String := oracle membersAliceWheel

/-- `sudo [-u target] [-g group] cmd args` by `invoking` on `host`. -/
def req (invoking host target group cmd : String) (args : List String := []) :
    Request String String :=
  ⟨invoking, host, target, group, cmd, args⟩

/-- `!name` in a runas group list. -/
def notG (n : String) : Spec Identifier := .forbid (.only (.name n))

/-! ## (a), (b): negation behaves as documented -/

/-- (a) `alice ALL = !/usr/bin/su` followed by `alice ALL = ALL`: the later line wins, `su` is
allowed (with the implicit SETENV of `ALL`). -/
theorem a_later_all_allows_su :
    authorize O₀ (pol [line [u "alice"] [ent none [] (notC "/usr/bin/su")],
        line [u "alice"] [ent none [] all]])
      (req "alice" "h1" "root" "root" "/usr/bin/su") = some { env := .setenv } := by
  decide

/-- (b) `!alice` in a later line's user list does not revoke alice's grant from an earlier
line, even with `!ALL` as its command. -/
theorem b_negated_user_cannot_revoke :
    authorize O₀ (pol [line [u "alice"] [ent none [] (c "/bin/ls")],
        line [all, notU "alice"] [ent none [] notAll]])
      (req "alice" "h1" "root" "root" "/bin/ls") = some {} := by
  decide

/-! ## (c)-(g): findings F1-F5 -/

/-- (c) F1, intended and documented: `alice h1 = /bin/ls -l *` allows `/bin/ls -l` (the
trailing `*` matches zero further arguments) and `/bin/ls -l /tmp`. -/
theorem c_f1_trailing_star :
    authorize O₀ (pol [lineH [u "alice"] [h "h1"] [ent none [] (cp "/bin/ls" ["-l"])]])
        (req "alice" "h1" "root" "root" "/bin/ls" ["-l"]) = some {} ∧
      authorize O₀ (pol [lineH [u "alice"] [h "h1"] [ent none [] (cp "/bin/ls" ["-l"])]])
        (req "alice" "h1" "root" "root" "/bin/ls" ["-l", "/tmp"]) = some {} := by
  decide

/-- The F2 policy: `alice ALL = /bin/ls`, no runas spec. -/
def f2Pol : Policy := pol [line [u "alice"] [ent none [] (c "/bin/ls")]]
/-- `sudo -u toor /bin/ls` by alice (toor's primary group is root). -/
def f2Req : Request String String := req "alice" "h1" "toor" "root" "/bin/ls"

/-- (d) F2, violating the documented P2r: `toor` is not the invoker, no runas list or
Runas_Alias mentions it, it is not named `root`, and the manual's reading of "no Runas_Spec"
denies; sudo-rs allows, because `toor` has uid 0. -/
theorem d_f2_toor :
    runasUserMentioned O₀ f2Pol f2Req = false ∧
      O₀.userEq f2Req.targetUser f2Req.invokingUser = false ∧
      O₀.hasName f2Req.targetUser "root" = false ∧
      runasManual O₀ f2Req (runasUserAliases O₀ f2Pol f2Req) (runasGroupAliases O₀ f2Pol f2Req)
        false none = false ∧
      authorize O₀ f2Pol f2Req = some {} := by
  decide

/-- The F3 policy: `alice ALL = (root : !wheel) /bin/ls`. -/
def f3Pol : Policy :=
  pol [line [u "alice"] [ent (some ⟨[u "root"], [notG "wheel"]⟩) [] (c "/bin/ls")]]

/-- (e) F3, violating "a `!` in a runas list switches the entry off": `sudo -u root -g wheel
/bin/ls` is allowed although the group list excludes wheel, because root is in wheel. With the
group list `(root : wheel)` or `(root)` the result is the same (`runas_grouplist_ignored`). -/
theorem e_f3_negated_group :
    inGroup O₀ "root" "wheel" = true ∧
      authorize O₀ f3Pol (req "alice" "h1" "root" "wheel" "/bin/ls") = some {} := by
  decide

/-- The F4 policy: `alice ALL = (root : wheel) /usr/local/bin/ls`. -/
def f4Pol : Policy :=
  pol [line [u "alice"] [ent (some ⟨[u "root"], [g "wheel"]⟩) [] (c "/usr/local/bin/ls")]]
/-- `sudo -g wheel /usr/local/bin/ls` by alice: the target user is alice. -/
def f4Req : Request String String := req "alice" "h1" "alice" "wheel" "/usr/local/bin/ls"
def f4RunAs : RunAs := ⟨[u "root"], [g "wheel"]⟩

/-- (f) F4, alice in wheel: the manual allows `sudo -g wheel` (wheel is listed, and it is one
of alice's groups); sudo-rs denies, because alice is not in the user list `(root)`. -/
theorem f_f4_member_denied :
    runasManual OW f4Req (runasUserAliases OW f4Pol f4Req) (runasGroupAliases OW f4Pol f4Req)
        true (some f4RunAs) = true ∧
      F4Case OW f4Req (runasUserAliases OW f4Pol f4Req) true f4RunAs = true ∧
      authorize OW f4Pol f4Req = none := by
  decide

/-- (f) F4, alice not in wheel: both allow. Being in the group makes sudo-rs deny. -/
theorem f_f4_nonmember_allowed :
    runasManual O₀ f4Req (runasUserAliases O₀ f4Pol f4Req) (runasGroupAliases O₀ f4Pol f4Req)
        true (some f4RunAs) = true ∧
      authorize O₀ f4Pol f4Req = some {} := by
  decide

/-- The F5 policy: `alice ALL = (!alice : wheel) /bin/ls`. -/
def f5Pol : Policy :=
  pol [line [u "alice"] [ent (some ⟨[notU "alice"], [g "wheel"]⟩) [] (c "/bin/ls")]]

/-- (g) F5, violating "a `!` in a runas list switches the entry off": `sudo -g wheel /bin/ls`
by alice (not in wheel) is allowed although the user list excludes alice: the user list is not
consulted (`runas_userlist_ignored`). -/
theorem g_f5_negated_self :
    inGroup O₀ "alice" "wheel" = false ∧
      authorize O₀ f5Pol (req "alice" "h1" "alice" "wheel" "/bin/ls") = some {} := by
  decide

/-- (g) F5 without `!`, against the manual: `alice ALL = (root : wheel) /bin/ls`,
`sudo -u alice -g wheel` (`gOnly = false`): the manual denies (alice is not in `(root)`),
sudo-rs allows. -/
theorem g_f5_manual :
    runasManual O₀ f4Req (runasUserAliases O₀ f4Pol f4Req) (runasGroupAliases O₀ f4Pol f4Req)
        false (some f4RunAs) = false ∧
      F5Case O₀ f4Req (runasUserAliases O₀ f4Pol f4Req) (runasGroupAliases O₀ f4Pol f4Req) false
        f4RunAs = true ∧
      authorize O₀ f4Pol f4Req = some {} := by
  decide

/-! ## (h) The hypotheses of P1-P9 can hold -/

/-- Two lines for alice; the second decides `/bin/ls`. -/
def p1Pol : Policy :=
  pol [line [u "alice"] [ent none [] (notC "/bin/ls")],
    line [u "alice"] [ent none [.nopasswd] (c "/bin/cat"), ent none [] (c "/bin/ls")]]
def lsReq : Request String String := req "alice" "h1" "root" "root" "/bin/ls"

/-- P1: the deciding entry is the second entry of the second line; it carries the NOPASSWD of
the first entry. -/
theorem h_p1 :
    decidingEntry O₀ p1Pol lsReq = some (none, ({ authenticate := .nopasswd }, c "/bin/ls")) ∧
      authorize O₀ p1Pol lsReq = some { authenticate := .nopasswd } := by
  decide

/-- A policy for bob only. -/
def bobPol : Policy := pol [lineH [u "bob"] [h "h1"] [ent none [] (c "/bin/ls")]]

/-- P2, users: bob's policy does not mention alice; it allows bob. -/
theorem h_p2_user :
    userMentioned O₀ bobPol lsReq = false ∧ authorize O₀ bobPol lsReq = none ∧
      (authorize O₀ bobPol (req "bob" "h1" "root" "root" "/bin/ls")).isSome = true :=
  ⟨by decide, unmentioned_user_unmatched O₀ _ _ (by decide), by decide⟩

/-- P2, hosts: host h2 is not mentioned. -/
theorem h_p2_host :
    hostMentioned O₀ bobPol (req "bob" "h2" "root" "root" "/bin/ls") = false ∧
      authorize O₀ bobPol (req "bob" "h2" "root" "root" "/bin/ls") = none :=
  ⟨by decide, unmentioned_host_unmatched O₀ _ _ (by decide)⟩

/-- P2, commands: `/bin/sh` is not mentioned, also not by a Cmnd_Alias. -/
theorem h_p2_command :
    cmdMentioned O₀ (pol [line [u "bob"] [ent none [] (al "LS")]] { cmnd := [⟨"LS", [c "/bin/ls"]⟩] })
        (req "bob" "h1" "root" "root" "/bin/sh") = false ∧
      authorize O₀ (pol [line [u "bob"] [ent none [] (al "LS")]] { cmnd := [⟨"LS", [c "/bin/ls"]⟩] })
        (req "bob" "h1" "root" "root" "/bin/sh") = none :=
  ⟨by decide, unmentioned_command_unmatched O₀ _ _ (by decide)⟩

/-- P2r: F2's request meets the hypotheses; the conclusion says the deciding entry has no
runas spec and `toor` is root by uid. -/
theorem h_p2r : O₀.isRoot f2Req.targetUser = true ∧
    ∃ e, decidingEntry O₀ f2Pol f2Req = some e ∧ e.1 = none :=
  unmentioned_runas_target O₀ f2Pol f2Req {} (by decide) (by decide) (by decide)

/-- `alice ALL = /bin/ls, !/bin/ls`. -/
def p3Pol : Policy := pol [line [u "alice"] [ent none [] (c "/bin/ls"), ent none [] (notC "/bin/ls")]]
/-- `Cmnd_Alias LS = !/bin/ls`, `alice ALL = /bin/ls, LS`. -/
def p3AliasPol : Policy :=
  pol [line [u "alice"] [ent none [] (c "/bin/ls"), ent none [] (al "LS")]]
    { cmnd := [⟨"LS", [notC "/bin/ls"]⟩] }

/-- P3: an allowed entry takes part and the request is denied, once through `!/bin/ls`, once
through a reference to `Cmnd_Alias LS = !/bin/ls`, which excludes `/bin/ls` explicitly. -/
theorem h_p3 :
    (∃ e ∈ allowedSpec O₀ p3Pol lsReq, cmdParticipates O₀ p3Pol lsReq e = true) ∧
      authorize O₀ p3Pol lsReq = none ∧
      (∃ e ∈ allowedSpec O₀ p3AliasPol lsReq, cmdParticipates O₀ p3AliasPol lsReq e = true) ∧
      authorize O₀ p3AliasPol lsReq = none ∧
      cmndAliases O₀ p3AliasPol lsReq "LS" = some false := by
  decide

/-- P3b, hosts: `alice h1 = /bin/ls : h2 = !/bin/ls`; on h1 the h2 group is irrelevant. -/
theorem h_p3b :
    authorize O₀ (pol [⟨[u "alice"], [([h "h1"], [ent none [] (c "/bin/ls")]),
        ([h "h2"], [ent none [] (notC "/bin/ls")])]⟩]) lsReq = some {} ∧
      hostListMatches O₀ (pol []) lsReq [h "h2"] = false := by
  decide

/-- P4: line `alice ALL = /bin/ls` decides; a later bob line does not take part; the earlier
`alice ALL = !/bin/ls` and the empty prefix give the same answer. -/
theorem h_p4 :
    (∃ e ∈ ruleCandidates O₀ (pol []) lsReq (line [u "alice"] [ent none [] (c "/bin/ls")]),
        entryDecides O₀ (pol []) lsReq e = true) ∧
      (∀ R' ∈ [line [u "bob"] [ent none [] notAll]],
        ∀ e ∈ ruleCandidates O₀ (pol []) lsReq R', entryDecides O₀ (pol []) lsReq e = false) ∧
      authorize O₀ (pol [line [u "alice"] [ent none [] (notC "/bin/ls")],
        line [u "alice"] [ent none [] (c "/bin/ls")], line [u "bob"] [ent none [] notAll]]) lsReq =
        some {} := by
  decide

/-- P5: a line for bob with `!ALL` inserted before alice's grant changes nothing. -/
theorem h_p5 :
    userListMatches O₀ (pol []) lsReq [u "bob"] = false ∧
      authorize O₀ (pol [line [u "bob"] [ent none [] notAll], line [u "alice"] [ent none [] (c "/bin/ls")]])
        lsReq = some {} := by
  decide

/-- P6: inserting `alice ALL = (bob) /bin/sh` (no command-side `!`) after a grant keeps it. -/
theorem h_p6 :
    (∀ seg ∈ (line [u "alice"] [ent (some ⟨[u "bob"], []⟩) [] (c "/bin/sh")]).permissions,
        ∀ x ∈ seg.2, x.2.cmd.isAllow = true) ∧
      (authorize O₀ (pol [line [u "alice"] [ent none [] (c "/bin/ls")]]) lsReq).isSome = true ∧
      (authorize O₀ (pol [line [u "alice"] [ent none [] (c "/bin/ls")],
        line [u "alice"] [ent (some ⟨[u "bob"], []⟩) [] (c "/bin/sh")]]) lsReq).isSome = true := by
  decide

/-- `alice ALL = (: wheel) /bin/ls`. -/
def p7Pol : Policy := pol [line [u "alice"] [ent (some ⟨[], [g "wheel"]⟩) [] (c "/bin/ls")]]

/-- P7: `(: wheel)` lets alice run with group wheel as herself, not as bob. -/
theorem h_p7 :
    decidingEntry O₀ p7Pol (req "alice" "h1" "alice" "wheel" "/bin/ls") =
        some (some ⟨[], [g "wheel"]⟩, ({}, c "/bin/ls")) ∧
      authorize O₀ p7Pol (req "alice" "h1" "alice" "wheel" "/bin/ls") = some {} ∧
      authorize O₀ p7Pol (req "alice" "h1" "bob" "wheel" "/bin/ls") = none := by
  decide

/-- P8: `alice ALL = (bob : wheel) /bin/ls`: bob is not in wheel, wheel is listed. -/
theorem h_p8 :
    inGroup O₀ "bob" "wheel" = false ∧
      authorize O₀ (pol [line [u "alice"] [ent (some ⟨[u "bob"], [g "wheel"]⟩) [] (c "/bin/ls")]])
        (req "alice" "h1" "bob" "wheel" "/bin/ls") = some {} := by
  decide

/-- `alice h1 = NOPASSWD: /bin/cat, /bin/ls : h1 = /bin/sh`. -/
def p9Pol : Policy :=
  pol [⟨[u "alice"], [([h "h1"], [ent none [.nopasswd] (c "/bin/cat"), ent none [] (c "/bin/ls")]),
    ([h "h1"], [ent none [] (c "/bin/sh")])]⟩]

/-- P9: NOPASSWD carries to `/bin/ls` (entry 1 of the first group, the tag is in the prefix)
but not across `:` to `/bin/sh`. -/
theorem h_p9 :
    authorize O₀ p9Pol lsReq = some { authenticate := .nopasswd } ∧
      (distributeTagsSpec [ent none [.nopasswd] (c "/bin/cat"), ent none [] (c "/bin/ls")])[1]? =
        decidingEntry O₀ p9Pol lsReq ∧
      authorize O₀ p9Pol (req "alice" "h1" "root" "root" "/bin/sh") = some {} := by
  decide

end SudoersSpec.Certificates
