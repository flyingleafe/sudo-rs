// -*- mode: Bluespec; -*-
// Linux process credentials and the set*id system calls.
//
// Semantics follow Chen, Wagner, Dean, "Setuid Demystified" (USENIX Sec 2002)
// for Linux, restricted to the calls sudo uses:
//  * a process is privileged (holds CAP_SETUID / CAP_SETGID) iff its effective
//    uid is 0 (no file capabilities, default securebits);
//  * setresuid(r, e, s): unprivileged callers may set each id only to one of
//    the current real/effective/saved uids; privileged callers to anything;
//  * setresgid: same rule over the gids (privilege still comes from euid 0);
//  * setgroups: privileged callers only;
//  * the argument -1 (KEEP) leaves the corresponding id unchanged.
// Every call may also fail although it is permitted (ENOMEM in
// prepare_creds, LSM or seccomp denial, RLIMIT_NPROC on older kernels); the
// caller passes `fault` to select that outcome. A failed call changes nothing.
module kernel {
  type Creds = {
    ruid: int, euid: int, suid: int,
    rgid: int, egid: int, sgid: int,
    groups: Set[int],
  }
  type Result = { ok: bool, creds: Creds }

  pure val KEEP = -1

  pure def credsFor(uid: int, gid: int, groups: Set[int]): Creds =
    { ruid: uid, euid: uid, suid: uid, rgid: gid, egid: gid, sgid: gid, groups: groups }

  pure def isPrivileged(c: Creds): bool = c.euid == 0

  pure def anyRootUid(c: Creds): bool = c.ruid == 0 or c.euid == 0 or c.suid == 0

  pure def holdsRoot(c: Creds): bool =
    anyRootUid(c) or c.rgid == 0 or c.egid == 0 or c.sgid == 0 or c.groups.contains(0)

  pure def keep(cur: int, x: int): int = if (x == KEEP) cur else x

  pure def uidAllowed(c: Creds, x: int): bool =
    x == KEEP or isPrivileged(c) or x == c.ruid or x == c.euid or x == c.suid

  pure def gidAllowed(c: Creds, x: int): bool =
    x == KEEP or isPrivileged(c) or x == c.rgid or x == c.egid or x == c.sgid

  pure def setresuid(c: Creds, r: int, e: int, s: int, fault: bool): Result =
    if (uidAllowed(c, r) and uidAllowed(c, e) and uidAllowed(c, s) and not(fault))
      { ok: true, creds: { ...c, ruid: keep(c.ruid, r), euid: keep(c.euid, e), suid: keep(c.suid, s) } }
    else
      { ok: false, creds: c }

  pure def setresgid(c: Creds, r: int, e: int, s: int, fault: bool): Result =
    if (gidAllowed(c, r) and gidAllowed(c, e) and gidAllowed(c, s) and not(fault))
      { ok: true, creds: { ...c, rgid: keep(c.rgid, r), egid: keep(c.egid, e), sgid: keep(c.sgid, s) } }
    else
      { ok: false, creds: c }

  pure def setgroups(c: Creds, gs: Set[int], fault: bool): Result =
    if (isPrivileged(c) and not(fault)) { ok: true, creds: { ...c, groups: gs } }
    else { ok: false, creds: c }

  // Credentials of a setuid-root binary right after execve by `uid`.
  pure def setuidRootExec(uid: int, gid: int, groups: Set[int]): Creds =
    { ruid: uid, euid: 0, suid: 0, rgid: gid, egid: gid, sgid: gid, groups: groups }
}
