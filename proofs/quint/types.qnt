// -*- mode: Bluespec; -*-
// Finite universe shared by every module of the sudo lifecycle model.
//
// The system has one real host, four accounts and two login sessions. Account
// names, gids and supplementary groups come from the trusted (system) user
// database; a lookup through an attacker-chosen NSS configuration is modelled
// separately in `sudo.qnt`.
module types {
  // ---- accounts ----------------------------------------------------------
  pure val ROOT = 0
  pure val ALICE = 1
  pure val BOB = 2
  // An account whose (directory-service supplied) name contains `../`.
  pure val EVIL = 3
  pure val USERS = Set(ROOT, ALICE, BOB, EVIL)
  // The adversary is any unprivileged account.
  pure val INVOKERS = Set(ALICE, BOB, EVIL)
  // `-u#-1` and `-u#4294967295` denote the same 32-bit value, which the kernel
  // reads as "leave unchanged" in setres[ug]id.
  pure val UID_MINUS_ONE = -1
  // Numeric uids an attacker can name with `-u#N`.
  pure val NUMERIC_UIDS = USERS.union(Set(UID_MINUS_ONE))
  // Gids an attacker can name with `-g`.
  pure val GIDS = Set(0, 1, 2, 3)

  pure def userName(u: int): str =
    if (u == ROOT) "root"
    else if (u == ALICE) "alice"
    else if (u == BOB) "bob"
    else if (u == EVIL) "../ts/bob"
    else "#unknown"

  // Owner of the file `<timestamp dir>/<name>` after the kernel resolves the
  // path lexically: `../ts/bob` lands on bob's file.
  pure def tsPathOwnerByName(name: str): int =
    if (name == "root") ROOT
    else if (name == "alice") ALICE
    else if (name == "bob" or name == "../ts/bob") BOB
    else UID_MINUS_ONE

  // gid == uid convention; unknown ids have no passwd entry.
  pure def primaryGid(u: int): int = u
  pure def suppGroups(u: int): Set[int] = if (USERS.contains(u)) Set(u) else Set()

  // ---- hosts, commands, files, sessions, time ---------------------------
  pure val REAL_HOST = "h1"
  pure val HOSTS = Set("h1", "h2")
  pure val COMMANDS = Set("c1", "c2")
  // Files sudoedit may be asked to edit.
  pure val FILES = Set("f1", "f2")
  // sudoedit is authorised per file: `sudoedit f1` is the command `edit_f1`.
  pure def editCmd(f: str): str = if (f == "f1") "edit_f1" else "edit_f2"
  pure val SESSIONS = Set(1, 2)
  pure val PIDS = Set(1, 2)

  // Wall-clock time in abstract ticks and the ticket lifetime.
  pure val MAX_TIME = 2
  pure val TIMEOUT = 1
  // Offsets an attacker-chosen TZ adds to local time.
  pure val TZ_OFFSETS = Set(-1, 0, 1)
  pure def clampTime(t: int): int = if (t < 0) 0 else if (t > MAX_TIME) MAX_TIME else t

  // A permitted credential call fails when the roll is 0. Both outcomes stay
  // reachable (Apalache explores both); the 1-in-4 ratio only keeps random
  // simulation from aborting most runs before they reach exec.
  pure val FAULT_ROLLS = 0.to(3)
  pure def isFault(roll: int): bool = roll == 0
}
