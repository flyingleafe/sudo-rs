// -*- mode: Bluespec; -*-
// Lifecycle of sudo invocations, parameterised by implementation features
// (IMPL) and by the set of historical bugs switched on (BUGS).
//
// Two invocation slots run concurrently and may be restarted any number of
// times; they share the timestamp (ticket) store. Each invocation goes through
//   parse -> load -> decide -> auth [-> auth_pw] -> setup
//     run:  -> set_groups -> set_gid -> set_uid -> exec
//     edit: -> edit_prepare -> (editor helper) -> edit_write
// and may detour through a helper (mailer, askpass, editor) that must drop to
// the invoker's credentials before it is executed:
//   h_groups -> h_gid -> h_uid -> h_exec -> back to the caller's phase.
//
// The invoker is the adversary: it picks argv, environment (TZ, EDITOR), the
// contents of directories it can write (a chroot tree, its own process name
// shown in /proc/self/stat) and the interleaving of the two invocations.
// Kernel facts (real uid, session, real host, clock) are trusted.
module sudo {
  import types.* from "./types"
  import kernel.* from "./kernel"
  import policy.* from "./policy"

  // ---- parameters -------------------------------------------------------
  type Impl = {
    hostOpt: bool,     // `-h host` exists (C sudo); sudo-rs's `-h` is only --help
    chrootOpt: bool,   // `-R dir` / CHROOT exists (C sudo)
    mailer: bool,      // sends mail on denial / bad password (C sudo)
    timeWindows: bool, // NOTBEFORE / NOTAFTER rules (C sudo)
    sudoedit: bool,    // sudoedit / `sudo -e`
    askpass: bool,     // `-A`, SUDO_ASKPASS helper
  }
  const IMPL: Impl
  const BUGS: Set[str]

  pure val CVE_2026_35535 = "CVE-2026-35535" // mailer runs after unchecked set*id failure
  pure val CVE_2025_32463 = "CVE-2025-32463" // chroot before policy lookup (NSS from attacker dir)
  pure val CVE_2025_32462 = "CVE-2025-32462" // -h honoured outside list mode
  pure val CVE_2019_14287 = "CVE-2019-14287" // -u#-1 accepted, runs as uid 0
  pure val CVE_2026_96512 = "CVE-2026-96512" // TZ shifts NOTBEFORE/NOTAFTER evaluation
  pure val CVE_2023_22809 = "CVE-2023-22809" // EDITOR injects extra files into sudoedit
  pure val CVE_2025_64517 = "CVE-2025-64517" // sudo-rs: ticket records invoker under targetpw/rootpw
  pure val CVE_2023_42456 = "CVE-2023-42456" // sudo-rs: ticket path traversal via user name
  pure val PROC_STAT_SPLIT = "PROC-STAT-SPLIT" // no CVE: /proc/self/stat split on spaces

  def bug(id: str): bool = BUGS.contains(id)

  // Local time as the policy sees it: without time windows rules cannot
  // depend on time, so all instants look the same.
  def policyTime(t: int): int = if (IMPL.timeWindows) t else 0

  def tsFileOwner(u: int): int =
    if (bug(CVE_2023_42456)) tsPathOwnerByName(userName(u)) else u

  pure def userCreds(u: int): Creds = credsFor(u, primaryGid(u), suppGroups(u))

  // ---- state ------------------------------------------------------------
  type Proc = {
    phase: str,
    // trusted facts provided by the kernel
    invoker: int, session: int,
    // argv (attacker)
    mode: str, runasKind: str, runasArg: int, hasGroup: bool, groupArg: int,
    cmd: str, file: str, hostArg: str, chroot: bool, askpass: bool,
    // environment and user-writable data (attacker)
    tzOffset: int, editorExtra: Set[str], statSession: int,
    // derived by sudo
    nssFromChroot: bool, target: int, targetGid: int, sessionUsed: int,
    verdict: str, principal: int, decideNow: int, authAt: int, viaTicket: bool,
    creds: Creds, credFail: bool, pending: Set[str],
    // helper sub-machine
    helper: str, helperRet: str, hcreds: Creds, hcredFail: bool,
  }

  type TicketRec = { session: int, authUid: int, time: int }

  // ghost history
  type AuthEv = { invoker: int, session: int, principal: int, time: int }
  type ActEv = {
    kind: str,                 // "exec" or "write" (sudoedit write-back)
    invoker: int, session: int,
    req: Request,              // the request actually carried out, on trusted inputs
    argvFile: str,             // sudoedit: the file named on the command line
    creds: Creds, expected: Creds, target: int, authAt: int, viaTicket: bool, credFail: bool,
  }
  type HelperEv = { kind: str, invoker: int, creds: Creds, credFail: bool }
  type DecisionEv = {
    invoker: int, used: Request, trusted: Request, usedSession: int, trustedSession: int,
  }
  type Log = {
    acts: Set[ActEv], helpers: Set[HelperEv], decisions: Set[DecisionEv], auths: Set[AuthEv],
  }

  var procs: int -> Proc
  var tickets: int -> Set[TicketRec]   // timestamp file of each account
  var policy: Oracle
  var now: int
  var log: Log

  pure val TERMINAL = Set("idle", "done", "aborted")

  pure val IDLE: Proc = {
    phase: "idle", invoker: ROOT, session: 1,
    mode: "run", runasKind: "default", runasArg: ROOT, hasGroup: false, groupArg: 0,
    cmd: "c1", file: "f1", hostArg: "", chroot: false, askpass: false,
    tzOffset: 0, editorExtra: Set(), statSession: 1,
    nssFromChroot: false, target: ROOT, targetGid: 0, sessionUsed: 1,
    verdict: "deny", principal: ROOT, decideNow: 0, authAt: 0, viaTicket: false,
    creds: userCreds(ROOT), credFail: false, pending: Set(),
    helper: "none", helperRet: "aborted", hcreds: userCreds(ROOT), hcredFail: false,
  }

  pure def targetGroups(s: Proc): Set[int] =
    suppGroups(s.target).union(if (s.hasGroup) Set(s.groupArg) else Set())

  pure def startHelper(s: Proc, kind: str, ret: str): Proc =
    { ...s, phase: "h_groups", helper: kind, helperRet: ret, hcreds: s.creds, hcredFail: false }

  def modes: Set[str] = if (IMPL.sudoedit) Set("run", "edit", "list") else Set("run", "list")

  // Deny / bad password: mail the admins if the implementation does, then stop.
  def failPath(s: Proc): Proc =
    if (IMPL.mailer) startHelper(s, "mailer", "aborted") else { ...s, phase: "aborted" }

  action init = all {
    procs' = PIDS.mapBy(_ => IDLE),
    tickets' = USERS.mapBy(_ => Set()),
    policy' = Map(),
    now' = 0,
    log' = { acts: Set(), helpers: Set(), decisions: Set(), auths: Set() },
  }

  action setProc(p: int, s: Proc): bool = all {
    procs' = procs.set(p, s),
    tickets' = tickets,
    policy' = policy,
    now' = now,
    log' = log,
  }

  // ---- adversary starts an invocation ----------------------------------
  // Every nondeterministic action below is a thin wrapper that picks its
  // choices and passes them to a `...With` action. A replay of an observed
  // run (`replay.qnt`) calls the `...With` actions with the observed or
  // fixture-declared values instead, and each `...With` action only accepts
  // values the nondeterministic wrapper could have picked.
  type StartArgs = {
    invoker: int, session: int, mode: str, runasKind: str, runasArg: int,
    hasGroup: bool, groupArg: int, cmd: str, file: str, hostArg: str, chroot: bool,
    askpass: bool, tzOffset: int, editorExtra: Set[str], statSession: int,
  }

  def startAdmissible(a: StartArgs): bool = and {
    INVOKERS.contains(a.invoker),
    SESSIONS.contains(a.session),
    modes.contains(a.mode),
    Set("default", "name", "num").contains(a.runasKind),
    NUMERIC_UIDS.contains(a.runasArg),
    GIDS.contains(a.groupArg),
    COMMANDS.contains(a.cmd),
    FILES.contains(a.file),
    (if (IMPL.hostOpt) Set("", "h1", "h2") else Set("")).contains(a.hostArg),
    IMPL.chrootOpt or not(a.chroot),
    IMPL.askpass or not(a.askpass),
    TZ_OFFSETS.contains(a.tzOffset),
    a.editorExtra.subseteq(FILES),
    SESSIONS.contains(a.statSession),
  }

  action startWith(p: int, a: StartArgs): bool = all {
    TERMINAL.contains(procs.get(p).phase),
    startAdmissible(a),
    setProc(p, {
      ...IDLE,
      phase: "parse", invoker: a.invoker, session: a.session,
      mode: a.mode, runasKind: a.runasKind, runasArg: a.runasArg, hasGroup: a.hasGroup,
      groupArg: a.groupArg, cmd: a.cmd, file: a.file, hostArg: a.hostArg, chroot: a.chroot,
      askpass: a.askpass, tzOffset: a.tzOffset, editorExtra: a.editorExtra,
      statSession: a.statSession,
      creds: setuidRootExec(a.invoker, primaryGid(a.invoker), suppGroups(a.invoker)),
    }),
  }

  action start(p: int): bool = {
    nondet invoker = INVOKERS.oneOf()
    nondet session = SESSIONS.oneOf()
    nondet mode = modes.oneOf()
    nondet runasKind = Set("default", "name", "num").oneOf()
    nondet runasArg = NUMERIC_UIDS.oneOf()
    nondet hasGroup = Bool.oneOf()
    nondet groupArg = GIDS.oneOf()
    nondet cmd = COMMANDS.oneOf()
    nondet file = FILES.oneOf()
    nondet hostArg = (if (IMPL.hostOpt) Set("", "h1", "h2") else Set("")).oneOf()
    nondet chroot = (if (IMPL.chrootOpt) Bool else Set(false)).oneOf()
    nondet askpass = (if (IMPL.askpass) Bool else Set(false)).oneOf()
    nondet tzOffset = TZ_OFFSETS.oneOf()
    nondet editorExtra = FILES.powerset().oneOf()
    nondet statSession = SESSIONS.oneOf()
    startWith(p, {
      invoker: invoker, session: session, mode: mode, runasKind: runasKind,
      runasArg: runasArg, hasGroup: hasGroup, groupArg: groupArg, cmd: cmd, file: file,
      hostArg: hostArg, chroot: chroot, askpass: askpass, tzOffset: tzOffset,
      editorExtra: editorExtra, statSession: statSession,
    })
  }

  // ---- parse the command line ------------------------------------------
  action parse(p: int): bool = {
    val s = procs.get(p)
    val target = if (s.runasKind == "default") ROOT else s.runasArg
    // `-u#-1` / `-u#4294967295` is rejected (the fix of CVE-2019-14287).
    val badUid = s.runasKind == "num" and s.runasArg == UID_MINUS_ONE and not(bug(CVE_2019_14287))
    val unknownName = s.runasKind == "name" and not(USERS.contains(s.runasArg))
    // `-h` is only meaningful with `-l` (the fix of CVE-2025-32462).
    val hostMisuse = s.hostArg != "" and s.mode != "list" and not(bug(CVE_2025_32462))
    // The session is read from /proc/self/stat, whose comm field the invoker
    // controls; a parser splitting on spaces reads an attacker-chosen field.
    val sessionUsed = if (bug(PROC_STAT_SPLIT)) s.statSession else s.session
    all {
      s.phase == "parse",
      setProc(p, {
        ...s,
        phase: if (badUid or unknownName or hostMisuse) "aborted" else "load",
        target: target,
        targetGid: if (s.hasGroup) s.groupArg else primaryGid(target),
        sessionUsed: sessionUsed,
      }),
    }
  }

  // ---- load the policy and the name service configuration ---------------
  action load(p: int): bool = {
    val s = procs.get(p)
    all {
      s.phase == "load",
      // Correct order: chroot only right before exec. With the bug the
      // chroot happens now and nsswitch.conf/libnss come from the
      // attacker's tree.
      setProc(p, { ...s, phase: "decide", nssFromChroot: s.chroot and bug(CVE_2025_32463) }),
    }
  }

  // ---- policy decision ---------------------------------------------------
  // `fresh` is the verdict the policy oracle gives the request if it has not
  // been looked up before; `nssAnswer` is whatever an attacker-provided NSS
  // module answers for the invoker (used only with CVE-2025-32463).
  action decideWith(p: int, fresh: str, nssAnswer: int): bool = {
    val s = procs.get(p)
    val user = if (s.nssFromChroot) nssAnswer else s.invoker
    val host = if (s.hostArg != "" and (s.mode == "list" or bug(CVE_2025_32462))) s.hostArg else REAL_HOST
    val tz = if (bug(CVE_2026_96512)) s.tzOffset else 0
    val cmd = if (s.mode == "edit") editCmd(s.file) else s.cmd
    val req = {
      user: user, host: host, runasUid: s.target, runasGid: s.targetGid,
      cmd: cmd, time: policyTime(clampTime(now + tz)),
    }
    val trusted = { ...req, user: s.invoker, host: REAL_HOST, time: policyTime(now) }
    val v = consult(policy, req, fresh)
    val decided = { ...s, verdict: v, principal: authPrincipal(v, s.invoker, s.target), decideNow: now }
    all {
      s.phase == "decide",
      VERDICTS.contains(fresh),
      USERS.contains(nssAnswer),
      procs' = procs.set(p,
        if (s.mode == "list") { ...decided, phase: "done" }
        else if (v == "deny") failPath(decided)
        else { ...decided, phase: "auth" }),
      tickets' = tickets,
      policy' = policy.put(req, v),
      now' = now,
      // Listing grants nothing, so only run/edit decisions are recorded.
      log' = if (s.mode == "list") log else {
        ...log,
        decisions: log.decisions.union(Set({
          invoker: s.invoker, used: req, trusted: trusted,
          usedSession: s.sessionUsed, trustedSession: s.session,
        })),
      },
    }
  }

  action decide(p: int): bool = {
    nondet fresh = VERDICTS.oneOf()
    nondet nssAnswer = USERS.oneOf()
    decideWith(p, fresh, nssAnswer)
  }

  // ---- authentication ---------------------------------------------------
  def ticketValid(s: Proc): bool =
    tickets.get(tsFileOwner(s.invoker)).exists(r =>
      r.session == s.sessionUsed and r.authUid == s.principal
        and r.time <= now and now - r.time <= TIMEOUT)

  action auth(p: int): bool = {
    val s = procs.get(p)
    all {
      s.phase == "auth",
      setProc(p,
        if (not(needsAuth(s.verdict))) { ...s, phase: "setup", authAt: now }
        else if (ticketValid(s)) { ...s, phase: "setup", authAt: now, viaTicket: true }
        else if (s.askpass) startHelper(s, "askpass", "auth_pw")
        else { ...s, phase: "auth_pw" }),
    }
  }

  // The adversary may or may not know the principal's password.
  action authPw(p: int): bool = {
    val s = procs.get(p)
    nondet correct = Bool.oneOf()
    val owner = tsFileOwner(s.invoker)
    val authUid = if (bug(CVE_2025_64517)) s.invoker else s.principal
    all {
      s.phase == "auth_pw",
      procs' = procs.set(p, if (correct) { ...s, phase: "setup", authAt: now } else failPath(s)),
      tickets' = if (correct)
          tickets.set(owner, tickets.get(owner).union(Set({ session: s.sessionUsed, authUid: authUid, time: now })))
        else tickets,
      policy' = policy,
      now' = now,
      log' = if (correct)
          { ...log, auths: log.auths.union(Set({ invoker: s.invoker, session: s.session, principal: s.principal, time: now })) }
        else log,
    }
  }

  // ---- environment and credentials --------------------------------------
  action setup(p: int): bool = {
    val s = procs.get(p)
    all {
      s.phase == "setup",
      // Environment sanitising and (correctly placed) chroot happen here;
      // neither changes modelled data.
      setProc(p, { ...s, phase: if (s.mode == "edit") "edit_prepare" else "set_groups" }),
    }
  }

  // One credential step of the command path: failures always abort. `roll`
  // selects a fault (see `isFault`).
  action credStep(p: int, phase: str, nextPhase: str, call: (Creds, bool) => Result, roll: int): bool = {
    val s = procs.get(p)
    val r = call(s.creds, isFault(roll))
    all {
      s.phase == phase,
      FAULT_ROLLS.contains(roll),
      setProc(p,
        if (r.ok) { ...s, phase: nextPhase, creds: r.creds }
        else { ...s, phase: "aborted", credFail: true }),
    }
  }

  action setGroupsWith(p: int, roll: int): bool = {
    val s = procs.get(p)
    credStep(p, "set_groups", "set_gid", (c, f) => setgroups(c, targetGroups(s), f), roll)
  }

  action setGroups(p: int): bool = {
    nondet roll = FAULT_ROLLS.oneOf()
    setGroupsWith(p, roll)
  }

  action setGidWith(p: int, roll: int): bool = {
    val s = procs.get(p)
    credStep(p, "set_gid", "set_uid", (c, f) => setresgid(c, s.targetGid, s.targetGid, s.targetGid, f), roll)
  }

  action setGid(p: int): bool = {
    nondet roll = FAULT_ROLLS.oneOf()
    setGidWith(p, roll)
  }

  action setUidWith(p: int, roll: int): bool = {
    val s = procs.get(p)
    credStep(p, "set_uid", "exec", (c, f) => setresuid(c, s.target, s.target, s.target, f), roll)
  }

  action setUid(p: int): bool = {
    nondet roll = FAULT_ROLLS.oneOf()
    setUidWith(p, roll)
  }

  // `fresh` is the verdict of the request actually carried out if the
  // policy has not seen it (a ghost lookup).
  action execWith(p: int, fresh: str): bool = {
    val s = procs.get(p)
    // What actually runs: the effective identity and the real invoker, host
    // and decision time.
    val real = {
      user: s.invoker, host: REAL_HOST, runasUid: s.creds.euid, runasGid: s.creds.egid,
      cmd: s.cmd, time: policyTime(s.decideNow),
    }
    val ev = {
      kind: "exec", invoker: s.invoker, session: s.session, req: real, argvFile: "",
      creds: s.creds, expected: credsFor(s.target, s.targetGid, targetGroups(s)),
      target: s.target, authAt: s.authAt, viaTicket: s.viaTicket, credFail: s.credFail,
    }
    all {
      s.phase == "exec",
      VERDICTS.contains(fresh),
      procs' = procs.set(p, { ...s, phase: "done" }),
      tickets' = tickets,
      policy' = remember(policy, real, fresh),
      now' = now,
      log' = { ...log, acts: log.acts.union(Set(ev)) },
    }
  }

  action exec(p: int): bool = {
    nondet fresh = VERDICTS.oneOf()
    execWith(p, fresh)
  }

  // ---- sudoedit ----------------------------------------------------------
  action editPrepare(p: int): bool = {
    val s = procs.get(p)
    // EDITOR="vi -- f2": the fixed versions refuse such an editor and use a
    // default one, so only the file named in argv is edited.
    val files = Set(s.file).union(if (bug(CVE_2023_22809)) s.editorExtra else Set())
    all {
      s.phase == "edit_prepare",
      setProc(p, startHelper({ ...s, pending: files }, "editor", "edit_write")),
    }
  }

  action editWrite(p: int): bool = {
    val s = procs.get(p)
    nondet f = FILES.oneOf()
    nondet fresh = VERDICTS.oneOf()
    val real = {
      user: s.invoker, host: REAL_HOST, runasUid: s.target, runasGid: s.targetGid,
      cmd: editCmd(f), time: policyTime(s.decideNow),
    }
    val ev = {
      kind: "write", invoker: s.invoker, session: s.session, req: real, argvFile: s.file,
      creds: s.creds, expected: s.creds, target: s.target, authAt: s.authAt,
      viaTicket: s.viaTicket, credFail: s.credFail,
    }
    val rest = s.pending.exclude(Set(f))
    all {
      s.phase == "edit_write",
      s.pending.contains(f),
      procs' = procs.set(p, { ...s, pending: rest, phase: if (rest == Set()) "done" else "edit_write" }),
      tickets' = tickets,
      policy' = remember(policy, real, fresh),
      now' = now,
      log' = { ...log, acts: log.acts.union(Set(ev)) },
    }
  }

  // ---- helpers (mailer, askpass, editor) --------------------------------
  // A helper drops to the invoker's credentials. A failed call aborts the
  // whole invocation, except with CVE-2026-35535 where the mailer path
  // ignores the result and carries on.
  action helperStep(p: int, phase: str, nextPhase: str, call: (Creds, bool) => Result): bool = {
    val s = procs.get(p)
    nondet roll = FAULT_ROLLS.oneOf()
    val r = call(s.hcreds, isFault(roll))
    val unchecked = bug(CVE_2026_35535) and s.helper == "mailer"
    all {
      s.phase == phase,
      setProc(p,
        if (r.ok) { ...s, phase: nextPhase, hcreds: r.creds }
        else if (unchecked) { ...s, phase: nextPhase, hcredFail: true }
        else { ...s, phase: "aborted", credFail: true }),
    }
  }

  action hGroups(p: int): bool = {
    val s = procs.get(p)
    helperStep(p, "h_groups", "h_gid", (c, f) => setgroups(c, suppGroups(s.invoker), f))
  }

  action hGid(p: int): bool = {
    val s = procs.get(p)
    val g = primaryGid(s.invoker)
    helperStep(p, "h_gid", "h_uid", (c, f) => setresgid(c, g, g, g, f))
  }

  action hUid(p: int): bool = {
    val s = procs.get(p)
    val u = s.invoker
    helperStep(p, "h_uid", "h_exec", (c, f) => setresuid(c, u, u, u, f))
  }

  action hExec(p: int): bool = {
    val s = procs.get(p)
    all {
      s.phase == "h_exec",
      procs' = procs.set(p, { ...s, phase: s.helperRet, helper: "none", hcredFail: false }),
      tickets' = tickets,
      policy' = policy,
      now' = now,
      log' = { ...log, helpers: log.helpers.union(Set({
        kind: s.helper, invoker: s.invoker, creds: s.hcreds, credFail: s.hcredFail,
      })) },
    }
  }

  // ---- time --------------------------------------------------------------
  action tick: bool = all {
    now < MAX_TIME,
    now' = now + 1,
    procs' = procs,
    tickets' = tickets,
    policy' = policy,
    log' = log,
  }

  // Advance invocation `p` by the one action its phase enables. Dispatching
  // on the phase (instead of offering every action) keeps the simulator from
  // searching the nondeterministic choices of disabled actions.
  action advance(p: int): bool = {
    val ph = procs.get(p).phase
    if (TERMINAL.contains(ph)) start(p)
    else if (ph == "parse") parse(p)
    else if (ph == "load") load(p)
    else if (ph == "decide") decide(p)
    else if (ph == "auth") auth(p)
    else if (ph == "auth_pw") authPw(p)
    else if (ph == "setup") setup(p)
    else if (ph == "set_groups") setGroups(p)
    else if (ph == "set_gid") setGid(p)
    else if (ph == "set_uid") setUid(p)
    else if (ph == "exec") exec(p)
    else if (ph == "edit_prepare") editPrepare(p)
    else if (ph == "edit_write") editWrite(p)
    else if (ph == "h_groups") hGroups(p)
    else if (ph == "h_gid") hGid(p)
    else if (ph == "h_uid") hUid(p)
    else hExec(p)
  }

  action step = any {
    nondet p = PIDS.oneOf()
    advance(p),
    tick,
  }

  // ---- invariants --------------------------------------------------------
  val execs = log.acts.filter(e => e.kind == "exec")
  val writes = log.acts.filter(e => e.kind == "write")

  // 1. Complete mediation: every command exec was allowed by the policy for
  //    the real invoker, on the real host, at the real decision time, for the
  //    identity it actually runs as.
  val inv1_completeMediation =
    execs.forall(e => permits(policy, e.req))

  // 2a. Every privileged action not waived by the rule follows a fresh
  //     password check of the right principal in the same session.
  val authBeforeAct =
    log.acts.forall(e => {
      val v = if (policy.keys().contains(e.req)) policy.get(e.req) else "deny"
      val who = authPrincipal(v, e.invoker, e.req.runasUid)
      not(needsAuth(v)) or log.auths.exists(a =>
        a.invoker == e.invoker and a.session == e.session and a.principal == who
          and a.time <= e.authAt and e.authAt - a.time <= TIMEOUT)
    })

  // 2b. Every ticket in a user's file stems from a password check by that
  //     user, in that session, of the principal recorded in the ticket.
  val ticketBinding =
    tickets.keys().forall(o => tickets.get(o).forall(r =>
      log.auths.exists(a =>
        a.invoker == o and a.session == r.session and a.principal == r.authUid and a.time == r.time)))

  val inv2_authentication = authBeforeAct and ticketBinding

  // 3. Exact credentials at exec, and no residual root uid unless the target
  //    is root.
  val inv3_exactCredentials =
    execs.forall(e => e.creds == e.expected and (e.target != ROOT implies not(anyRootUid(e.creds))))

  // 4a. Helpers run with exactly the invoker's credentials (hence no root).
  val helpersUnprivileged =
    log.helpers.forall(h => h.creds == userCreds(h.invoker) and not(holdsRoot(h.creds)))

  // 4b. Nothing is executed after a failed credential call.
  val failedCredAborts =
    log.helpers.forall(h => not(h.credFail)) and log.acts.forall(e => not(e.credFail))

  val inv4_helperIsolation = helpersUnprivileged and failedCredAborts

  // 5. The decision is evaluated on trusted inputs only: real invoker
  //    identity (not an attacker NSS answer), real host (not `-h`), real
  //    time (not TZ-shifted), kernel session (not parsed attacker text).
  val inv5_trustedInputs =
    log.decisions.forall(d => d.used == d.trusted and d.usedSession == d.trustedSession)

  // 6. sudoedit writes back only the file named on the command line, and only
  //    when the policy allows editing it.
  val inv6_sudoeditFiles =
    writes.forall(w => w.req.cmd == editCmd(w.argvFile) and permits(policy, w.req))

  val allInvariants = and {
    inv1_completeMediation, inv2_authentication, inv3_exactCredentials,
    inv4_helperIsolation, inv5_trustedInputs, inv6_sudoeditFiles,
  }

  // ---- witnesses: the clean model reaches the interesting situations ------
  val witnessExec = execs.size() > 0
  val witnessExecAsOther = execs.exists(e => e.target != ROOT)
  val witnessTicketReuse = log.acts.exists(e => e.viaTicket)
  val witnessSudoeditWrite = writes.size() > 0
  val witnessMailer = log.helpers.exists(h => h.kind == "mailer")
  val witnessAskpass = log.helpers.exists(h => h.kind == "askpass")
  val witnessEditor = log.helpers.exists(h => h.kind == "editor")
  val witnessCredFailure = PIDS.exists(p => procs.get(p).credFail)
  val witnessConcurrent = PIDS.forall(p => not(TERMINAL.contains(procs.get(p).phase)))
}
