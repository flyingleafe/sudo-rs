// -*- mode: Bluespec; -*-
// Replay of one observed sudo-rs invocation through the clean sudo-rs model.
//
// `observe/observe.py replay` derives an `Observed` record from a capture of
// the real binary (README.md, section "Observed traces") and runs
// `replayExec` or `replayRefused` on it as a Quint test. Every choice the
// model would make nondeterministically comes from one of three sources,
// never from the observed outcome:
//   * observed: argv, environment, invoker, launch credentials, the result of
//     each credential call of the command process (so the fault roll is the
//     observed success), the executed command and its credentials, the
//     timestamp files;
//   * pinned by the committed fixture before the run: the policy verdict of
//     the request (`verdict`, from observe/fixture/scenarios);
//   * fixed because unobservable here and without effect in the clean model:
//     the session and the /proc/self/stat session, the NSS answer (sudo-rs
//     has no chroot).
// The replay rejects the observation when the model cannot take a step from
// these values, or when a model state differs from the observation it is
// compared with (`expect`).
module replay {
  import types.* from "./types"
  import kernel.* from "./kernel"
  // Same feature set as `sudors` in instances.qnt.
  import sudo(
    IMPL = { hostOpt: false, chrootOpt: false, mailer: false, timeWindows: false, sudoedit: true, askpass: true },
    BUGS = Set()
  ).* from "./sudo"

  // Arguments of the three credential calls of the command process
  // (setgroups, setgid, setuid in sudo-rs; setgid/setuid as root set all
  // three ids, i.e. setresgid(g,g,g) / setresuid(u,u,u) in the model).
  type CredCalls = { groups: Set[int], gid: int, uid: int }

  type Observed = {
    start: StartArgs,       // argv and environment of the invocation
    startCreds: Creds,      // credentials sudo was started with
    verdict: str,           // fixture-pinned verdict of the decided request
    outcome: str,           // "exec" or "refused"
    calls: CredCalls,       // exec only: credential calls of the command process
    execCreds: Creds,       // exec only: credentials of the executed command
    execCmd: str,           // exec only: the executed command
    ticketOwners: Set[int], // accounts with a timestamp record after the run
  }

  pure val PID = 1
  // A successful credential call (`isFault(1)` is false). Observed calls
  // that fail are rejected before a replay is attempted.
  pure val NO_FAULT = 1
  // Ghost verdict of a request that was never decided: counts as denied, so
  // executing an undecided request breaks inv1.
  pure val UNDECIDED = "deny"

  def ticketsMatch(o: Observed): bool =
    USERS.forall(u => (tickets.get(u) != Set()) iff o.ticketOwners.contains(u))

  def callsMatch(o: Observed): bool = {
    val s = procs.get(PID)
    and {
      s.phase == "set_groups",
      targetGroups(s) == o.calls.groups,
      s.targetGid == o.calls.gid,
      s.target == o.calls.uid,
    }
  }

  def execMatches(o: Observed): bool = and {
    o.outcome == "exec",
    procs.get(PID).phase == "done",
    log.helpers == Set(),
    execs.size() == 1,
    execs.forall(e => and {
      e.invoker == o.start.invoker,
      e.req.cmd == o.execCmd,
      e.creds == o.execCreds,
      not(e.credFail),
    }),
    ticketsMatch(o),
  }

  def refusalMatches(o: Observed): bool = and {
    o.outcome == "refused",
    procs.get(PID).phase == "aborted",
    not(procs.get(PID).credFail),
    log.acts == Set(),
    log.helpers == Set(),
    log.auths == Set(),
    ticketsMatch(o),
  }

  // A permitted run: decision, no password check (the verdict must waive
  // it, otherwise `setup` is not enabled), three credential calls, exec.
  run replayExec(o: Observed): bool =
    init
      .then(startWith(PID, o.start))
      .expect(procs.get(PID).creds == o.startCreds)
      .then(parse(PID))
      .then(load(PID))
      .then(decideWith(PID, o.verdict, o.start.invoker))
      .then(auth(PID))
      .then(setup(PID))
      .expect(callsMatch(o))
      .then(setGroupsWith(PID, NO_FAULT))
      .then(setGidWith(PID, NO_FAULT))
      .then(setUidWith(PID, NO_FAULT))
      .then(execWith(PID, UNDECIDED))
      .expect(execMatches(o) and allInvariants)

  // A refused run: the decision ends the invocation (sudo-rs has no mailer).
  run replayRefused(o: Observed): bool =
    init
      .then(startWith(PID, o.start))
      .expect(procs.get(PID).creds == o.startCreds)
      .then(parse(PID))
      .then(load(PID))
      .then(decideWith(PID, o.verdict, o.start.invoker))
      .expect(refusalMatches(o) and allInvariants)
}
