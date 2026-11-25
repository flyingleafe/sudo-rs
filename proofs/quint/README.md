# Quint model of the sudo invocation lifecycle

This directory has an implementation-independent Quint model of a sudo invocation, from command line to `execve`.
Original C sudo ("ogsudo") and sudo-rs are both instances of it, selected by feature flags.
The invoker is the adversary.
The model has one switchable mutant per historical bug, and `check.sh` confirms that each mutant breaks its invariant.

The Lean/Aeneas work in `proofs/lean` covers the policy decision (`check_permission`).
This model covers everything around it: credentials, authentication, tickets, helpers and exec.
Here the policy is an arbitrary relation, so the model's results hold whatever the decision procedure computes.

## Files

| File | Contents |
|---|---|
| `types.qnt` | Finite universe: accounts (root, alice, bob, and `evil`, whose name is `../ts/bob`), hosts, commands, sudoedit files, sessions, clock |
| `kernel.qnt` | Linux credentials (real/effective/saved uid and gid, supplementary groups) and `setresuid` / `setresgid` / `setgroups`, including failure |
| `policy.qnt` | The policy as a lazily fixed nondeterministic oracle `Request -> Verdict` |
| `sudo.qnt` | Lifecycle state machine, parameterised by `IMPL` (features) and `BUGS` (mutants); invariants; coverage witnesses |
| `instances.qnt` | `ogsudo`, `sudors`, and one `mut_*` module per mutant |
| `check.sh` | Typecheck, clean-model checks, mutant checks, observed-trace replay |
| `traces/` | ITF counterexample of every mutant, written by `check.sh` |
| `replay.qnt` | Replay of one observed sudo-rs run through the clean sudo-rs model (see [Observed traces](#observed-traces)) |
| `observe/` | Guest capture script, fixture, recorder and replay driver for observed runs of the real binary |

## Model

**Processes.**
Two invocation slots run concurrently. Each slot restarts after it finishes, and both share the timestamp store.
Each invocation goes through these phases:

```
parse -> load -> decide -> auth [-> auth_pw] -> setup
   run:  -> set_groups -> set_gid -> set_uid -> exec
   edit: -> edit_prepare -> (editor helper) -> edit_write (one step per file)
deny / bad password -> (mailer helper, if the implementation mails) -> aborted
```

A helper (mailer, askpass, sudoedit's editor) is forked from sudo's credentials and runs `h_groups -> h_gid -> h_uid -> h_exec`.
It drops to the invoker's groups, gid and uid, then returns to the phase that called it.

**Kernel.**
The kernel semantics follow Chen, Wagner and Dean, *Setuid Demystified* (2002), for Linux:
- A process holds CAP_SETUID/CAP_SETGID iff its euid is 0.
- Unprivileged `setres[ug]id` may only permute the current ids.
- `setgroups` needs privilege.
- An id argument of `-1` means "unchanged".
- A permitted call can still fail (ENOMEM, LSM/seccomp, RLIMIT_NPROC on old kernels); a failed call changes nothing.

sudo starts with the credentials of a setuid-root exec: `ruid = invoker, euid = suid = 0`, with the invoker's gids and groups.

**Policy.**
The policy is a total function from `(user, host, runas uid, runas gid, command, time)` to `deny | nopasswd | passwd | targetpw | rootpw`.
The model never fixes this function. The first time a request is looked up, its verdict is chosen nondeterministically and then remembered.
Each run therefore follows one fixed policy, and the set of runs covers every policy over the finite universe.
Ghost lookups at exec and write time also fix the verdict of the request that is *actually* carried out, so the invariants can compare it with the request that was decided.
Without time windows (sudo-rs), the policy cannot depend on time.

**Adversary.**
The invoker chooses all of the following:
- the account (alice, bob or evil) and the session it runs in;
- argv: mode (`run`, `-e`, `-l`), `-u name` or `-u#N` (including `#-1`), `-g`, command, file, `-h host`, `-R dir`, `-A`;
- environment: `TZ` (a local-time offset) and `EDITOR` (extra files after `--`);
- the contents of user-writable data: the chroot tree, which supplies the NSS answers if sudo reads them there, and its own process name in `/proc/self/stat`;
- whether it knows the password asked for;
- the interleaving of the two invocations and the clock ticks.

Kernel facts (real uid, session, real host, clock) are trusted.

## Invariants

All invariants are `val`s in `sudo.qnt`. Conjunctions also have named components.

| # | Name | Statement |
|---|---|---|
| 1 | `inv1_completeMediation` | Every command exec was allowed by the policy for the real invoker, on the real host, at the real decision time, for the uid/gid it actually runs as. |
| 2 | `inv2_authentication` = `authBeforeAct` ∧ `ticketBinding` | Every exec or sudoedit write whose rule is not NOPASSWD follows a password check, at most `TIMEOUT` old, by the right principal (invoker; target for targetpw; root for rootpw) in the same session. Every ticket stored in user *u*'s file comes from a password check by *u*, in the recorded session, of the recorded principal. |
| 3 | `inv3_exactCredentials` | At exec, all three uids and gids and the group list equal the target's; no uid is 0 unless the target is root. |
| 4 | `inv4_helperIsolation` = `helpersUnprivileged` ∧ `failedCredAborts` | Every helper runs with exactly the invoker's credentials (hence no root uid, gid or group). Nothing (helper or command) is executed after a failed credential call. |
| 5 | `inv5_trustedInputs` | Each run/edit decision is evaluated on the real invoker identity (not an NSS answer from an attacker tree), the real host (not `-h`), the real time (not shifted by TZ) and the kernel's session (not parsed from attacker text). |
| 6 | `inv6_sudoeditFiles` | sudoedit writes back only the file named on the command line, and only if the policy allows editing it. |

`allInvariants` is the conjunction of all six.

The `witness*` vals are coverage probes. `check.sh` requires each one to be reached in the clean runs, so that no invariant passes vacuously:
- exec as root and as another user;
- ticket reuse;
- sudoedit write;
- mailer, askpass and editor helpers;
- credential-call failure;
- two invocations in flight at once.

## Implementations

| Feature (`IMPL` field) | C sudo (`ogsudo`) | sudo-rs (`sudors`) |
|---|---|---|
| `-h host` (`hostOpt`) | yes | no (`-h` is `--help`) |
| `-R dir` / `CHROOT` (`chrootOpt`) | yes | no (`CHROOT` in sudoers is a parse error) |
| mail on deny / bad password (`mailer`) | yes | no (`mailerpath` ignored) |
| `NOTBEFORE` / `NOTAFTER` (`timeWindows`) | yes | no (parse error, "not supported") |
| sudoedit (`sudoedit`) | yes | yes |
| askpass `-A` (`askpass`) | yes | yes |

sudo-rs also lacks `TIMEOUT`, `INTERCEPT`, mail options and other features outside this model's scope.
The table only lists what the model uses.
The sudo-rs column was checked against this tree (`src/sudo/cli/mod.rs`, `src/sudoers/ast.rs`, `src/defaults/mod.rs`).

## Mutants

Each mutant is the matching clean implementation plus one bug flag.
`check.sh` asserts the invariant in the "Expected" column.
The last column lists every invariant (component) that random simulation broke for that mutant: 100 000 runs × 60 steps per invariant, outside `check.sh`.

| Bug | Base | Module | Bug as modelled | Expected | All broken |
|---|---|---|---|---|---|
| CVE-2026-35535 | C sudo | `mut_cve_2026_35535` | the mailer helper ignores a failed `setgroups`/`setresgid`/`setresuid` and is executed anyway | `inv4_helperIsolation` | 4 (`helpersUnprivileged`, `failedCredAborts`) |
| CVE-2025-32463 | C sudo | `mut_cve_2025_32463` | `-R dir` chroots before the policy lookup, so the invoker identity comes from the attacker tree's NSS | `inv5_trustedInputs` | 1, 2 (`authBeforeAct`), 5, 6 |
| CVE-2025-32462 | C sudo | `mut_cve_2025_32462` | `-h host` is accepted outside `-l` and used as the decision host | `inv1_completeMediation` | 1, 2 (`authBeforeAct`), 5, 6 |
| CVE-2019-14287 | C sudo | `mut_cve_2019_14287` | `-u#-1` is accepted; `setresuid(-1,-1,-1)` leaves uid 0 | `inv3_exactCredentials` | 1, 2 (`authBeforeAct`), 3 |
| CVE-2026-96512 | C sudo | `mut_cve_2026_96512` | NOTBEFORE/NOTAFTER are evaluated at the TZ-shifted local time | `inv5_trustedInputs` | 1, 2 (`authBeforeAct`), 5, 6 |
| CVE-2023-22809 | C sudo | `mut_cve_2023_22809` | files after `--` in `EDITOR` join the edited set after the policy check | `inv6_sudoeditFiles` | 2 (`authBeforeAct`), 6 |
| CVE-2025-64517 | sudo-rs | `mut_cve_2025_64517` | under targetpw/rootpw the ticket records the invoker, not the authenticated uid | `inv2_authentication` | 2 (`authBeforeAct`, `ticketBinding`) |
| CVE-2023-42456 | sudo-rs | `mut_cve_2023_42456` | the ticket path is `<dir>/<user name>`, and evil's name `../ts/bob` lands in bob's file | `inv2_authentication` | 2 (`authBeforeAct`, `ticketBinding`) |
| none (illustrative) | sudo-rs | `mut_proc_stat_split` | `/proc/self/stat` is split on spaces, so the invoker's process name chooses the session id | `inv5_trustedInputs` | 2 (`authBeforeAct`, `ticketBinding`), 5 |

CVE-2026-35535 and CVE-2026-96512 are modelled from the one-line descriptions in the task. The model has no further source for them.

## Running

```
cd proofs/quint
nix shell nixpkgs#quint nixpkgs#jdk -c ./check.sh
```

The output has:
- one `PASS` line per module typecheck;
- one `PASS <impl> <invariant> (simulation)` line per invariant and implementation;
- witness counts;
- with `VERIFY_STEPS=N`, one `PASS ... (apalache, N steps)` line per invariant and implementation;
- one `VIOLATED <invariant> by <mutant> (<bug>)` line per mutant;
- the observed-trace stage: `PASS harness expectation …` and `CONTROL harness rejected as required: …` lines, then per recorded observation `ACCEPTED <file> <scenario>` and `CONTROL raw|model rejected as required: …` lines (or `SKIP no recorded observation`).

The script exits non-zero on any unexpected outcome. That includes a mutant that is not caught, a clean-model violation, an unreached witness, a typecheck error, a rejected observation and an accepted negative control.
It needs `python3` (3.9 or later) for the observed-trace stage.

Budgets (environment variables):

| Variable | Default | Meaning |
|---|---|---|
| `SAMPLES` | 100000 | random runs per clean model |
| `STEPS` | 60 | steps per random run (clean and mutants) |
| `MUTANT_SAMPLES` | 100000 | maximum runs per mutant; the search stops at the first violation |
| `VERIFY_STEPS` | 0 (off) | Apalache bound for `quint verify --invariant=allInvariants` on both clean models |
| `SEED` | 0x5ad0 | simulator seed |

Measured cost on this machine (under load from other jobs): `check.sh` with defaults took 5.5 min in total.

Apalache (0.56.1, downloaded by `quint verify`) works here but is slow on this state space, so it is opt-in. Measured times for `allInvariants`, all without violations:

| Model | Steps | Time |
|---|---|---|
| `ogsudo` | 4 | 20 s |
| `ogsudo` | 8 | 7.5 min |
| `sudors` | 10 | 19 min |

An exec needs at least 10 steps (`start` … `exec` on the NOPASSWD path), and a sudoedit write needs 12. The mailer path takes 8 steps.
So depth 8 covers decisions (inv5) and helper credentials (inv4), and depth 10 is the first depth that reaches a command exec (inv1, inv3).
Two-invocation ticket attacks need about 20 steps, which is out of Apalache's reach here; random simulation covers them.

Single checks:

```
quint run    --main=sudors instances.qnt --invariant=inv2_authentication --max-steps=60
quint run    --main=mut_cve_2025_64517 instances.qnt --invariant=inv2_authentication --out-itf=t.itf.json
quint verify --main=ogsudo instances.qnt --invariant=allInvariants --max-steps=8
```

## Abstractions and limits

- **Bounded, finite universe.**
  - 4 accounts, 2 hosts, 2 commands, 2 editable files, 2 sessions, 3 clock ticks, and 2 concurrent invocations (restartable).
  - Random simulation is not exhaustive.
  - Apalache is exhaustive only up to `VERIFY_STEPS` transitions.
  - Neither result is a proof for unbounded runs.
- **Policy content is abstract.** The sudoers language, aliases, `Defaults` and matching are not modelled; `proofs/lean` covers them. Each rule carries only its authentication tag (`targetpw`/`rootpw` are per-request verdicts here, not global Defaults).
- **NSS.** Only the invoker's identity can be falsified by an attacker NSS. Runas name resolution always uses the system database. The code-execution aspect of CVE-2025-32463 (loading attacker `libnss_*.so` as root) is represented by the attacker choosing the lookup answer.
- **Credentials.**
  - Privilege is euid 0. File capabilities, user namespaces, securebits and fsuid are not modelled.
  - Supplementary groups are one group per account, plus `-g`.
  - Unknown uids (only reachable through the CVE-2019-14287 mutant) have gid = uid and no groups.
  - sudo's own `PERM_ROOT` switch (`setresuid(0,0,0)` early on) is not modelled; with CVE-2019-14287 the command therefore runs with `ruid = invoker, euid = suid = 0` instead of all-zero. Both break invariant 3.
- **Authentication.** A password check is a nondeterministic success or failure (the attacker may or may not know the secret). PAM stacks, lockout, `-k`/`-K`, `timestamp_type`, and ticket expiry other than a fixed `TIMEOUT` are not modelled.
- **Tickets.**
  - A ticket is `(session, auth uid, time)` in a per-account file.
  - The session stands for sudo-rs's `RecordScope` (tty + session leader + start time) and for C sudo's tty/ppid records.
  - File-system races on the ticket file itself are not modelled; only interleavings of whole steps are.
- **Environment.** Only `TZ` and `EDITOR` are modelled. Environment sanitising and the placement of a legitimate chroot are a no-op `setup` step.
- **sudoedit.**
  - The temporary copies, ownership checks, symlink handling and the write-back credentials are not modelled; only which files are written back.
  - The editor runs as a helper with the invoker's credentials.
- **Helpers.** The mailer drops to the invoker's credentials (the task's specification). Real C sudo releases may run the mailer as a configured user; any unprivileged identity gives the same result.
- **Clean model = fixed behaviour.** `-u#-1` is rejected. `-h` outside `-l` is rejected. The chroot happens after the decision. TZ is ignored for time windows. `EDITOR` extra files are dropped. Tickets record the authenticated uid. Ticket files are named by uid. The session comes from a correct parse.

## Observed traces

The model is checked against runs of the real sudo-rs binary: one ordinary permitted command and one ordinary refusal.
An observation is replayed through the clean `sudors` model step by step (`replay.qnt`); the replay rejects it if the model cannot take a step or ends in a state that differs from what was observed.
The policy verdict of each request is pinned by the committed fixture before any run, so the replay cannot fit an arbitrary trace by choosing the verdict afterwards.
Evidence kind: test, for the two recorded runs only.

No observation is committed yet: the capture needs the disposable guest described below, which the coordinator runs. Until then `check.sh` runs only the harness self-test (fixture expectations, labelled as such, never stored as observations).

### What runs

| Item | Value |
|---|---|
| Fixture | `observe/fixture/`: `sudoers` with the single rule `ferris ALL=(another_user) NOPASSWD: /usr/bin/cat /proc/self/status`; `pam.d-sudo` = `STOCK_PAM_D_SUDO` of `test-framework/sudo-test` (checked); `scenarios` |
| Scenarios | `permitted`: `sudo -n -u another_user /usr/bin/cat /proc/self/status`, pinned verdict `nopasswd`. `refused`: `sudo -n -u another_user /usr/bin/id`, pinned verdict `deny`. Invoker `ferris`; no request targets root. User names follow the compliance framework (`USERNAME`, `another_user` of `flag_user::user_can_become_another_user`) |
| Binary | `cargo build --locked --offline --bin sudo` (debug, default features) of `git archive <commit>`, built in the guest by an unprivileged account, installed `root:root 0755` without the setuid bit |
| Launch | The guest administrator starts the binary as `env -i PATH=/usr/bin:/bin setpriv --ruid=<ferris> --euid=0 --rgid=<ferris> --egid=<ferris> --init-groups -- <sudo> <argv>`: real uid/gid ferris, effective and saved uid 0, ferris's groups, i.e. the credentials of a setuid-root exec by ferris (`setuidRootExec` in `kernel.qnt`), without a setuid file |
| Recording | `strace -f -qq -e signal=none -e trace=execve,fork,vfork,clone,clone3,setgroups,setuid,setgid,setreuid,setregid,setresuid,setresgid` (passive, no injection); stdout, stderr, exit status; `/var/run/sudo-rs/ts` before and after; the launcher's own credentials as a control (`setpriv … -- cat /proc/self/status`) |
| Guest | Disposable Debian 13 VM under KVM, no network, no sudo package; the script refuses (exit 3, `out/REFUSED`) on a host without the hypervisor CPU flag, with an existing sudoers, a setuid sudo, or existing fixture accounts |

### Pipeline

```
observe/prepare-input.sh <commit> <in>      # host, unprivileged: src.tar, crates checked against Cargo.lock, fixture
guest-run <in> <out> 900 -- sh /fixture/guest-run.sh /fixture /out    # inside the disposable guest
observe/observe.py record <out>/out <file>.obs.json                    # host, unprivileged, read-only on the capture
observe/observe.py replay <file>.obs.json                              # quint test per scenario
observe/observe.py controls <file>.obs.json                            # negative controls
```

`observe/cluster-job.sh` runs all of it as one `omnirun` job on `uni-cpu` (needs `GUEST_RUN`, `/dev/kvm`, `npm` for quint 0.33.0).
Recorded observations go to `observe/observations/<name>.obs.json`; `check.sh` replays each one and runs its controls.

An observation file holds the raw capture verbatim (except the binary, kept as its hash), the provenance and the derived facts.
`replay` derives the facts again from the raw capture and rejects the file if they differ from the stored ones; the model only ever sees the re-derived facts and the committed fixture.

### Observed, pinned, unobserved

| Model element | Status | Source |
|---|---|---|
| `start`: invoker, argv | observed | strace `execve` of sudo; launcher control |
| `start`: credentials | observed | the launcher's set*id calls traced up to the exec of sudo, equal to the launcher control |
| `start`: `TZ`, `EDITOR` | observed | fixed environment `env -i PATH=/usr/bin:/bin` |
| `start`: session, `/proc/self/stat` session | fixed (1) | not observable here; neither run reads or writes a ticket |
| `parse`, `load`, `setup` | unobserved | internal to sudo |
| `decide`: verdict | pinned | `observe/fixture/scenarios`, before the run; derived by hand from the one sudoers rule, not by `text_to_authorization` |
| `decide`: user, host, time of the request | unobserved | internal to sudo |
| `auth`: no password check | follows from the pinned verdict | with `-n`, a required password ends the run with "interactive authentication is required"; observed: exit 0, empty stderr |
| PAM library calls (`pam_start`, account management, session open/close, setcred) | unobserved, not modelled | no PAM event is synthesised; in the refusal sudo-rs stops before PAM (code reading: `src/sudo/pipeline.rs`, `run`) |
| PAM account helper (`/usr/sbin/unix_chkpwd`) | observed, not modelled | permitted run only: pam_unix's account management runs it; acceptance rule below |
| `set_groups`, `set_gid`, `set_uid` | observed | strace: arguments and results in the command process; must be exactly `setgroups`, `setgid`, `setuid`, all successful, from the launch credentials |
| `exec`: program and arguments | observed | strace `execve`; `Name` in the command's `/proc/self/status` |
| `exec`: credentials | observed | the command's `/proc/self/status`, equal to the credentials traced at its exec |
| refusal | observed | exit 1, `sudo: I'm sorry ferris. I'm afraid I can't do that`, no `execve` after sudo, no lasting credential change |
| sudo's helpers (mailer, askpass, editor) | observed | none: no program executed besides the command and the classified PAM helper |
| tickets | observed | timestamp directory empty before the run (the model starts without tickets) and listed after it |
| temporary credential switches of sudo itself | observed, not modelled | `sudo_call` switches to the target to resolve the command; accepted only if every sudo process ends at its launch credentials |
| fsuid/fsgid, `CapEff`, `NoNewPrivs` of the command | observed, not modelled | recorded in the observation |

Concrete ids map to `types.qnt` by account: root → `ROOT`, ferris → `ALICE`, another_user → `BOB`.
The recorder rejects a capture whose accounts do not fit the model's convention (gid = own group, no other groups) or that contains an id outside the three accounts.

### The PAM account helper

The first guest capture (commit `776a0317`, job `lifecycle-trace-d41939`) showed a second program in the permitted run.
sudo's main process forked a child before the command. The child called `setuid(0)` and executed `/usr/sbin/unix_chkpwd ferris chkexpiry` with an empty environment.
The child inherits sudo's launch credentials (real uid ferris, effective and saved uid 0), so after `setuid(0)` all three uids are 0. The gids and the group list stay ferris's.
The program, the `chkexpiry` argument and the `common-account` include of the fixture's PAM file point to pam_unix's account management, which runs this helper to check password expiry. That attribution is an inference from the trace, not checked against the Linux-PAM source here.
No such program appears in the refusal, which stops before PAM.

The recorder accepts this event only if all of the following hold:
- the path is `/usr/sbin/unix_chkpwd` and the argv is exactly `unix_chkpwd <invoker> chkexpiry`, with no environment variables;
- the process was forked by sudo's main process and started with sudo's launch credentials;
- its only credential call is `setuid(0)`, before the exec, and it executes nothing else;
- at the exec its credentials are the launch credentials with all three uids 0;
- it runs at most once, only in a run that executes the command, and before the command.

Any other program, or this program in any other form, is rejected as unclassified.

The model does not cover this event. `inv4_helperIsolation` is about the helpers sudo itself starts (mailer, askpass, editor), which drop to the invoker's credentials. The PAM helper is started by the PAM stack inside sudo's process, as root and with fixed arguments, and the model contains no PAM.
The replay therefore makes no claim about it. Its credentials are recorded in the observation (`unmodelled`), and the rule above keeps every detail of the event fixed.

### Rejection

The recorder and `replay` reject, before the model runs: a guest refusal or incomplete capture; fixture or guest script different from the committed ones; installed sudoers or PAM file different from the fixture; a binary with setuid/setgid bits, other owner or mode, or a guest hash different from the copied binary; `src.tar` different from `git archive` of the recorded commit (checked when the clone has the commit); a launcher, environment or argv other than the declared ones; strace output that cannot be parsed or a failed credential call; any program executed after sudo other than the command and the classified PAM helper; a command process whose credential calls differ from `setgroups`, `setgid`, `setuid`; command credentials that differ from the traced ones; an outcome that is neither a completed exec nor the policy refusal; a timestamp record before the run.
The model rejects: a permitted run whose pinned verdict requires a password (`setup` is not enabled), a refusal under a permitting verdict, an exec after a denial, launch credentials other than `setuidRootExec(invoker)`, credential calls or command credentials other than the model's, a command other than the decided one, a ticket the model does not create, and any invariant violation.

`observe.py controls` shows on each real observation that the replay is not vacuous. It first requires both scenarios to be accepted, then requires every control to be rejected.
Raw controls (edited captures): command output, PAM helper argv, the PAM helper's `setuid(0)` removed (both only when the capture contains the helper), binary hash, installed sudoers hash, the stored verdict, the provenance kind.
Model controls (edited facts, never written as observations): the command ran with the invoker's credentials; kept the invoker's group; another command ran; a timestamp record appeared; the fixture pins a password rule; sudo started without setuid-root credentials; the denied request executed; the permitted request was refused.

### Boundary

- Two runs of one fixture. The replay shows that these runs are runs of the model and satisfy its invariants; it says nothing about other requests, policies or attackers.
- The binary does not run setuid. `setpriv` reproduces the credentials of a setuid-root exec, but not the kernel's secure-exec handling (`AT_SECURE`, dumpability, dynamic-loader environment filtering). sudo-rs's own check (`self_check`) only tests the effective uid (code reading: `src/sudo/mod.rs`).
- strace (a tracer is attached, `TracerPid` is set) changes timing, not results; nothing is injected.
- PAM's library calls are neither observed nor modelled. The model's only authentication event, the password check, does not occur in either run. PAM's helper program is observed, but not modelled (see above).
- The verdicts are pinned by reading the fixture rule, not by the kernel-checked `text_to_authorization`.
- The model's `setresgid(g,g,g)`/`setresuid(u,u,u)` stands for sudo-rs's `setgid`/`setuid` as root, which set all three ids on Linux (`kernel.qnt` semantics).
- Debug build with default features; the compliance image builds with other features.
