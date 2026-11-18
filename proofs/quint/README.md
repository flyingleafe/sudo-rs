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
| `check.sh` | Typecheck, clean-model checks, mutant checks |
| `traces/` | ITF counterexample of every mutant, written by `check.sh` |

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
- one `PASS ... (apalache, N steps)` line per invariant and implementation;
- one `VIOLATED <invariant> by <mutant> (<bug>)` line per mutant.

The script exits non-zero on any unexpected outcome. That includes a mutant that is not caught, a clean-model violation, an unreached witness, and a typecheck error.

Budgets (environment variables):

| Variable | Default | Meaning |
|---|---|---|
| `SAMPLES` | 100000 | random runs per clean model |
| `STEPS` | 60 | steps per random run (clean and mutants) |
| `MUTANT_SAMPLES` | 100000 | maximum runs per mutant; the search stops at the first violation |
| `VERIFY_STEPS` | VERIFY_DEFAULT | Apalache bound for `quint verify` on the clean models |
| `SEED` | 0x5ad0 | simulator seed |

Typical cost on this machine: about 1 min of simulation per clean model; each mutant fails within seconds. APALACHE_COST

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
