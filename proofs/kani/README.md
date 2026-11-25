# Kani bounded proofs

Bounded model checking of selected sudo-rs functions with Kani 0.68.0 (CBMC 6.11.0, CaDiCaL;
Kani toolchain nightly-2026-08-21). Every result is a **bounded proof**: it holds for all inputs
within the stated sizes (every byte value, every integer) and for nothing larger. Kani's default
checks stay on: bounds, pointer validity, arithmetic overflow, panics, unwinding assertions.

Harnesses check the real functions. They live in `#[cfg(kani)]` child modules
`src/<path>/kani_proofs.rs`; normal builds never compile them (`cfg(kani)` is declared for
`check-cfg` in `Cargo.toml`). Outside those modules only the test constructor
`CurrentUser::fake` is also compiled under `cfg(kani)`.

```sh
cargo install --locked kani-verifier && cargo kani setup     # once
/tmp/sudo-rs-wt/dev proofs/kani/run.sh [harness-substring ...]
/tmp/sudo-rs-wt/dev proofs/check.sh kani                      # gate stage, not default
```

`run.sh` runs one Kani process per harness and reports result, wall time (including
compilation) and peak memory. On the verification machine each harness gets its own
memory-limited scope and the peak is that scope's; without the limiter (`KANI_LIMITED` naming a
missing file) it is the largest process's maximum resident set (GNU `time`). A `PASS` needs a
successful proof and every coverage witness. `FAIL` reports a failed check; `VACUOUS` reports
an unmet coverage witness. `TIME`, `OOM` (including solver-reported memory exhaustion),
`UNSUPPORTED` (for example a foreign call without an effective stub) and `ERROR` do not
establish a counterexample or a proof. All non-`PASS` statuses make the runner fail.

At `f20cfeb7` all 36 harnesses passed in one Slurm job (8 CPUs, 24 GB requested, GCC 11.5).
Three groups ran concurrently; each group ran its harnesses serially with a 3600 s timeout.
The job had no additional per-harness memory limit.

```sh
KANI_LIMITED=/nonexistent KANI_TIMEOUT=3600 proofs/kani/run.sh common::command::
KANI_LIMITED=/nonexistent KANI_TIMEOUT=3600 proofs/kani/run.sh system::timestamp::
KANI_LIMITED=/nonexistent KANI_TIMEOUT=3600 proofs/kani/run.sh cutils:: exec::noexec:: pam::securemem:: system::signal::
```

The complete job took 12 minutes, including setup and checks on the planted copies.

## Replaced functions (`#[kani::stub]`)

| Replaced | Returns instead |
|---|---|
| `common::resolve::canonicalize` | the path unchanged, another path, or an error |
| `libc::free` (PAM buffer only) | asserts the freed buffer is wiped; does not release it |
| `system::audit::secure_open_cookie_file` (E1) | checks the path it receives on the bytes, then ends the execution (`kani::assume(false)`); a `kani::cover!` shows it is reached |
| `system::time::SystemTime::now` (E5) | any normalised time |
| `system::User::from_uid` (E5 rootpw) | an entry with the requested uid, other fields arbitrary (lookup failures not modelled) |

## Results (bounded proofs)

| Harness | Property | Bounds | Result | Time | Peak MiB |
|---|---|---|---|---|---|
| escaped_no_args | `[]` and `[""]` escape to `""` | concrete | PASS | 6 s | 297 |
| escaped_exact_1_arg_1_and_2_bytes | output is exactly: each byte kept iff `[A-Za-z0-9_$-]`, else `\`-prefixed; args joined by one space | 1 arg of 1 byte; 1 arg of 2 bytes | PASS | 15 s | 422 |
| escaped_exact_1_arg_3_bytes | same | 1 arg of 3 bytes | PASS | 21 s | 772 |
| escaped_exact_1_arg_4_bytes | same | 1 arg of 4 bytes | PASS | 48 s | 1670 |
| escaped_exact_1_arg_5_bytes | same | 1 arg of 5 bytes | PASS | 150 s | 3490 |
| escaped_exact_2_args_2_bytes | same | 2 args x 2 bytes | PASS | 64 s | 2609 |
| escaped_exact_2_args_with_empty | same | lengths (0,2), (2,0) | PASS | 44 s | 2388 |
| escaped_injective_1x2_vs_2x1 | equal escaped strings imply equal lists | [2] vs [1,1] | PASS | 18 s | 695 |
| escaped_injective_1x3_vs_2x1 | same | [3] vs [1,1] | PASS | 23 s | 951 |
| escaped_injective_1x3_space_vs_2x1 | same | [3] with middle byte a space vs [1,1] | PASS | 25 s | 914 |
| escaped_injective_1x2_vs_1x2 | same | [2] vs [2] | PASS | 20 s | 640 |
| escaped_injective_mixed_lengths | same | [1] vs [2]; [2] vs [1,0]; [2] vs [0,1] | PASS | 52 s | 1449 |
| shell_empty_list_collision_not_policy_visible | `escaped([]) == escaped([""])`, but the policy sees `[]` vs `["-c",""]` | concrete | PASS | 19 s | 553 |
| shell_policy_arguments_injective_1x2_vs_2x1 | policy arguments `["-c", escaped]` equal only for equal lists | [2] vs [1,1] | PASS | 182 s | 4804 |
| direct_empty_argv_panics | direct mode with empty argv panics (callers never pass one) | concrete, `should_panic` | PASS | 9 s | 492 |
| from_ptr_null_is_empty | `string_from_ptr`/`os_string_from_ptr` map NULL to "" | concrete | PASS | 6 s | 308 |
| cerr_only_minus_one_is_error | `cerr(x)` is Err iff x == -1, else Ok(x) | all i32, i64, isize | PASS | 8 s | 329 |
| dynamic_fill_bounds_and_result | offered buffers grow strictly within [start,end]; result is what the closure reported | ranges 1..16, 3..10, 5..5, 32..64; arbitrary closure | PASS | 33 s | 1050 |
| dynamic_fill_overlong_report_panics | over-long report panics | concrete | PASS | 5 s | 302 |
| alloc_dynamic_any_kernel_size | seccomp buffers non-null, aligned, zeroed, size = max(reported, type size) | all u16 sizes | PASS | 7 s | 326 |
| pam_buffer_bounds_and_terminator | 511 bytes reachable, writes read back, index >= 511 refused, terminator stays NUL | any index/value | PASS | 99 s | 1495 |
| pam_buffer_wiped_on_drop | all 512 bytes overwritten before free | any content | PASS | 68 s | 803 |
| wipe_memory_exact_8 | exactly the given slice is overwritten | slices up to 8 bytes in a 10-byte array | PASS | 6 s | 370 |
| signaler_pid_reads_si_pid | user signals yield the pid at offset 16, others None; read stays in siginfo_t | all 128-byte patterns | PASS | 5 s | 370 |
| record_path_is_uid_entry_name_2_bytes | (E1, CVE-2023-42456 class) `open_for_user` opens exactly `/var/run/sudo-rs/ts/1000`: inside the directory, no `..` last component, named by the uid alone | uid 1000; every valid 2-byte name | PASS | 36 s | 771 |
| record_path_is_uid_entry_name_3_bytes | same | uid 1000; every valid 3-byte name | PASS | 37 s | 787 |
| record_encode_decode_roundtrip_tty | (E2) a tty-scope record encodes to 50 bytes and decodes to itself | all field values, nanoseconds in [0, 10^9) | PASS | 21 s | 530 |
| record_encode_decode_roundtrip_ppid | (E2) a parent-process-scope record encodes to 46 bytes and decodes to itself | same | PASS | 21 s | 530 |
| record_decode_tty_50_bytes | (E3) decoding never panics or reads outside the input; accepted iff the enabled flag is 0x00/0xFF | 50 bytes, tag 1; stored seconds in [-2^62, 2^62] | PASS | 18 s | 501 |
| record_decode_ppid_46_bytes | same | 46 bytes, tag 2; same precondition | PASS | 18 s | 502 |
| record_decode_tty_wrong_lengths_fail | (E3) rejected without panic | tag 1; 1, 13, 45, 46, 47, 49, 51 bytes; same precondition | PASS | 99 s | 1342 |
| record_decode_ppid_wrong_lengths_fail | same | tag 2; 1, 13, 45, 47, 49, 50, 51 bytes; same precondition | PASS | 107 s | 1848 |
| record_matches_exactly_its_scope_and_auth_user | (E4, CVE-2025-64517 class) a record matches (scope, authenticating user) iff scope and uid are the ones written; the targetpw and invoking-user constructors carry that user's uid | all scopes, uids; 2-byte names | PASS | 21 s | 572 |
| created_record_identifies_invoking_user | (E5, CVE-2025-64517 class) the created record matches the authenticating user, no user with another uid, and not the invoking user unless same uid | default authentication; all scopes, uids; 2-byte names | PASS | 27 s | 577 |
| created_record_identifies_target_user_targetpw | same; the record carries the target user's uid | targetpw | PASS | 33 s | 574 |
| created_record_identifies_root_rootpw | same; `resolve_root_for_rootpw` yields uid 0 | rootpw, lookup returns an entry | PASS | 131 s | 605 |

### Secure file opening and credential changes

The [file-policy harnesses](../../src/system/audit/kani_proofs.rs) check every `u32`
owner/group/mode triple. The second harness also varies metadata-read success, and
checks that the *same handle* is returned after acceptance and dropped on failure.
The [credential harnesses](../../src/system/kani_proofs.rs) use the same generic
drivers as production with a local recorder in place of the native system calls.

| Check | Bound | Property |
|---|---|---|
| `inject_group_{empty,one_entry,two_entries}` | 0, 1 or 2 initial groups, arbitrary IDs, capacity 3 | The primary group is inserted or moved to the front; other groups and duplicates are preserved. |
| `credential_application_order_and_fail_stop` | 0–3 prepared groups, all IDs, every first failing setter | The calls use the intended groups, GID and UID in that order. A failed setter prevents all later setters. |
| `temporary_credentials_switch_and_restore` | 0–3 target and 0–2 saved groups | A failed snapshot or switch cannot call the operation. The guard restores the saved credentials in reverse order. |
| `temporary_credentials_restore_is_fail_stop` | Same group bounds, failure at each restore step | The driver does not return normally after a restoration failure. |

In `assurance-kani-credscore-41b384`, six harnesses passed on their unchanged
definitions; `assurance-kani-credscore-5d6f51` checked both temporary-switch
harnesses after their success and failure witnesses were separated. All 28 intended
coverage obligations were reached across the two runs. These are bounded driver
proofs, not verification of `open`/`fstat`, NSS, filesystem races, OS credential
effects, `errno`, panic unwinding, or the standard library's `pre_exec`/exec behavior.

## Planted bugs

Each planted bug is a patch applied to a copy of the tree at `f20cfeb7` (never committed; the
committed tree records only the outcome), checked in the same run as the table above with the
harnesses that should catch it. FAIL here is a failed Kani check, named in the last column.

| Planted bug | Harness | Clean tree | Planted copy |
|---|---|---|---|
| record path built from the user name (pre-fix CVE-2023-42456) | record_path_is_uid_entry_name_2_bytes | PASS | FAIL: "outside the timestamp directory", "ends in a `..` component", "not <timestamp directory>/<uid>" |
| same | record_path_is_uid_entry_name_3_bytes | PASS | FAIL: the same three checks |
| space kept by `escaped` | escaped_exact_1_arg_1_and_2_bytes | PASS | FAIL: `is_escaping_of(args, out)` |
| same | escaped_injective_1x3_vs_2x1 | PASS | FAIL: `a == b` |
| same | escaped_injective_1x3_space_vs_2x1 | PASS | FAIL: `a == b` |
| same | escaped_injective_1x2_vs_2x1 | PASS | PASS (shape too small to show the collision) |
| `PamBuffer` `DerefMut` one byte too long | pam_buffer_bounds_and_terminator | PASS | FAIL: `i < SIZE - 1` |
| record decoding without the seconds precondition | record_decode_tty_50_bytes, record_decode_ppid_46_bytes | PASS | FAIL: "attempt to add with overflow" (time normalisation) |

## Not covered

- Escaping, measured on the pre-rebase implementation (5 GiB): 1 argument of 6 bytes,
  3-argument shapes [1,1,1] and [1,0,1] (exact output), injectivity [1,1,1] vs [2,1] / [1,2]:
  out of memory (110-572 s). Not retried on the rewritten `escaped`.
- `NameOrId::parse` (C): symbolic inputs on the heap `SudoString` exceed time/memory limits at
  4 bytes; no committed harness.
- `string_from_ptr`/`os_string_from_ptr` on non-null input, `User::from_libc`,
  `Group::from_libc`: Kani 0.68 does not support the foreign `strlen` used by `CStr::from_ptr`.
- `read_unbuffered` (rpassword): unwinding of the 512-byte wipe on drop exceeds the bounds.
- Direct-mode `build_from_args` argv tail: timed out (420 s) even at 2 x 1 byte.
- Session record decoding: inputs whose first byte (scope tag) is not 1 or 2 (error message
  formatting and boxed custom error: timed out at 300-600 s, even for 3 concrete tags);
  re-encoding a decoded well-formed record to the same bytes (out of memory at 5 GiB).
- Session record path for an arbitrary uid (E1 uses uid 1000): timed out at 420 s.
- The authenticating-user choice in `sudo::pipeline::auth_and_update_record_file` (PAM,
  process and file calls) and `SessionRecordFile::create` (real file I/O) are not reachable.
