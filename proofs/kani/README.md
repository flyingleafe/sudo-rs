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

`run.sh` runs one Kani process per harness in its own memory-limited scope and reports result,
wall time (including compilation) and the scope's peak memory. A harness with an unsatisfied
`kani::cover!` counts as failed. All runs below were on a shared 4-CPU slice with other work on
the machine (load 12-20), so times vary by 2-4x between runs:

- `common::command` harnesses: run at `fc4a086a` (this branch rebased onto `7d7f363f`, which
  rewrote `escaped` with index loops), 8 GiB / 1800 s per harness, one at a time.
- All other harnesses: full run at `da94693a` (before the rebase), 5 GiB / 600 s per harness.
  Their modules (timestamp, pam/securemem, cutils, exec/noexec, signal/info) are byte-identical
  between `bc2fc69e` and `7d7f363f` outside `cfg(test)`/`cfg(fuzzing)`, so the results carry
  over.

## Replaced functions (`#[kani::stub]`)

| Replaced | Returns instead |
|---|---|
| `common::resolve::canonicalize` | the path unchanged, another path, or an error |
| `libc::free` (PAM buffer only) | asserts the freed buffer is wiped; does not release it |
| `system::audit::secure_open_cookie_file` (E1) | checks the path it receives on the bytes, then ends the execution (`kani::assume(false)`); a `kani::cover!` shows it is reached |
| `system::time::SystemTime::now` (E5) | any normalised time |
| `system::User::from_uid` (E5 rootpw) | an entry with the requested uid, other fields arbitrary (lookup failures not modelled) |

## Results (bounded proofs)

| Harness | Property | Bounds | Result | Time | Peak MiB | Commit, limits |
|---|---|---|---|---|---|---|
| escaped_no_args | `[]` and `[""]` escape to `""` | concrete | PASS | 30 s | 237 | fc4a086a, 8G |
| escaped_exact_1_arg_1_and_2_bytes | output is exactly: each byte kept iff `[A-Za-z0-9_$-]`, else `\`-prefixed; args joined by one space | 1 arg of 1 byte; 1 arg of 2 bytes | PASS | 78 s | 484 | fc4a086a, 8G |
| escaped_exact_1_arg_3_bytes | same | 1 arg of 3 bytes | PASS | 100 s | 806 | fc4a086a, 8G |
| escaped_exact_1_arg_4_bytes | same | 1 arg of 4 bytes | PASS | 185 s | 1697 | fc4a086a, 8G |
| escaped_exact_1_arg_5_bytes | same | 1 arg of 5 bytes | PASS | 731 s | 3515 | fc4a086a, 8G |
| escaped_exact_2_args_2_bytes | same | 2 args x 2 bytes | PASS | 312 s | 2648 | fc4a086a, 8G |
| escaped_exact_2_args_with_empty | same | lengths (0,2), (2,0) | PASS | 290 s | 2468 | fc4a086a, 8G |
| escaped_injective_1x2_vs_2x1 | equal escaped strings imply equal lists | [2] vs [1,1] | PASS | 96 s | 767 | fc4a086a, 8G |
| escaped_injective_1x3_vs_2x1 | same | [3] vs [1,1] | PASS | 126 s | 1004 | fc4a086a, 8G |
| escaped_injective_1x3_space_vs_2x1 | same | [3] with middle byte a space vs [1,1] | PASS | 158 s | 992 | fc4a086a, 8G |
| escaped_injective_1x2_vs_1x2 | same | [2] vs [2] | PASS | 115 s | 632 | fc4a086a, 8G |
| escaped_injective_mixed_lengths | same | [1] vs [2]; [2] vs [1,0]; [2] vs [0,1] | PASS | 298 s | 1441 | fc4a086a, 8G |
| shell_empty_list_collision_not_policy_visible | `escaped([]) == escaped([""])`, but the policy sees `[]` vs `["-c",""]` | concrete | PASS | 112 s | 485 | fc4a086a, 8G |
| shell_policy_arguments_injective_1x2_vs_2x1 | policy arguments `["-c", escaped]` equal only for equal lists | [2] vs [1,1] | PASS | 693 s | 4745 | fc4a086a, 8G |
| direct_empty_argv_panics | direct mode with empty argv panics (callers never pass one) | concrete, `should_panic` | PASS | 51 s | 426 | fc4a086a, 8G |
| from_ptr_null_is_empty | `string_from_ptr`/`os_string_from_ptr` map NULL to "" | concrete | PASS | 30 s | 236 | da94693a, 5G |
| cerr_only_minus_one_is_error | `cerr(x)` is Err iff x == -1, else Ok(x) | all i32, i64, isize | PASS | 49 s | 256 | da94693a, 5G |
| dynamic_fill_bounds_and_result | offered buffers grow strictly within [start,end]; result is what the closure reported | ranges 1..16, 3..10, 5..5, 32..64; arbitrary closure | PASS | 178 s | 1062 | da94693a, 5G |
| dynamic_fill_overlong_report_panics | over-long report panics | concrete | PASS | 32 s | 229 | da94693a, 5G |
| alloc_dynamic_any_kernel_size | seccomp buffers non-null, aligned, zeroed, size = max(reported, type size) | all u16 sizes | PASS | 46 s | 254 | da94693a, 5G |
| pam_buffer_bounds_and_terminator | 511 bytes reachable, writes read back, index >= 511 refused, terminator stays NUL | any index/value | PASS | 589 s | 1973 | da94693a, 5G |
| pam_buffer_wiped_on_drop | all 512 bytes overwritten before free | any content | PASS | 401 s | 810 | da94693a, 5G |
| wipe_memory_exact_8 | exactly the given slice is overwritten | slices up to 8 bytes in a 10-byte array | PASS | 43 s | 298 | da94693a, 5G |
| signaler_pid_reads_si_pid | user signals yield the pid at offset 16, others None; read stays in siginfo_t | all 128-byte patterns | PASS | 39 s | 298 | da94693a, 5G |
| record_path_is_uid_entry_name_2_bytes | (E1, CVE-2023-42456 class) `open_for_user` opens exactly `/var/run/sudo-rs/ts/1000`: inside the directory, no `..` last component, named by the uid alone | uid 1000; every valid 2-byte name | PASS | 219 s | 1196 | da94693a, 5G |
| record_path_is_uid_entry_name_3_bytes | same | uid 1000; every valid 3-byte name | PASS | 210 s | 1200 | da94693a, 5G |
| record_encode_decode_roundtrip_tty | (E2) a tty-scope record encodes to 50 bytes and decodes to itself | all field values, nanoseconds in [0, 10^9) | PASS | 99 s | 461 | da94693a, 5G |
| record_encode_decode_roundtrip_ppid | (E2) a parent-process-scope record encodes to 46 bytes and decodes to itself | same | PASS | 94 s | 462 | da94693a, 5G |
| record_decode_tty_50_bytes | (E3) decoding never panics or reads outside the input; accepted iff the enabled flag is 0x00/0xFF | 50 bytes, tag 1; stored seconds in [-2^62, 2^62] | PASS | 80 s | 442 | da94693a, 5G |
| record_decode_ppid_46_bytes | same | 46 bytes, tag 2; same precondition | PASS | 82 s | 447 | da94693a, 5G |
| record_decode_tty_wrong_lengths_fail | (E3) rejected without panic | tag 1; 1, 13, 45, 46, 47, 49, 51 bytes; same precondition | PASS | 391 s | 2154 | da94693a, 5G |
| record_decode_ppid_wrong_lengths_fail | same | tag 2; 1, 13, 45, 47, 49, 50, 51 bytes; same precondition | PASS | 590 s | 2673 | da94693a, 5G |
| record_matches_exactly_its_scope_and_auth_user | (E4, CVE-2025-64517 class) a record matches (scope, authenticating user) iff scope and uid are the ones written; the targetpw and invoking-user constructors carry that user's uid | all scopes, uids; 2-byte names | PASS | 102 s | 504 | da94693a, 5G |
| created_record_identifies_invoking_user | (E5, CVE-2025-64517 class) the created record matches the authenticating user, no user with another uid, and not the invoking user unless same uid | default authentication; all scopes, uids; 2-byte names | PASS | 150 s | 508 | da94693a, 5G |
| created_record_identifies_target_user_targetpw | same; the record carries the target user's uid | targetpw | PASS | 157 s | 599 | da94693a, 5G |
| created_record_identifies_root_rootpw | same; `resolve_root_for_rootpw` yields uid 0 | rootpw, lookup returns an entry | PASS in a scratch copy with the identical harness (491 s, 828 MiB, 5G); TIME at 600 s in the da94693a run; rerun at fc4a086a with 8G/1800 s pending | | | |

## Planted bugs

Scratch copies (never committed); the committed tree records only the outcome.

| Planted bug | Harness | Clean tree | Planted copy |
|---|---|---|---|
| record path built from the user name (pre-fix CVE-2023-42456) | record_path_is_uid_entry_name_2_bytes | PASS | FAIL (outside the directory, `..` last component, not `<dir>/<uid>`) |
| same | record_path_is_uid_entry_name_3_bytes | PASS | FAIL (same three checks) |
| space kept by `escaped` (pre-rebase implementation) | escaped_exact_1_arg_1_and_2_bytes | PASS | FAIL |
| same | escaped_injective_1x3_vs_2x1 | PASS | FAIL (`a == b`) |
| same | escaped_injective_1x3_space_vs_2x1 | PASS | FAIL (`a == b`) |
| same | escaped_injective_1x2_vs_2x1 | PASS | PASS (shape too small to show the collision) |
| `PamBuffer` `DerefMut` one byte too long | pam_buffer_bounds_and_terminator | PASS | FAIL |
| record decoding without the seconds precondition | record_decode_tty_50_bytes, record_decode_ppid_46_bytes | PASS | FAIL (arithmetic overflow in time normalisation) |

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
