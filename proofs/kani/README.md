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
wall time (including ~5-15 s compilation) and the scope's peak memory. Rows marked 8G were
measured with an 8 GiB limit per harness, rows marked 5G with 5 GiB and a 600 s time limit;
all on a shared 4-CPU slice with other jobs running.

## Replaced functions (`#[kani::stub]`)

| Replaced | Returns instead |
|---|---|
| `common::resolve::canonicalize` | the path unchanged, another path, or an error |
| `libc::free` (PAM buffer only) | asserts the freed buffer is wiped; does not release it |
| `system::audit::secure_open_cookie_file` (E1) | checks the path it receives on the bytes, then ends the execution (`kani::assume(false)`); a `kani::cover!` shows it is reached |
| `system::time::SystemTime::now` (E5) | any normalised time |
| `system::User::from_uid` (E5 rootpw) | an entry with the requested uid, other fields arbitrary (lookup failures not modelled) |

## Results (bounded proofs; all PASS)

| Harness | Property | Bounds | Time | Peak MiB | Limit |
|---|---|---|---|---|---|
| escaped_no_args | `[]` and `[""]` escape to `""` | concrete | 15 s | 364 | 8G |
| escaped_exact_1_arg_1_and_2_bytes | output is exactly: each byte kept iff `[A-Za-z0-9_$-]`, else `\`-prefixed; args joined by one space | 1 arg of 1 byte; 1 arg of 2 bytes | 43 s | 530 | 8G |
| escaped_exact_1_arg_3_bytes | same | 1 arg of 3 bytes | 46 s | 816 | 8G |
| escaped_exact_1_arg_4_bytes | same | 1 arg of 4 bytes | 222 s | 4168 | 5G |
| escaped_exact_1_arg_5_bytes | same | 1 arg of 5 bytes | 502 s | 4701 | 5G |
| escaped_exact_2_args_2_bytes | same | 2 args x 2 bytes | 90 s | 2456 | 8G |
| escaped_exact_2_args_with_empty | same | lengths (0,2), (2,0) | 86 s | 2032 | 8G |
| escaped_injective_1x2_vs_2x1 | equal escaped strings imply equal lists | [2] vs [1,1] | 66 s | 790 | 8G |
| escaped_injective_1x3_vs_2x1 | same | [3] vs [1,1] | 77 s | 1523 | 5G |
| escaped_injective_1x3_space_vs_2x1 | same | [3] with middle byte a space vs [1,1] | 63 s | 1054 | 5G |
| escaped_injective_1x2_vs_1x2 | same | [2] vs [2] | 25 s | 829 | 8G |
| escaped_injective_mixed_lengths | same | [1] vs [2]; [2] vs [1,0]; [2] vs [0,1] | 72 s | 1500 | 8G |
| shell_empty_list_collision_not_policy_visible | `escaped([]) == escaped([""])`, but the policy sees `[]` vs `["-c",""]` | concrete | 23 s | 612 | 8G |
| shell_policy_arguments_injective_1x2_vs_2x1 | policy arguments `["-c", escaped]` equal only for equal lists | [2] vs [1,1] | 329 s | 6376 | 8G |
| direct_empty_argv_panics | direct mode with empty argv panics (callers never pass one) | concrete, `should_panic` | 14 s | 657 | 8G |
| from_ptr_null_is_empty | `string_from_ptr`/`os_string_from_ptr` map NULL to "" | concrete | 5 s | 238 | 8G |
| cerr_only_minus_one_is_error | `cerr(x)` is Err iff x == -1, else Ok(x) | all i32, i64, isize | 10 s | 259 | 8G |
| dynamic_fill_bounds_and_result | offered buffers grow strictly within [start,end]; result is what the closure reported | ranges 1..16, 3..10, 5..5, 32..64; arbitrary closure | 41 s | 1058 | 8G |
| dynamic_fill_overlong_report_panics | over-long report panics | concrete | 9 s | 230 | 8G |
| alloc_dynamic_any_kernel_size | seccomp buffers non-null, aligned, zeroed, size = max(reported, type size) | all u16 sizes | 26 s | 257 | 8G |
| pam_buffer_bounds_and_terminator | 511 bytes reachable, writes read back, index >= 511 refused, terminator stays NUL | any index/value | 86 s | 2481 | 8G |
| pam_buffer_wiped_on_drop | all 512 bytes overwritten before free | any content | 84 s | 810 | 8G |
| wipe_memory_exact_8 | exactly the given slice is overwritten | slices up to 8 bytes in a 10-byte array | 6 s | 300 | 8G |
| signaler_pid_reads_si_pid | user signals yield the pid at offset 16, others None; read stays in siginfo_t | all 128-byte patterns | 6 s | 299 | 8G |
| record_encode_decode_roundtrip_tty | a tty-scope session record encodes to 50 bytes and decodes to itself | all field values, nanoseconds in [0, 10^9) | 45 s | 519 | 5G |
| record_encode_decode_roundtrip_ppid | a parent-process-scope record encodes to 46 bytes and decodes to itself | same | 40 s | 460 | 5G |
| record_matches_exactly_its_scope_and_auth_user | a record matches (scope, authenticating user) iff scope and uid are the ones written; the targetpw and invoking-user constructors carry that user's uid | all scopes, uids; 2-byte user names | 172 s | 2571 | 5G |
| record_path_is_uid_entry_name_2_bytes | (E1, CVE-2023-42456 class) `open_for_user` opens exactly `/var/run/sudo-rs/ts/1000`: inside the directory, no `..` last component, named by the uid alone | uid 1000; every valid 2-byte name | 132 s | 1196 | 5G |
| record_path_is_uid_entry_name_3_bytes | same | uid 1000; every valid 3-byte name | 127 s | 1200 | 5G |
| record_decode_tty_50_bytes | (E3) decoding never panics or reads outside the input; accepted iff enabled flag is 0x00/0xFF | 50 bytes, tag 1; stored seconds in [-2^62, 2^62] | 32 s | 462 | 5G |
| record_decode_ppid_46_bytes | same | 46 bytes, tag 2; same precondition | 30 s | 447 | 5G |
| record_decode_tty_wrong_lengths_fail | (E3) rejected without panic | tag 1; 1, 13, 45, 46, 47, 49, 51 bytes; same precondition | 129 s | 2183 | 5G |
| record_decode_ppid_wrong_lengths_fail | same | tag 2; 1, 13, 45, 47, 49, 50, 51 bytes; same precondition | 183 s | 2721 | 5G |
| created_record_identifies_invoking_user | (E5, CVE-2025-64517 class) the created record matches the authenticating user, no user with another uid, and not the invoking user unless same uid | default authentication; all scopes, uids; 2-byte names | 56 s | 666 | 5G |
| created_record_identifies_target_user_targetpw | same; the record carries the target user's uid | targetpw | 64 s | 683 | 5G |
| created_record_identifies_root_rootpw | same; `resolve_root_for_rootpw` yields uid 0 | rootpw, lookup returns an entry | 491 s | 828 | 5G |

## Planted bugs

Scratch copies (never committed), see the report of the branch: escaping with space kept,
`DerefMut` of `PamBuffer` one byte too long, record path built from the user name (pre-fix
CVE-2023-42456), record decoding without its precondition.

| Planted bug | Harness | Clean tree | Planted copy |
|---|---|---|---|
| space kept by `escaped` | escaped_exact_1_arg_1_and_2_bytes | PASS | FAIL |
| space kept by `escaped` | escaped_injective_1x2_vs_2x1 | PASS | PASS (shape too small) |
| `PamBuffer` `DerefMut` one byte too long | pam_buffer_bounds_and_terminator | PASS | FAIL |

## Not covered

- Escaping: 1 argument of 6 bytes, 3-argument shapes [1,1,1] and [1,0,1] (exact output), and
  injectivity [1,1,1] vs [2,1] / [1,2]: out of memory at 5 GiB (110-572 s).
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
