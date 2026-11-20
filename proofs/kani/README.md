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
wall time (including ~15 s compilation) and the scope's peak memory. Measured on a shared
4-CPU slice with other jobs running, 8 GiB limit per harness.

## Replaced functions (`#[kani::stub]`)

| Replaced | Returns instead |
|---|---|
| `common::resolve::canonicalize` | the path unchanged, another path, or an error |
| `system::audit::secure_open_cookie_file` | checks the path it receives, then fails (E1) |
| `system::time::SystemTime::now` | any normalised time (E5) |
| `system::User::from_uid` | error, no entry, or an entry with the requested uid (E5) |
| `libc::free` (F2 only) | asserts the freed buffer is wiped; does not release it |

## Results (bounded proofs; all PASS)

| Harness | Property | Bounds | Time | Peak MiB |
|---|---|---|---|---|
| escaped_no_args | `[]` and `[""]` escape to `""` | concrete | 15 s | 364 |
| escaped_exact_1_arg_1_and_2_bytes | output is exactly: each byte kept iff `[A-Za-z0-9_$-]`, else `\`-prefixed; args joined by one space | 1 arg of 1 byte; 1 arg of 2 bytes | 43 s | 530 |
| escaped_exact_1_arg_3_bytes | same | 1 arg of 3 bytes | 46 s | 816 |
| escaped_exact_2_args_2_bytes | same | 2 args x 2 bytes | 90 s | 2456 |
| escaped_exact_2_args_with_empty | same | lengths (0,2), (2,0) | 86 s | 2032 |
| escaped_injective_1x2_vs_2x1 | equal escaped strings imply equal lists | [2] vs [1,1] | 66 s | 790 |
| escaped_injective_1x2_vs_1x2 | same | [2] vs [2] | 25 s | 829 |
| escaped_injective_mixed_lengths | same | [1] vs [2]; [2] vs [1,0]; [2] vs [0,1] | 72 s | 1500 |
| shell_empty_list_collision_not_policy_visible | `escaped([]) == escaped([""])`, but the policy sees `[]` vs `["-c",""]` | concrete | 23 s | 612 |
| shell_policy_arguments_injective_1x2_vs_2x1 | policy arguments `["-c", escaped]` equal only for equal lists | [2] vs [1,1] | 329 s | 6376 |
| direct_empty_argv_panics | direct mode with empty argv panics (callers never pass one) | concrete, `should_panic` | 14 s | 657 |
| from_ptr_null_is_empty | `string_from_ptr`/`os_string_from_ptr` map NULL to "" | concrete | 5 s | 238 |
| cerr_only_minus_one_is_error | `cerr(x)` is Err iff x == -1, else Ok(x) | all i32, i64, isize | 10 s | 259 |
| dynamic_fill_bounds_and_result | offered buffers grow strictly within [start,end]; result is what the closure reported | ranges 1..16, 3..10, 5..5, 32..64; arbitrary closure | 41 s | 1058 |
| dynamic_fill_overlong_report_panics | over-long report panics | concrete | 9 s | 230 |
| alloc_dynamic_any_kernel_size | seccomp buffers non-null, aligned, zeroed, size = max(reported, type size) | all u16 sizes | 26 s | 257 |
| pam_buffer_bounds_and_terminator | 511 bytes reachable, writes read back, index >= 511 refused, terminator stays NUL | any index/value | 86 s | 2481 |
| pam_buffer_wiped_on_drop | all 512 bytes overwritten before free | any content | 84 s | 810 |
| wipe_memory_exact_8 | exactly the given slice is overwritten | slices up to 8 bytes in a 10-byte array | 6 s | 300 |
| signaler_pid_reads_si_pid | user signals yield the pid at offset 16, others None; read stays in siginfo_t | all 128-byte patterns | 6 s | 299 |

## Planted bugs

Scratch copies (never committed), see the report of the branch: escaping with space kept,
`DerefMut` of `PamBuffer` one byte too long, record path built from the user name (pre-fix
CVE-2023-42456), E3 without its precondition.

## Not covered

- `NameOrId::parse` (C): symbolic inputs on the heap `SudoString` exceed time/memory limits at
  4 bytes; no committed harness.
- `string_from_ptr`/`os_string_from_ptr` on non-null input, `User::from_libc`,
  `Group::from_libc`: Kani 0.68 does not support the foreign `strlen` used by `CStr::from_ptr`.
- `read_unbuffered` (rpassword): unwinding of the 512-byte wipe on drop exceeds the bounds.
- Direct-mode `build_from_args` argv tail: timed out (420 s) even at 2 x 1 byte.
- Escaping with 3 arguments: out of memory at 1 byte each.
- Timestamp harnesses (E1-E5, `system/timestamp/kani_proofs.rs`) are committed but not yet
  verified (E1 timed out at 420 s); they are not part of the passing set above.
- The authenticating-user choice in `sudo::pipeline::auth_and_update_record_file` (PAM,
  process and file calls) and `SessionRecordFile::create` (real file I/O) are not reachable.
