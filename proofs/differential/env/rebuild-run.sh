#!/usr/bin/env bash
# Compare C sudo 1.9.18's actual rebuild/validation/insertion with env_fixture_cases.
# Run as an ordinary Linux user: bash proofs/differential/env/rebuild-run.sh OUT
# SUDO_SRC: read-only pinned git checkout (defaults to the omnirun C cache).
# SUDO_RS_ENV_CASES: optional absolute fixture path (default: src/sudo/env/fixture_cases.txt).
# OUT receives aggregate observations, provenance and build logs (Rust log only for the default).
set -euo pipefail
umask 077
export LC_ALL=C LANG=C
unset LANGUAGE RUSTFLAGS CARGO_ENCODED_RUSTFLAGS

repo=${ASSURANCE_ROOT:-$(cd "$(dirname "$0")/../../.." && pwd)}
here=$repo/proofs/differential/env
fixture_input=$repo/src/sudo/env/fixture_cases.txt
private_input=0
if [[ -v SUDO_RS_ENV_CASES ]]; then
    fixture_input=$SUDO_RS_ENV_CASES
    private_input=1
    if [[ $fixture_input != /* ]]; then
        echo 'SUDO_RS_ENV_CASES must be an absolute path' >&2
        exit 2
    fi
fi
unset SUDO_RS_ENV_CASES
out=${1:-${OMNIRUN_OUTPUT:?usage: rebuild-run.sh OUT}}
if [[ ${EUID} == 0 || $(uname -s) != Linux ]]; then
    echo 'rebuild-run.sh needs an ordinary nonroot Linux user' >&2
    exit 2
fi
if [[ -n ${OMNIRUN_ROOT:-} ]]; then
    cache=$OMNIRUN_ROOT/cache/sudo-rs-fuzz
    export RUSTUP_HOME="$cache/rustup" CARGO_HOME="$cache/cargo" PATH="$cache/cargo/bin:$PATH"
fi
src=${SUDO_SRC:-${OMNIRUN_ROOT:+$OMNIRUN_ROOT/cache/sudo-rs-csudo/sudo}}
: "${src:?set SUDO_SRC to the pinned C sudo checkout}"
pin=d58e85d868c79ab92860e22fc2d76756cf8f0e2c
jobs=${JOBS:-${SLURM_CPUS_PER_TASK:-4}}
export RUSTUP_TOOLCHAIN=nightly-2026-11-20

mkdir -p "$out"
out=$(realpath "$out")
scratch_root=$(realpath -e "${TMPDIR:-/tmp}")
scratch=$(mktemp -d "$scratch_root/sudo-env-rebuild.XXXXXXXX")
trap 'rm -rf -- "$scratch"' EXIT
mkdir "$scratch/sudo" "$scratch/joblib"

# Snapshot once; validation, hashing, C and Rust all consume these exact bytes. The source
# fixture is never modified, and the snapshot and raw observations never go into OUT.
fixture=$scratch/cases.txt
if [[ ! -f $fixture_input ]] || ! cp -- "$fixture_input" "$fixture" 2>/dev/null; then
    echo 'cannot read comparison fixture' >&2
    exit 2
fi
chmod 400 "$fixture"
fixture_sha256=$(sha256sum < "$fixture")

# Refuse unsupported input before either implementation consumes the fixture.
python3 "$here/rebuild_compare.py" "$fixture" | tee "$out/rebuild-summary.txt"
if [[ $(git -C "$src" rev-parse HEAD) != "$pin" ]]; then
    echo 'wrong C sudo checkout revision' >&2
    exit 2
fi
git -C "$src" archive "$pin" | tar -x -C "$scratch/sudo"
grep -q "^PACKAGE_VERSION='1.9.18'$" "$scratch/sudo/configure"
{
    printf 'c_sudo=1.9.18\nc_revision=%s\nlocale=C\nrust_features=no-default-features\n' "$pin"
    printf 'c_system_environment=empty\nenv_reset=true\nenv_lists=fixture replacements\n'
    (cd "$scratch/sudo" && sha256sum plugins/sudoers/env.c)
    printf 'fixture_sha256=%s\n' "${fixture_sha256%% *}"
    rustc -Vv
    gcc --version
} > "$out/rebuild-provenance.txt"

# Upstream's configured objects and static sudoers module, not a replacement for env.c.
# No sudo frontend, make install, or C regress execution is involved.
if ! (
    cd "$scratch/sudo" || exit 2
    env -u CPPFLAGS -u LDFLAGS -u LIBS CONFIG_SITE=/dev/null CC=gcc CFLAGS='-O2 -g' \
        ./configure --disable-shared --enable-static-sudoers --without-pam --disable-nls \
        --without-sendmail --without-lecture --disable-sasl --without-ldap \
        --disable-log-server --disable-log-client --disable-openssl --disable-gcrypt \
        --without-audit --without-selinux --without-apparmor --disable-zlib --with-noexec=no \
        --enable-env-reset --without-secure-path &&
    make -C lib/util -j"$jobs" &&
    make -C lib/eventlog -j"$jobs" &&
    make -C lib/iolog -j"$jobs" &&
    cp "$here/rebuild-env.c" plugins/sudoers/ &&
    make -C plugins/sudoers -f Makefile -f - -j"$jobs" rebuild-env <<'MAKE'
rebuild-env: rebuild-env.o sudoers.la $(LIBUTIL)
	$(LIBTOOL) $(LTFLAGS) --mode=link $(CC) -o $@ rebuild-env.o $(LDFLAGS) $(ASAN_LDFLAGS) $(PIE_LDFLAGS) $(HARDENING_LDFLAGS) sudoers.la $(LIBUTIL)
MAKE
) > "$out/rebuild-c-build.log" 2>&1; then
    echo 'C build failed; see rebuild-c-build.log' >&2
    exit 2
fi

# The Rust binary links libpam but this test supplies an empty PAM environment and starts no
# session. Some cluster nodes have the runtime library without the development linker alias.
for dir in /usr/lib64 /lib64 /usr/lib/x86_64-linux-gnu; do
    if [[ -f $dir/libpam.so.0 ]]; then
        ln -s "$dir/libpam.so.0" "$scratch/joblib/libpam.so"
        break
    fi
done
rust_log=$out/rebuild-rust-build.log
if (( private_input )); then
    rust_log=$scratch/rust-build.log
fi
if ! (
    cd "$repo" || exit 2
    export LIBRARY_PATH="$scratch/joblib${LIBRARY_PATH:+:$LIBRARY_PATH}"
    export CARGO_TARGET_DIR="$scratch/target" CARGO_BUILD_JOBS="$jobs"
    export SUDO_RS_ENV_CASES="$fixture"
    export SUDO_RS_ENV_OBSERVATIONS="$scratch/rust.tsv"
    cargo test --locked --no-default-features --lib sudo::env::tests::env_fixture_cases -- --exact &&
    test -s "$SUDO_RS_ENV_OBSERVATIONS"
) > "$rust_log" 2>&1; then
    if (( private_input )); then
        echo 'Rust test failed or produced no observations (private fixture)' >&2
    else
        echo 'Rust test failed or produced no observations; see rebuild-rust-build.log' >&2
    fi
    exit 2
fi

python3 "$here/rebuild_compare.py" "$fixture" \
    "$scratch/sudo/plugins/sudoers/rebuild-env" "$scratch/rust.tsv" |
    tee -a "$out/rebuild-summary.txt"
