#!/bin/sh
# LifecycleTrace capture inside a disposable virtual machine guest.
#   sh /fixture/guest-run.sh /fixture /out
# Runs as the guest administrator (uid 0) of a fresh Debian guest without a
# sudo package and without network. /fixture is the read-only directory made
# by prepare-input.sh; /out is empty and is copied out afterwards.
#
# 1. Builds the non-setuid sudo-rs binary of src.tar offline, as the
#    unprivileged guest account `builder`.
# 2. Installs the fixture: accounts ferris and another_user, /etc/sudoers-rs,
#    /etc/pam.d/sudo, the binary as root:root 0755 (no setuid bit).
# 3. Runs every scenario of /fixture/scenarios once. The administrator starts
#    the binary with the credentials a setuid-root exec by ferris would give
#    (setpriv: real uid/gid ferris, effective and saved uid 0, ferris's
#    groups), under `strace -f` restricted to execve, fork/clone and the
#    set*id calls. strace only reads; it injects nothing.
# 4. Records outputs, exit codes, the timestamp directory before and after
#    each run, and provenance (hashes, versions, account database).
# Exit 0: capture complete (out/COMPLETE). Exit 3: a precondition does not
# hold; out/REFUSED says which, and nothing was run.
set -eu
in=$1
out=$2
PATH=/usr/sbin:/usr/bin:/sbin:/bin
export PATH

refuse() {
  printf '%s\n' "$*" > "$out/REFUSED"
  echo "REFUSED: $*" >&2
  exit 3
}

# ---- preconditions ---------------------------------------------------------
[ -d "$out" ] || { echo "no output directory $out" >&2; exit 3; }
[ -z "$(ls -A "$out")" ] || { echo "$out is not empty" >&2; exit 3; }
[ "$(id -u)" = 0 ] || refuse "must run as the guest administrator (uid 0)"
grep -qw hypervisor /proc/cpuinfo || refuse "no hypervisor CPU flag: not a virtual machine guest"
for t in setpriv strace useradd getent sha256sum cargo rustc tar stat timeout install; do
  command -v "$t" > /dev/null || refuse "missing tool $t"
done
for f in src.tar guest-run.sh sudoers pam.d-sudo scenarios commit; do
  [ -f "$in/$f" ] || refuse "missing input $in/$f"
done
for f in /etc/sudoers /etc/sudoers-rs /etc/sudoers.d /var/run/sudo-rs; do
  [ ! -e "$f" ] || refuse "$f exists: not a fresh guest without sudo"
done
setuid_sudo=$(find / -xdev \( -name sudo -o -name 'sudo-rs' \) -perm /6000 2> /dev/null || true)
[ -z "$setuid_sudo" ] || refuse "setuid/setgid sudo present: $setuid_sudo"
for u in ferris another_user builder; do
  ! getent passwd "$u" > /dev/null || refuse "account $u already exists"
done
if [ -e /etc/pam.d/sudo ] && ! cmp -s /etc/pam.d/sudo "$in/pam.d-sudo"; then
  refuse "/etc/pam.d/sudo exists and differs from the fixture"
fi

mkdir -p "$out/meta" "$out/build" "$out/bin" "$out/launcher"

# ---- 1. build as an unprivileged account -----------------------------------
useradd --system --user-group --no-create-home --shell /usr/sbin/nologin builder
build=$(mktemp -d /var/tmp/lifecycle-build.XXXXXXXX)
mkdir -p "$build/src" "$build/vendor" "$build/cargo-home"
tar -x -f "$in/src.tar" -C "$build/src"
for crate in "$in"/crates/*.crate; do
  [ -e "$crate" ] || continue
  base=$(basename "$crate" .crate)
  sum=$(sha256sum "$crate" | cut -d' ' -f1)
  mkdir -p "$build/vendor/$base"
  tar -x -z -f "$crate" -C "$build/vendor/$base" --strip-components=1
  # cargo compares "package" with the checksum in Cargo.lock (--locked).
  printf '{"files":{},"package":"%s"}\n' "$sum" > "$build/vendor/$base/.cargo-checksum.json"
  printf '%s  %s\n' "$sum" "$base.crate" >> "$out/meta/crates.sha256"
done
printf '[source.crates-io]\nreplace-with = "vendored"\n[source.vendored]\ndirectory = "%s"\n' \
  "$build/vendor" > "$build/cargo-home/config.toml"
chown -R builder:builder "$build"
build_cmd="cargo build --locked --offline --bin sudo"
printf '%s\n' "$build_cmd" > "$out/meta/build-command"
rc=0
(cd "$build/src" && setpriv --reuid=builder --regid=builder --clear-groups -- \
  env -i PATH=/usr/bin:/bin HOME="$build" CARGO_HOME="$build/cargo-home" \
  CARGO_TARGET_DIR="$build/target" $build_cmd) > "$out/build/log" 2>&1 || rc=$?
[ "$rc" = 0 ] || refuse "build failed with status $rc (see build/log)"

sudo_bin=/usr/local/libexec/lifecycle-trace/sudo
install -D -o root -g root -m 0755 "$build/target/debug/sudo" "$sudo_bin"
cp "$sudo_bin" "$out/bin/sudo"
printf '%s\n' "$sudo_bin" > "$out/meta/binary-path"
stat -c '%a %u %g' "$sudo_bin" > "$out/meta/binary-stat"
sha256sum < "$sudo_bin" | cut -d' ' -f1 > "$out/meta/binary.sha256"

# ---- 2. fixture -------------------------------------------------------------
useradd --user-group --no-create-home --shell /bin/sh ferris
useradd --user-group --no-create-home --shell /bin/sh another_user
install -o root -g root -m 0440 "$in/sudoers" /etc/sudoers-rs
if [ -e /etc/pam.d/sudo ]; then echo preexisting-identical > "$out/meta/pam-origin"
else install -o root -g root -m 0644 "$in/pam.d-sudo" /etc/pam.d/sudo; echo installed > "$out/meta/pam-origin"; fi

# ---- provenance -------------------------------------------------------------
for f in guest-run.sh src.tar sudoers pam.d-sudo scenarios; do
  printf '%s  %s\n' "$(sha256sum < "$in/$f" | cut -d' ' -f1)" "$f"
done > "$out/meta/inputs.sha256"
cp "$in/commit" "$out/meta/commit"
for f in /etc/sudoers-rs /etc/pam.d/sudo /etc/pam.d/common-auth /etc/pam.d/common-account \
         /etc/pam.d/common-session-noninteractive; do
  if [ -e "$f" ]; then printf '%s  %s\n' "$(sha256sum < "$f" | cut -d' ' -f1)" "$f"
  else printf 'ABSENT  %s\n' "$f"; fi
done > "$out/meta/installed.sha256"
uname -srm > "$out/meta/kernel"
cat /etc/os-release > "$out/meta/os-release"
setpriv --version > "$out/meta/setpriv-version" 2>&1
strace -V 2>&1 | head -n 1 > "$out/meta/strace-version"
{ cargo --version; rustc --version; } > "$out/meta/toolchain"
getent passwd root ferris another_user > "$out/meta/passwd"
getent group root ferris another_user > "$out/meta/group"
for u in ferris another_user; do printf '%s %s\n' "$u" "$(id -G "$u")"; done > "$out/meta/groups"
date -u +%Y-%m-%dT%H:%M:%SZ > "$out/meta/date"

# ---- 3. scenarios ------------------------------------------------------------
fuid=$(id -u ferris)
fgid=$(id -g ferris)
launch="setpriv --ruid=$fuid --euid=0 --rgid=$fgid --egid=$fgid --init-groups --"
printf '%s\n' "env -i PATH=/usr/bin:/bin" > "$out/meta/environment"
printf '%s\n' "$launch" > "$out/meta/launcher"
trace_set=execve,fork,vfork,clone,clone3,setgroups,setuid,setgid,setreuid,setregid,setresuid,setresgid

ts_state() {
  if [ -d /var/run/sudo-rs/ts ]; then ls -1A /var/run/sudo-rs/ts; else echo ABSENT; fi
}

# Control: the credentials the launcher gives the program it starts.
env -i PATH=/usr/bin:/bin $launch /usr/bin/cat /proc/self/status > "$out/launcher/status"

set -f
grep -v -e '^#' -e '^[[:space:]]*$' "$in/scenarios" | while read -r name verdict model rest; do
  d="$out/scenario/$name"
  mkdir -p "$d"
  printf '%s %s\n' "$verdict" "$model" > "$d/declared"
  printf '%s\n' $rest > "$d/argv"
  ts_state > "$d/ts-before"
  rc=0
  timeout 120 env -i PATH=/usr/bin:/bin \
    strace -f -qq -s 256 -e signal=none -e trace="$trace_set" -o "$d/strace" \
    $launch "$sudo_bin" $rest < /dev/null > "$d/stdout" 2> "$d/stderr" || rc=$?
  echo "$rc" > "$d/exit"
  ts_state > "$d/ts-after"
done
set +f

date -u +%Y-%m-%dT%H:%M:%SZ > "$out/COMPLETE"
echo "capture complete in $out"
