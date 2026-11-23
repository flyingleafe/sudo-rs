#!/usr/bin/env bash
# Build C sudo's visudo, cvtsudoers and testsudoers (unprivileged, not installed) in a scratch
# copy of the sudo 1.9.18 sources and print the build directory. Same configuration as
# build-testsudoers.sh (testsudoers-flags.patch applied). Reuses an existing build.
#   SUDO_SRC     sudo source tree, read-only (default /tmp/fi/src/sudo)
#   CSUDO_BUILD  scratch build directory    (default /tmp/sudo-parser-csudo/sudo)
#   JOBS         parallel make jobs         (default 4)
set -euo pipefail

here=$(cd "$(dirname "$0")" && pwd)
src=${SUDO_SRC:-/tmp/fi/src/sudo}
build=${CSUDO_BUILD:-/tmp/sudo-parser-csudo/sudo}
jobs=${JOBS:-4}
tools=(visudo cvtsudoers testsudoers)

built() {
  for t in "${tools[@]}"; do [ -x "$build/plugins/sudoers/$t" ] || return 1; done
  cmp -s "$here/testsudoers-flags.patch" "$build/.differential-patch"
}

if built; then
  echo "$build"
  exit 0
fi

grep -q "PACKAGE_VERSION='1.9.18'" "$src/configure" || { echo "$src is not sudo 1.9.18" >&2; exit 1; }
rm -rf "$build"
mkdir -p "$(dirname "$build")"
cp -r "$src" "$build"
cd "$build"
patch -p1 < "$here/testsudoers-flags.patch" >&2
# visudo.c needs _PATH_MV, which configure leaves undefined on hosts without /bin/mv (NixOS);
# check mode (-c) never runs it.
CPPFLAGS='-D_PATH_MV=\"/bin/mv\"' ./configure --disable-shared --without-pam --disable-nls --without-sendmail \
  --without-lecture --disable-sasl --without-ldap --disable-log-server --disable-log-client \
  --disable-openssl --disable-gcrypt --without-audit --without-selinux --without-apparmor \
  --disable-zlib --with-noexec=no > configure.log 2>&1
make -C lib/util -j"$jobs" > make-util.log 2>&1
make -C lib/eventlog -j"$jobs" > make-eventlog.log 2>&1
make -C lib/iolog -j"$jobs" > make-iolog.log 2>&1
make -C lib/logsrv -j"$jobs" > make-logsrv.log 2>&1 || true
make -C plugins/sudoers -j"$jobs" "${tools[@]}" > make-tools.log 2>&1
cp "$here/testsudoers-flags.patch" .differential-patch
echo "$build"
