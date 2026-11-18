#!/usr/bin/env bash
# Build C sudo's testsudoers (with testsudoers-flags.patch) in a scratch copy of the sudo
# sources and print the path of the binary. Reuses an existing build.
#   SUDO_SRC   sudo source tree, read-only (default /tmp/fi/src/sudo)
#   TS_BUILD   scratch build directory      (default /tmp/sudo-differential/sudo)
set -euo pipefail

here=$(cd "$(dirname "$0")" && pwd)
src=${SUDO_SRC:-/tmp/fi/src/sudo}
build=${TS_BUILD:-/tmp/sudo-differential/sudo}
bin=$build/plugins/sudoers/testsudoers

if [ -x "$bin" ] && cmp -s "$here/testsudoers-flags.patch" "$build/.differential-patch"; then
  echo "$bin"
  exit 0
fi

rm -rf "$build"
mkdir -p "$(dirname "$build")"
cp -r "$src" "$build"
cd "$build"
patch -p1 < "$here/testsudoers-flags.patch" >&2
./configure --disable-shared --without-pam --disable-nls --without-sendmail \
  --without-lecture --disable-sasl --without-ldap --disable-log-server --disable-log-client \
  --disable-openssl --disable-gcrypt --without-audit --without-selinux --without-apparmor \
  --disable-zlib --with-noexec=no > configure.log 2>&1
make -C lib/util -j"$(nproc)" > make-util.log 2>&1
make -C plugins/sudoers -j"$(nproc)" testsudoers > make-testsudoers.log 2>&1
cp "$here/testsudoers-flags.patch" .differential-patch
echo "$bin"
