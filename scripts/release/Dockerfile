# The toolchain image of eukhe-release.yml's build-linux job
# (ghcr.io/gildrb/eukhe-build:jammy-<date>, linux/amd64 + linux/arm64): the
# glibc 2.35 baseline (Ubuntu 22.04) with the release build's prerequisites,
# from the jammy, jammy-updates and jammy-security archive on the day it is
# built. Built once by .github/workflows/build-image.yml
# (scripts/release/build_image.sh, which prints the installed packages and
# records them in the image's labels); the release pins the result by
# digest, so no release installs a package.
FROM buildpack-deps:jammy-curl@sha256:6326f638affaad95fcc68973d732ecee04d8746fd1529ec113e88c76be9b3ad0

LABEL org.opencontainers.image.source="https://github.com/gildrb/eukhe"
LABEL org.opencontainers.image.description="eukhe release build toolchain (Ubuntu 22.04, glibc 2.35)"

# clang: the compiled Bend core (crates/eukhe-bend, c/core.c) uses
# `musttail`, which gcc accepts only from 15; jammy's clang 14 has it, and
# eukhe-bend's build.rs picks clang when cc lacks it.
RUN <<'EOF'
#!/bin/bash
set -euo pipefail
case "$(dpkg --print-architecture)" in
  amd64) base=http://archive.ubuntu.com/ubuntu security=http://security.ubuntu.com/ubuntu ;;
  *) base=http://ports.ubuntu.com/ubuntu-ports security=http://ports.ubuntu.com/ubuntu-ports ;;
esac
rm -f /etc/apt/sources.list.d/*.list /etc/apt/sources.list.d/*.sources
{
  echo "deb ${base} jammy main universe"
  echo "deb ${base} jammy-updates main universe"
  echo "deb ${security} jammy-security main universe"
} > /etc/apt/sources.list
apt-get -o Acquire::Retries=5 update --error-on=any
dpkg-query -W -f '${Package}\n' | sort > /tmp/before
apt-get -o Acquire::Retries=5 install -y --no-install-recommends build-essential clang python3 git binutils
mkdir -p /usr/share/eukhe-build
echo "$(date -u +%Y-%m-%dT%H:%M:%SZ) ${base} ${security}" > /usr/share/eukhe-build/source
# The packages this layer installed, with their exact versions.
dpkg-query -W -f '${Package}\n' | sort | comm -13 /tmp/before - \
  | xargs dpkg-query -W -f '${Package}=${Version}\n' > /usr/share/eukhe-build/packages.txt
rm -rf /var/lib/apt/lists/* /tmp/before
EOF
