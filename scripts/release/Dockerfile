# The toolchain image of eukhe-release.yml's build-linux job
# (ghcr.io/gildrb/eukhe-build:jammy-<date>, linux/amd64 + linux/arm64): the
# glibc 2.35 baseline (Ubuntu 22.04) with the release build's prerequisites.
# buildpack-deps:jammy-curl is ubuntu:22.04 plus ca-certificates and curl,
# so the snapshot is reachable over verified TLS without an unpinned
# bootstrap. Built once by .github/workflows/build-image.yml
# (scripts/release/build_image.sh); the release pins the result by digest,
# so no release installs a package.
FROM buildpack-deps:jammy-curl@sha256:6326f638affaad95fcc68973d732ecee04d8746fd1529ec113e88c76be9b3ad0

LABEL org.opencontainers.image.source="https://github.com/gildrb/eukhe"
LABEL org.opencontainers.image.description="eukhe release build toolchain (Ubuntu 22.04, glibc 2.35)"

# The Ubuntu archive as of this instant (snapshot.ubuntu.com serves amd64
# and arm64 under the same path). When the snapshot does not answer, the
# regular jammy, jammy-updates and jammy-security archive is used instead;
# /usr/share/eukhe-build/source names the one the image was built from.
ARG UBUNTU_SNAPSHOT=20261005T000000Z

# clang: the compiled Bend core (crates/eukhe-bend, c/core.c) uses
# `musttail`, which gcc accepts only from 15; jammy's clang 14 has it, and
# eukhe-bend's build.rs picks clang when cc lacks it.
RUN <<'EOF'
#!/bin/bash
set -euo pipefail
sources() {
  local base="$1" security="$2" suite
  for suite in jammy jammy-updates; do
    echo "deb ${base} ${suite} main universe"
  done
  echo "deb ${security} jammy-security main universe"
}
rm -f /etc/apt/sources.list.d/*.list /etc/apt/sources.list.d/*.sources
snapshot="https://snapshot.ubuntu.com/ubuntu/${UBUNTU_SNAPSHOT}"
source=""
if curl -fsS --retry 3 -o /dev/null "${snapshot}/dists/jammy/InRelease"; then
  sources "${snapshot}" "${snapshot}" > /etc/apt/sources.list
  # The snapshot server answers 5xx in bursts: each fetch retries.
  if apt-get -o Acquire::Retries=10 update --error-on=any; then
    source="${snapshot}"
  fi
fi
if [[ -z "${source}" ]]; then
  echo "snapshot ${UBUNTU_SNAPSHOT} unavailable: the regular jammy archive"
  case "$(dpkg --print-architecture)" in
    amd64) sources http://archive.ubuntu.com/ubuntu http://security.ubuntu.com/ubuntu > /etc/apt/sources.list ;;
    *) sources http://ports.ubuntu.com/ubuntu-ports http://ports.ubuntu.com/ubuntu-ports > /etc/apt/sources.list ;;
  esac
  apt-get -o Acquire::Retries=10 update --error-on=any
  source="regular jammy archive ($(date -u +%Y-%m-%dT%H:%M:%SZ))"
fi
dpkg-query -W -f '${Package}\n' | sort > /tmp/before
apt-get -o Acquire::Retries=10 install -y --no-install-recommends build-essential clang python3 git binutils
mkdir -p /usr/share/eukhe-build
echo "${source}" > /usr/share/eukhe-build/source
# The packages this layer installed, with their exact versions.
dpkg-query -W -f '${Package}\n' | sort | comm -13 /tmp/before - \
  | xargs dpkg-query -W -f '${Package}=${Version}\n' > /usr/share/eukhe-build/packages.txt
rm -rf /var/lib/apt/lists/* /tmp/before
EOF
