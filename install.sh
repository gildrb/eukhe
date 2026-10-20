#!/bin/sh
# eukhe installer: the newest GitHub release, checksum-verified, no root.
#
# Usage:
#   curl -fsSL https://eukhe.com/install | sh
#   sh install.sh [version]
#
# Install (macOS Apple Silicon, Linux x64 and arm64):
#
#   curl -fsSL https://eukhe.com/install | sh
#
# Pin one release (0.10.41, v0.10.41 or eukhe-v0.10.41):
#
#   curl -fsSL https://eukhe.com/install | sh -s -- 0.10.41
#
# https://eukhe.com/install redirects to the copy of this script that each
# release attaches (releases/latest/download/install.sh), so the script that
# runs is the one CI passed with the newest release.
#
# The payload lands in ${EUKHE_INSTALL_ROOT:-~/.local/share/eukhe}/eukhe-<version>
# and a launcher in ${EUKHE_INSTALL_BIN_DIR:-~/.local/bin}/eukhe. Re-running
# the script updates in place (it keeps the previous payload for running
# daemons and prunes older ones). It never uses sudo.
#
# Every download is checked against the release SHA256SUMS. The newest
# release is also checked against the hash pinned in nix/release.json on
# main, so a tampered release asset fails the install.
set -eu

REPO="gildrb/eukhe"
RELEASES="https://github.com/${REPO}/releases"
RAW="https://raw.githubusercontent.com/${REPO}/main"

log()  { printf '%s\n' "$*"; }
warn() { printf 'warning: %s\n' "$*" >&2; }
die()  { printf 'error: %s\n' "$*" >&2; exit 1; }

usage() {
  cat <<EOF
Usage: install.sh [version]

Install the eukhe coding agent from the ${REPO} GitHub releases.
No root. macOS (Apple Silicon) and Linux (x64, arm64).

  version   pin one release (0.10.41, v0.10.41 or eukhe-v0.10.41);
            default: the newest release

Environment:
  EUKHE_INSTALL_ROOT     payload directory (default ~/.local/share/eukhe)
  EUKHE_INSTALL_BIN_DIR  launcher directory (default ~/.local/bin)
EOF
}

for arg in "$@"; do
  case "$arg" in
    -h|--help) usage; exit 0 ;;
    -*) usage >&2; die "unknown option: $arg" ;;
  esac
done
[ $# -le 1 ] || { usage >&2; die "at most one version argument"; }

command -v curl >/dev/null 2>&1 || die "curl is required"
command -v tar >/dev/null 2>&1 || die "tar is required"

fetch() {
  # fetch <url> <output-file>
  curl -fsSL --proto '=https' --tlsv1.2 --retry 3 --retry-delay 2 -o "$2" "$1"
}

# --- platform ----------------------------------------------------------
os="$(uname -s)"
machine="$(uname -m)"
case "$os" in
  Linux|Darwin) ;;
  *) die "unsupported OS '${os}': eukhe ships for Linux and macOS" ;;
esac
case "${os}:${machine}" in
  Linux:x86_64|Linux:amd64)   alias=linux-x64 ;;
  Linux:aarch64|Linux:arm64)  alias=linux-arm64 ;;
  Darwin:arm64|Darwin:aarch64) alias=darwin-arm64 ;;
  Darwin:*)
    die "no macOS build for '${machine}': eukhe is Apple Silicon only" ;;
  *)
    die "unsupported architecture '${machine}' on ${os}" ;;
esac

# --- version -----------------------------------------------------------
if [ $# -eq 1 ]; then
  case "$1" in
    eukhe-v*) version=${1#eukhe-v} ;;
    v*)       version=${1#v} ;;
    *)        version=$1 ;;
  esac
  printf '%s\n' "$version" | grep -Eq '^[0-9]+\.[0-9]+\.[0-9]+$' \
    || die "not a release version: '$1' (expected X.Y.Z)"
else
  # github.com/<repo>/releases/latest redirects to .../tag/<tag>.
  effective="$(curl -fsSL --proto '=https' --tlsv1.2 --retry 3 \
    -o /dev/null -w '%{url_effective}' "${RELEASES}/latest")" \
    || die "cannot resolve the newest release; pass a version (see --help)"
  tag="${effective##*/}"
  case "$tag" in
    eukhe-v*) version=${tag#eukhe-v} ;;
    *) die "newest release tag looks wrong: '${tag}'" ;;
  esac
fi
tag="eukhe-v${version}"
tarball="eukhe-${version}-${alias}.tar.gz"
base="${RELEASES}/download/${tag}"

# --- download ----------------------------------------------------------
work="$(mktemp -d "${TMPDIR:-/tmp}/eukhe-install.XXXXXX")"
trap 'rm -rf "$work"' EXIT INT TERM

log "eukhe ${version} for ${alias}"
log "downloading ${base}/${tarball}"
fetch "${base}/${tarball}" "${work}/${tarball}" \
  || die "download failed: ${tarball}"
fetch "${base}/SHA256SUMS" "${work}/SHA256SUMS" \
  || die "download failed: SHA256SUMS"

# --- verify ------------------------------------------------------------
expected="$(awk -v name="${tarball}" '$2 == name { print $1 }' "${work}/SHA256SUMS")"
[ -n "$expected" ] || die "${tarball} is not listed in SHA256SUMS"
if command -v sha256sum >/dev/null 2>&1; then
  actual="$(sha256sum "${work}/${tarball}" | awk '{print $1}')"
elif command -v shasum >/dev/null 2>&1; then
  actual="$(shasum -a 256 "${work}/${tarball}" | awk '{print $1}')"
else
  die "need sha256sum or shasum to verify the download"
fi
[ "$actual" = "$expected" ] || die "checksum mismatch for ${tarball}
  expected ${expected}
  actual   ${actual}"

# Cross-check against the hash the repository pins on main. The newest
# release must match; older pinned versions predate it.
json_version=""
if fetch "${RAW}/nix/release.json" "${work}/release.json"; then
  json_version="$(awk -F'"' '/^  "version":/ { print $4; exit }' "${work}/release.json")"
else
  warn "could not fetch nix/release.json: SHA256SUMS verification only"
fi
if [ -n "$json_version" ] && [ "$json_version" != "$version" ]; then
  log "pinned version ${version}: SHA256SUMS verified (nix/release.json holds ${json_version})"
elif [ -n "$json_version" ]; then
  pin_hash="$(awk -v name="${tarball}" \
    'index($0, name) && index($0, "\"url\"") {
       if ((getline next_line) > 0) {
         sub(/^.*"hash": "sha256-/, "", next_line)
         sub(/".*$/, "", next_line)
         print next_line
       }
     }' "${work}/release.json")"
  [ -n "$pin_hash" ] || die "nix/release.json ${version} has no hash for ${tarball}"
  if command -v openssl >/dev/null 2>&1; then
    pin_actual="$(openssl dgst -sha256 -binary "${work}/${tarball}" | openssl base64 -A)"
    [ "$pin_actual" = "$pin_hash" ] || die "hash differs from nix/release.json on main
  expected ${pin_hash}
  actual   ${pin_actual}"
    log "verified against SHA256SUMS and nix/release.json"
  else
    warn "openssl not found: skipped the nix/release.json cross-check (SHA256SUMS still enforced)"
  fi
fi

# --- install -----------------------------------------------------------
root="${EUKHE_INSTALL_ROOT:-${HOME}/.local/share/eukhe}"
bin_dir="${EUKHE_INSTALL_BIN_DIR:-${HOME}/.local/bin}"
payload="${root}/eukhe-${version}"
stage="${root}/.stage-eukhe-${version}.$$"

mkdir -p "${root}" "${bin_dir}" "${stage}"
tar -xzf "${work}/${tarball}" -C "${stage}" || die "extract failed"
[ -x "${stage}/eukhe" ] || die "the tarball has no eukhe binary"

# Livecheck before anything is replaced, as the release workflow does.
reported="$("${stage}/eukhe" --version)" || die "the downloaded binary does not run on this machine"
[ "$reported" = "$version" ] || die "binary reports '${reported}', expected '${version}'"

if [ -d "$payload" ] && [ "$("${payload}/eukhe" --version 2>/dev/null)" = "$version" ]; then
  # Same release already installed: keep it in place (a running daemon
  # still reads its files) and drop the fresh copy.
  rm -rf "${stage}"
  log "eukhe ${version} is already installed: kept ${payload}"
else
  [ ! -d "$payload" ] || rm -rf "$payload"
  mv "${stage}" "${payload}"
fi

wrapper="${bin_dir}/eukhe"
wrapper_tmp="${bin_dir}/.eukhe-installer.$$"
{
  printf '#!/bin/sh\n'
  printf '# eukhe launcher written by install.sh; the payload sits beside itself\n'
  printf 'exec "%s/eukhe" "$@"\n' "${payload}"
} > "${wrapper_tmp}"
chmod 755 "${wrapper_tmp}"
mv -f "${wrapper_tmp}" "${wrapper}"

# Prune superseded payloads; keep the current one and the one before it
# (a daemon may still run from the previous version).
for dir in "$root"/eukhe-*; do
  [ -d "$dir" ] || continue
  [ "$dir" = "$payload" ] && continue
  v="${dir##*/eukhe-}"
  printf '%s\t%s\n' "$v" "$dir"
done | sort -t. -k1,1n -k2,2n -k3,3n | sed '$d' | while IFS= read -r line; do
  rm -rf "${line#*	}"
done

# --- guidance ----------------------------------------------------------
case ":${PATH}:" in
  *":${bin_dir}:"*) ;;
  *)
    warn "${bin_dir} is not on your PATH"
    log ""
    log "  add it, then reopen your shell:"
    log "    export PATH=\"${bin_dir}:\$PATH\"   # put this line in your shell profile"
    ;;
esac
if other="$(command -v eukhe 2>/dev/null)" && [ "$other" != "$wrapper" ]; then
  warn "another eukhe is first on PATH: ${other} (this install: ${wrapper})"
fi
for dep in uv git; do
  command -v "$dep" >/dev/null 2>&1 && continue
  [ "$dep" = "uv" ] && [ -x "${HOME}/.local/bin/uv" ] && continue
  if [ "$dep" = "uv" ]; then
    warn "uv not found: the Python kernel needs it (macOS: brew install uv; Linux: https://docs.astral.sh/uv/)"
  else
    warn "git not found: chat memory commits need it (macOS: brew install git)"
  fi
done

log ""
log "installed eukhe ${version}"
log "  payload:  ${payload}"
log "  launcher: ${wrapper}"
log ""
log "next: run 'eukhe' in a project, then /login on first launch"
log "update: re-run this command; uninstall: 'eukhe shutdown', then remove the two paths above"
