#!/usr/bin/env bash
# The release toolchain image (scripts/release/Dockerfile), run by
# .github/workflows/build-image.yml: one `push` per architecture on a native
# runner, then `merge`.
#
#   build_image.sh build <tag>  build ${IMAGE}:<tag>-<arch> for this machine's
#                               architecture and print the installed packages
#   build_image.sh push <tag>   build, then push ${IMAGE}:<tag>-<arch>
#   build_image.sh merge <tag>  ${IMAGE}:<tag> = the amd64 + arm64 images;
#                               prints the multi-arch digest to pin
#
# <tag> is jammy-<YYYYMMDD>; IMAGE defaults to ghcr.io/gildrb/eukhe-build.
# push and merge need `docker login ghcr.io` first.
set -euo pipefail

usage() { echo "usage: $0 build|push|merge jammy-<YYYYMMDD>" >&2; exit 2; }
[[ $# -eq 2 ]] || usage
mode="$1" tag="$2"
[[ "${tag}" =~ ^jammy-[0-9]{8}$ ]] || usage
image="${IMAGE:-ghcr.io/gildrb/eukhe-build}"
dockerfile="$(dirname "$0")/Dockerfile"

build() {
  local arch
  arch="$(docker version --format '{{.Server.Arch}}')"
  case "${arch}" in amd64 | arm64) ;; *) echo "unsupported architecture ${arch}" >&2; exit 1 ;; esac
  ref="${image}:${tag}-${arch}"
  # No cache and a fresh base: the image holds exactly what the Dockerfile
  # installs today. No provenance/SBOM manifests: a plain image per arch.
  docker buildx build --pull --no-cache --provenance=false --sbom=false \
    --platform "linux/${arch}" --load -t "${ref}" - < "${dockerfile}"
  echo "${ref}: apt source $(docker run --rm "${ref}" cat /usr/share/eukhe-build/source)"
  echo "${ref}: installed packages"
  docker run --rm "${ref}" cat /usr/share/eukhe-build/packages.txt
}

case "${mode}" in
  build) build ;;
  push)
    build
    docker push "${ref}"
    ;;
  merge)
    docker buildx imagetools create -t "${image}:${tag}" "${image}:${tag}-amd64" "${image}:${tag}-arm64"
    digest="$(docker buildx imagetools inspect "${image}:${tag}" | awk '$1 == "Digest:" { print $2; exit }')"
    [[ "${digest}" == sha256:* ]] || { echo "no digest for ${image}:${tag}" >&2; exit 1; }
    echo "pin: ${image}:${tag}@${digest}"
    [[ -z "${GITHUB_STEP_SUMMARY:-}" ]] || echo "pin: \`${image}:${tag}@${digest}\`" >> "${GITHUB_STEP_SUMMARY}"
    ;;
  *) usage ;;
esac
