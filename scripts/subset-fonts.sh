#!/usr/bin/env bash
# Rebuilds public/fonts from Ioskeley Mono's full web release: Latin, Greek and polytonic Greek,
# punctuation, arrows, box drawing. Bump `?v=` in src/render.tsx after a change.
set -euo pipefail
version=v2.2.0
work="$(mktemp -d)"
trap 'rm -rf "$work"' EXIT
gh release download "$version" -R ahatem/IoskeleyMono -p IoskeleyMono-Web-Full.zip -D "$work"
unzip -q "$work/IoskeleyMono-Web-Full.zip" -d "$work"
for weight in Regular Bold; do
  nix shell --impure --expr 'with import <nixpkgs> {}; python3.withPackages (p: [p.fonttools p.brotli])' -c \
    pyftsubset "$work/WOFF2/IoskeleyMono-$weight.woff2" \
    --unicodes='U+0000-00FF,U+0131,U+0152-0153,U+02C6,U+02DA,U+02DC,U+0300-036F,U+0370-03FF,U+1F00-1FFF,U+2000-206F,U+20AC,U+2122,U+2190-21FF,U+2500-259F' \
    --layout-features='*' --flavor=woff2 \
    --output-file="public/fonts/IoskeleyMono-$weight.woff2"
done
