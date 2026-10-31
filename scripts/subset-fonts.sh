#!/usr/bin/env bash
# Rebuilds public/fonts from Ioskeley Mono's full web release, three files per weight, each with a
# unicode-range in src/render.tsx so a page loads only the ranges it shows:
#   core:  Latin, punctuation, symbols the page text uses
#   greek: Greek and polytonic Greek, combining marks
#   box:   arrows, box drawing, blocks (the pickers' borders, the COLORS swatches)
# Bump `?v=` in src/render.tsx after a change.
set -euo pipefail
version=v2.2.0
work="$(mktemp -d)"
trap 'rm -rf "$work"' EXIT
gh release download "$version" -R ahatem/IoskeleyMono -p IoskeleyMono-Web-Full.zip -D "$work"
unzip -q "$work/IoskeleyMono-Web-Full.zip" -d "$work"
declare -A ranges=(
  [core]='U+0000-00FF,U+0131,U+0152-0153,U+02C6,U+02DA,U+02DC,U+2000-206F,U+20AC,U+2122'
  [greek]='U+0300-036F,U+0370-03FF,U+1F00-1FFF'
  [box]='U+2190-21FF,U+2500-259F'
)
for weight in Regular Bold; do
  for part in core greek box; do
    nix shell --impure --expr 'with import <nixpkgs> {}; python3.withPackages (p: [p.fonttools p.brotli])' -c \
      pyftsubset "$work/WOFF2/IoskeleyMono-$weight.woff2" \
      --unicodes="${ranges[$part]}" \
      --layout-features='*' --flavor=woff2 \
      --output-file="public/fonts/IoskeleyMono-$weight-$part.woff2"
  done
done
