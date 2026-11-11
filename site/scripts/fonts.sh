#!/usr/bin/env bash
# Puts Paper Mono's release files in public/fonts, unmodified (no subsetting, no renaming: the
# OFL's Reserved Font Name question never arises): the two weights the site sets (Regular 400,
# Bold 700) and the release's OFL.txt. The checksums are those files at the pinned release; a new
# release changes them here and `?v=` in src/render.tsx.
set -euo pipefail
cd "$(dirname "$0")/.."
version=v1.000
work="$(mktemp -d)"
trap 'rm -rf "$work"' EXIT
gh release download "$version" -R paper-design/paper-mono -p "paper-mono-$version.zip" -D "$work"
unzip -q "$work/paper-mono-$version.zip" -d "$work"
release="$work/paper-mono-$version"
cp "$release/fonts/webfonts/PaperMono-Regular.woff2" "$release/fonts/webfonts/PaperMono-Bold.woff2" \
  "$release/OFL.txt" public/fonts/
shasum -a 256 -c - <<'EOF'
ebfbaa0f177a172a207b38dc5708f6e0b648f75cd3fa523d5097380fa2a707f0  public/fonts/PaperMono-Regular.woff2
2a7bfa7f29e15ab37a463bae8d7a953cdf8728664a77b759e211f58ab07be258  public/fonts/PaperMono-Bold.woff2
ae8bcaf5a046be7e096b5710a8532cdaa5a299462e182752b805dcfa44370e4c  public/fonts/OFL.txt
EOF
