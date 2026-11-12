#!/bin/sh
# The site's laws (LAWS.bend, laws/vim/), its own and apart from Eukhe's: every proof
# PROOF.bend imports checks, by the checker and by Lean (`--verdict`, Lean as
# ../scripts/toolchain.env pins it), with the repository's pinned Bend
# (../scripts/pinned_bend.sh); then LAWS.lock holds the laws as they are (the bend skill's
# `gate.py --lock-only`; BEND_SKILL: the skill directory, default ~/.agents/skills/bend).
set -eu
cd "$(dirname "$0")/.."
bend="$(../scripts/pinned_bend.sh)"
for flag in "" --verdict; do
  out="$("$bend" PROOF.bend $flag)"
  printf '%s\n' "$out"
  printf '%s\n' "$out" | grep -qx 'ALL PROOFS CHECK'
done
python3 "${BEND_SKILL:-$HOME/.agents/skills/bend}/scripts/gate.py" . --lock-only
