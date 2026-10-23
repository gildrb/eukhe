#!/usr/bin/env python3
"""check_laws_wired.py [ROOT]: the layout of the laws (AGENTS.md, Tests).

Every law lives in LAWS.bend or in a file of laws/ that LAWS.bend imports,
and every proof and proof lemma in a file of proof/ that PROOF.bend
imports (the Bend Bank layout: proof/<area>/<law>.bend per law,
proof/<area>/base.bend and proof/base.bend for shared lemmas):
- PROOF.bend imports LAWS.bend and holds no def;
- every law has a fill `def <Alias>.NAME(` in a proof/ file PROOF.bend
  imports, where <Alias> is that file's name for the law's file;
- a file proof/<area>/<x>.bend but base.bend fills law <x>; when <x> lives
  in laws/<a>.bend, <area> is <a>;
- no laws/ file but those LAWS.bend imports; no proof*.bend file but
  PROOF.bend;
- no other .bend file declares a `law` or fills one.
Exit 1 with the list of gaps."""
import re
import subprocess
import sys
from pathlib import Path

IMPORT = re.compile(r"^import\s+(\S+\.bend)\s+as\s+(\S+)", re.M)
LAW = re.compile(r"^law (\w+)", re.M)
DEF = re.compile(r"^def ", re.M)
SKIP = {".git", "target", "node_modules", "vendor"}


def bend_files(root: Path) -> list[Path]:
    """Every .bend file of the tree: tracked and untracked, not ignored."""
    try:
        out = subprocess.run(
            ["git", "ls-files", "-co", "--exclude-standard", "--", "*.bend"],
            cwd=root, capture_output=True, text=True, check=True,
        ).stdout
        return sorted(root / p for p in out.splitlines() if (root / p).exists())
    except (OSError, subprocess.CalledProcessError):
        return sorted(
            p for p in root.rglob("*.bend") if not SKIP & set(p.relative_to(root).parts)
        )


def imports(text: str, path: Path) -> dict[Path, str]:
    """The files `text` (the file at `path`) imports, with their aliases."""
    return {(path.parent / p).resolve(): a for p, a in IMPORT.findall(text)}


def fills_of(text: str, alias: str) -> set[str]:
    return set(re.findall(rf"^def {re.escape(alias)}\.(\w+)\(", text, re.M))


def gaps_of(root: Path) -> list[str]:
    root = root.resolve()
    laws_path = (root / "LAWS.bend").resolve()
    proof_path = (root / "PROOF.bend").resolve()
    laws_dir = (root / "laws").resolve()
    proof_dir = (root / "proof").resolve()
    gaps = []
    if not laws_path.exists() or not proof_path.exists():
        return gaps + ["LAWS.bend and PROOF.bend must both exist at the root"]
    # the files that may declare laws: LAWS.bend and the laws/ files it imports
    law_files = [laws_path] + [p for p in imports(laws_path.read_text(), laws_path) if p.parent == laws_dir]
    home = {}  # law -> the file that declares it
    for lf in law_files:
        if not lf.exists():
            continue
        for n in LAW.findall(lf.read_text()):
            home[n] = lf
    proof = proof_path.read_text()
    if laws_path not in imports(proof, proof_path):
        gaps.append("PROOF.bend: does not import ./LAWS.bend")
    if DEF.search(proof):
        gaps.append("PROOF.bend: holds a def; it only imports the proof/ files")
    # the proof/ files PROOF.bend imports: they may fill laws
    proof_files = {p for p in imports(proof, proof_path) if proof_dir in p.parents}

    filled = set()
    for f in bend_files(root):
        rf = f.resolve()
        if rf in (laws_path, proof_path):
            continue
        rel = f.relative_to(root).as_posix()
        text = f.read_text()
        if rf.parent == laws_dir and rf not in law_files:
            gaps.append(f"{rel}: LAWS.bend does not import it")
        if f.name.lower().startswith("proof"):
            gaps.append(f"{rel}: every proof and proof lemma lives in a proof/ file")
        if rf not in law_files:
            for n in LAW.findall(text):
                gaps.append(f"{rel}: declares law {n}; every law lives in LAWS.bend or laws/")
        mine = set()
        for p, alias in imports(text, f).items():
            if p in law_files:
                mine |= {n for n in fills_of(text, alias) if home.get(n) == p}
        for n in sorted(mine):
            if rf in proof_files:
                filled.add(n)
            else:
                gaps.append(f"{rel}: proves law {n}; every proof lives in a proof/ file PROOF.bend imports")
        if rf in proof_files and rf.parent != proof_dir and rf.stem != "base":
            law = rf.stem
            if law not in mine:
                gaps.append(f"{rel}: does not fill law {law}")
            elif home[law].parent == laws_dir and home[law].stem != rf.parent.name:
                gaps.append(f"{rel}: law {law} lives in laws/{home[law].stem}.bend; its proof in proof/{home[law].stem}/")
    for n in sorted(set(home) - filled):
        gaps.append(f"{home[n].relative_to(root).as_posix()}: law {n} has no fill in a proof/ file PROOF.bend imports")
    return gaps


if __name__ == "__main__":
    gaps = gaps_of(Path(sys.argv[1] if len(sys.argv) > 1 else "."))
    print("\n".join(gaps) if gaps else "every law is in LAWS.bend or laws/ and proven in proof/")
    sys.exit(1 if gaps else 0)
