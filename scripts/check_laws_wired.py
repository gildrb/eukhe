#!/usr/bin/env python3
"""check_laws_wired.py [ROOT]: the layout of the laws (AGENTS.md, Tests).

Every law lives in LAWS.bend and every proof and proof lemma in PROOF.bend
or in a file of proof/ that PROOF.bend imports (the Bend Bank layout:
proof/<law>.bend per law, proof/base.bend for shared lemmas):
- PROOF.bend imports LAWS.bend, and every `law NAME` of LAWS.bend has a fill
  `def <Alias>.NAME(` in PROOF.bend or in a proof/ file PROOF.bend imports,
  where <Alias> is that file's name for LAWS.bend;
- there is no laws/ directory and no proof*.bend file but PROOF.bend;
- no .bend file but LAWS.bend declares a `law`;
- no .bend file but PROOF.bend and the proof/ files it imports fills a law
  of LAWS.bend.
Exit 1 with the list of gaps."""
import re
import subprocess
import sys
from pathlib import Path

IMPORT = re.compile(r"^import\s+(\S+\.bend)\s+as\s+(\S+)", re.M)
LAW = re.compile(r"^law (\w+)", re.M)
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


def laws_alias(text: str, path: Path, laws_path: Path) -> str | None:
    """The name `text` (the file at `path`) gives LAWS.bend, if it imports it."""
    return next(
        (a for p, a in IMPORT.findall(text) if (path.parent / p).resolve() == laws_path),
        None,
    )


def fills_of(text: str, alias: str) -> set[str]:
    return set(re.findall(rf"^def {re.escape(alias)}\.(\w+)\(", text, re.M))


def gaps_of(root: Path) -> list[str]:
    root = root.resolve()
    laws_path = (root / "LAWS.bend").resolve()
    proof_path = (root / "PROOF.bend").resolve()
    gaps = []
    if (root / "laws").exists():
        gaps.append("laws/: every law lives in LAWS.bend; remove the directory")
    if not laws_path.exists() or not proof_path.exists():
        return gaps + ["LAWS.bend and PROOF.bend must both exist at the root"]
    laws = set(LAW.findall(laws_path.read_text()))
    proof = proof_path.read_text()
    proof_dir = (root / "proof").resolve()
    # the proof/ files PROOF.bend imports: they may fill laws
    proof_files = {
        (root / p).resolve()
        for p, _ in IMPORT.findall(proof)
        if (root / p).resolve().parent == proof_dir
    }

    filled = set()
    for f in bend_files(root):
        rf = f.resolve()
        if rf in (laws_path, proof_path):
            continue
        rel = f.relative_to(root).as_posix()
        text = f.read_text()
        if f.name.lower().startswith("proof"):
            gaps.append(f"{rel}: every proof and proof lemma lives in PROOF.bend")
        for n in LAW.findall(text):
            gaps.append(f"{rel}: declares law {n}; every law lives in LAWS.bend")
        alias = laws_alias(text, f, laws_path)
        if alias is None:
            continue
        for n in sorted(fills_of(text, alias) & laws):
            if rf in proof_files:
                filled.add(n)
            else:
                gaps.append(f"{rel}: proves law {n}; every proof lives in PROOF.bend or a proof/ file it imports")

    alias = laws_alias(proof, proof_path, laws_path)
    if alias is None:
        return gaps + ["PROOF.bend: does not import ./LAWS.bend"]
    filled |= fills_of(proof, alias)
    for n in sorted(laws - filled):
        gaps.append(f"LAWS.bend: law {n} has no fill def {alias}.{n}( in PROOF.bend or a proof/ file it imports")
    return gaps


if __name__ == "__main__":
    gaps = gaps_of(Path(sys.argv[1] if len(sys.argv) > 1 else "."))
    print("\n".join(gaps) if gaps else "every law is in LAWS.bend and proven in PROOF.bend")
    sys.exit(1 if gaps else 0)
