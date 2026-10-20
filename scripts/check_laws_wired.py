#!/usr/bin/env python3
"""check_laws_wired.py [ROOT]: every laws/*.bend is imported by LAWS.bend, and
every `law NAME` of it has a fill `def <Alias>.NAME(` in some file of the
PROOF.bend import closure, where <Alias> is the name that file gives the law
module. Exit 1 with the list of gaps."""
import re
import sys
from pathlib import Path

IMPORT = re.compile(r"^import\s+(\S+\.bend)\s+as\s+(\S+)", re.M)

root = Path(sys.argv[1] if len(sys.argv) > 1 else ".").resolve()
laws_imports = {
    (root / p).resolve() for p, _ in IMPORT.findall((root / "LAWS.bend").read_text())
}

# The PROOF.bend import closure: (file, {resolved import path: alias}).
closure: dict[Path, dict[Path, str]] = {}
todo = [(root / "PROOF.bend").resolve()]
while todo:
    f = todo.pop()
    if f in closure or not f.exists():
        continue
    aliases = {(f.parent / p).resolve(): a for p, a in IMPORT.findall(f.read_text())}
    closure[f] = aliases
    todo.extend(aliases)

gaps = []
for law_file in sorted((root / "laws").glob("*.bend")):
    lf = law_file.resolve()
    rel = law_file.relative_to(root).as_posix()
    if lf not in laws_imports:
        gaps.append(f"{rel}: not imported by LAWS.bend")
        continue
    filled: set[str] = set()
    for f, aliases in closure.items():
        a = aliases.get(lf)
        if a:
            filled |= set(re.findall(rf"^def {re.escape(a)}\.(\w+)\(", f.read_text(), re.M))
    for n in re.findall(r"^law (\w+)", law_file.read_text(), re.M):
        if n not in filled:
            gaps.append(f"{rel}: law {n} has no fill in the PROOF.bend import closure")
print("\n".join(gaps) if gaps else "every law file is imported and every law is filled")
sys.exit(1 if gaps else 0)
