# eukhe: the proof of LAW background_never_replaces

import Base
import ../../bend/replace.bend as Rp
import ../../laws/replace.bend as Replace

# (D1) background_never_replaces
# ------------------------------

def pr.bg(r: Rp.Rel, -c: Rp.Build, -d: Rp.Build) -> {Rp.after.put(Rp.verdict.put(r, Rp.Background{}), c, d) == d : Rp.Build}:
  match r:
    case Rp.Same{}:
      {==}
    case Rp.Older{}:
      {==}
    case Rp.Newer{}:
      {==}
    case Rp.Other{}:
      {==}

def pr.background_never_replaces(+c: Rp.Build, +d: Rp.Build) -> {Rp.after(Rp.Start{c, Rp.Background{}}, Some{d}) == d : Rp.Build}:
  pr.bg(Rp.relation(c, d), c, d)

def Replace.background_never_replaces(c, d):
  pr.background_never_replaces(c, d)
