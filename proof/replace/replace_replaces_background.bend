# eukhe: the proof of LAW replace_replaces_background
#
# PROOF of LAW replace_replaces_background: no daemon counts 0; on a
# running daemon, a background start's verdict is a Keep whatever the
# relation (rrb.put).

import Base
import ../../bend/replace.bend as Rp
import ../../laws/replace.bend as Replace

def rrb.put(r: Rp.Rel) -> {Rp.replaces.put(Rp.verdict.put(r, Rp.Background{})) == 0n : Nat}:
  match r:
    case Rp.Same{}:
      {==}
    case Rp.Older{}:
      {==}
    case Rp.Newer{}:
      {==}
    case Rp.Other{}:
      {==}

def Replace.replace_replaces_background(c, d):
  match d:
    case None{}:
      {==}
    case Some{+b}:
      rrb.put(Rp.relation(c, b))
