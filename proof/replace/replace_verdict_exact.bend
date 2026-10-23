# eukhe: the proof of LAW replace_verdict_exact

import Base
import ../../bend/replace.bend as Rp
import ../../laws/replace.bend as Replace
import ./base.bend as LA

def rk.verdict_put(r: Rp.Rel, k: Rp.Caller) -> {Rp.verdict.put(r, k) == Replace.verdict_spec(r, k) : Rp.Verdict}:
  match r k:
    case Rp.Same{} Rp.Interactive{}:
      {==}
    case Rp.Same{} Rp.Background{}:
      {==}
    case Rp.Older{} Rp.Interactive{}:
      {==}
    case Rp.Older{} Rp.Background{}:
      {==}
    case Rp.Newer{} Rp.Interactive{}:
      {==}
    case Rp.Newer{} Rp.Background{}:
      {==}
    case Rp.Other{} Rp.Interactive{}:
      {==}
    case Rp.Other{} Rp.Background{}:
      {==}

def rk.verdict_exact(+c: Rp.Build, +d: Rp.Build, +k: Rp.Caller) -> {Rp.verdict(c, d, k) == Replace.verdict_spec(Replace.rel_spec(c, d), k) : Rp.Verdict}:
  %LA.rk.relation_exact(c, d) : {Rp.verdict.put(Rp.relation(c, d), k) == Replace.verdict_spec(_, k) : Rp.Verdict}
  rk.verdict_put(Rp.relation(c, d), k)

def Replace.replace_verdict_exact(c, d, k):
  rk.verdict_exact(c, d, k)
