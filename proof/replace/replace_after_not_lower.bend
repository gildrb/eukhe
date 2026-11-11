# eukhe: the proof of LAW replace_after_not_lower: a daemon not below the
# client is never Older, so every relation it can have (Same, Newer,
# Other) keeps it, for every caller (ran.keep)

import Base
import ../../bend/replace.bend as Rp
import ../../laws/replace.bend as Replace

def ran.keep(same: Bool, newer: Bool, k: Rp.Caller, -c: Rp.Build, -b: Rp.Build) -> {Rp.after.put(Rp.verdict.put(Rp.rel.put(same, False{}, newer), k), c, b) == b : Rp.Build}:
  match same newer:
    case True{} True{}:
      {==}
    case True{} False{}:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      {==}

def ran.go(+rc: List<&2, Nat>, +ic: String, +rb: List<&2, Nat>, +ib: String, +k: Rp.Caller, keep: {Rp.lt(rb, rc) == False{} : Bool}) -> {Rp.after(Rp.Start{Rp.Build{rc, ic}, k}, Some{Rp.Build{rb, ib}}) == Rp.Build{rb, ib} : Rp.Build}:
  %Equal.sym(Bool, Rp.lt(rb, rc), False{}, keep) : {Rp.after.put(Rp.verdict.put(Rp.rel.put(String.eq(ic, ib), _, Rp.lt(rc, rb)), k), Rp.Build{rc, ic}, Rp.Build{rb, ib}) == Rp.Build{rb, ib} : Rp.Build}
  ran.keep(String.eq(ic, ib), Rp.lt(rc, rb), k, Rp.Build{rc, ic}, Rp.Build{rb, ib})

def Replace.replace_after_not_lower(rc, ic, rb, ib, k, keep):
  ran.go(rc, ic, rb, ib, k, keep)
