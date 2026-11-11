# eukhe: the proof of LAW replace_after_same_build: equal build ids make
# the relation Same, whose verdict keeps the daemon for every caller

import Base
import ../../bend/replace.bend as Rp
import ../../laws/replace.bend as Replace

def ras.go(+rc: List<&2, Nat>, +ic: String, +rb: List<&2, Nat>, +ib: String, +k: Rp.Caller, same: {String.eq(ic, ib) == True{} : Bool}) -> {Rp.after(Rp.Start{Rp.Build{rc, ic}, k}, Some{Rp.Build{rb, ib}}) == Rp.Build{rb, ib} : Rp.Build}:
  %Equal.sym(Bool, String.eq(ic, ib), True{}, same) : {Rp.after.put(Rp.verdict.put(Rp.rel.put(_, Rp.lt(rb, rc), Rp.lt(rc, rb)), k), Rp.Build{rc, ic}, Rp.Build{rb, ib}) == Rp.Build{rb, ib} : Rp.Build}
  {==}

def Replace.replace_after_same_build(rc, ic, rb, ib, k, same):
  ras.go(rc, ic, rb, ib, k, same)
