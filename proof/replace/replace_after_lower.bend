# eukhe: the proof of LAW replace_after_lower: other build ids and a lower
# daemon make the relation Older, whose verdict on an interactive start is
# Replace: the client's build

import Base
import ../../bend/replace.bend as Rp
import ../../laws/replace.bend as Replace

def ral.go(+rc: List<&2, Nat>, +ic: String, +rb: List<&2, Nat>, +ib: String, other: {String.eq(ic, ib) == False{} : Bool}, lower: {Rp.lt(rb, rc) == True{} : Bool}) -> {Rp.after(Rp.Start{Rp.Build{rc, ic}, Rp.Interactive{}}, Some{Rp.Build{rb, ib}}) == Rp.Build{rc, ic} : Rp.Build}:
  %Equal.sym(Bool, String.eq(ic, ib), False{}, other) : {Rp.after.put(Rp.verdict.put(Rp.rel.put(_, Rp.lt(rb, rc), Rp.lt(rc, rb)), Rp.Interactive{}), Rp.Build{rc, ic}, Rp.Build{rb, ib}) == Rp.Build{rc, ic} : Rp.Build}
  %Equal.sym(Bool, Rp.lt(rb, rc), True{}, lower) : {Rp.after.put(Rp.verdict.put(Rp.rel.put(False{}, _, Rp.lt(rc, rb)), Rp.Interactive{}), Rp.Build{rc, ic}, Rp.Build{rb, ib}) == Rp.Build{rc, ic} : Rp.Build}
  {==}

def Replace.replace_after_lower(rc, ic, rb, ib, other, lower):
  ral.go(rc, ic, rb, ib, other, lower)
