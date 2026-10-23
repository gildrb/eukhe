# eukhe: the proof of LAW write_writes_seen

import Base
import ../../bend/doc_commit.bend as Cm
import ../../laws/doc_commit.bend as DocCommit

# the law write_writes_seen
def pc.write_writes(+d: Maybe<&2, Nat>, +s: List<&2, Nat>, +c: Nat, kept: {Cm.unseen(d, s) == False{} : Bool}) -> {Cm.write(d, s, c) == Cm.Wt{True{}, Some{c}, Cm.saw(c, s)} : Cm.Wt}:
  %Equal.sym(Bool, Cm.unseen(d, s), False{}, kept) : {Cm.write.go(_, d, s, c) == Cm.Wt{True{}, Some{c}, Cm.saw(c, s)} : Cm.Wt}
  {==}

def DocCommit.write_writes_seen(d, s, c, kept):
  pc.write_writes(d, s, c, kept)
