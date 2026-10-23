# eukhe: the proof of LAW write_never_loses_unseen

import Base
import ../../bend/doc_commit.bend as Cm
import ../../laws/doc_commit.bend as DocCommit

# Write
# -----

# the law write_never_loses_unseen
def pc.write_refused(+d: Maybe<&2, Nat>, +s: List<&2, Nat>, +c: Nat, lost: {Cm.unseen(d, s) == True{} : Bool}) -> {Cm.write(d, s, c) == Cm.Wt{False{}, d, s} : Cm.Wt}:
  %Equal.sym(Bool, Cm.unseen(d, s), True{}, lost) : {Cm.write.go(_, d, s, c) == Cm.Wt{False{}, d, s} : Cm.Wt}
  {==}

# (F2) The write tool

def DocCommit.write_never_loses_unseen(d, s, c, lost):
  pc.write_refused(d, s, c, lost)
