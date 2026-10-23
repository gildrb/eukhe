# eukhe: the proof of LAW move_never_overwrites

import Base
import ../../bend/doc_commit.bend as Cm
import ../../laws/doc_commit.bend as DocCommit

# Move
# ----

# the law move_never_overwrites
def pc.move_taken(+s: Nat, +t: Nat, +es: List<&2, Cm.Entry>, taken: {Cm.has(t, es) == True{} : Bool}) -> {Cm.move(s, t, es) == Cm.Mv{False{}, es} : Cm.Mv}:
  %Equal.sym(Bool, Cm.has(t, es), True{}, taken) : {Cm.move.go(s, t, _, es) == Cm.Mv{False{}, es} : Cm.Mv}
  {==}

# (F5) A move

def DocCommit.move_never_overwrites(s, t, es, taken):
  pc.move_taken(s, t, es, taken)
