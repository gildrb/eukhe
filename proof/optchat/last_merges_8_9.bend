# eukhe: the proof of LAW last_merges_8_9

import Base
import ../../bend/optchat.bend as O
import ../../bend/spec.bend as S
import ../../LAWS.bend as Laws

# ---- push ----

# proof_push: the bounded laws, proven by computation. push_agrees is
# split into chunks so each conversion stays inside the kernel's fuel.

# First is not last
# -----------------

def last_merges_8_9() -> {O.fit.view(O.Last{}, S.ten(), 3n, 0n, O.All{1n}, S.view10()) == [O.Node{2n, []}, O.Node{2n, [True{}]}, O.Node{1n, [False{}, False{}, True{}]}] : List<&2, O.Node>}:
  {==}

# (f) First is not last

def Laws.last_merges_8_9():
  last_merges_8_9()
