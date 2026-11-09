# eukhe: the proof of LAW replace_lt_irreflexive
#
# PROOF of LAW replace_lt_irreflexive: by induction on the rank, each
# number equal to itself (LAReplace.pr.lt_irrefl).

import Base
import ../../laws/replace.bend as Replace
import ./base.bend as LAReplace

def Replace.replace_lt_irreflexive(xs):
  LAReplace.pr.lt_irrefl(xs)
