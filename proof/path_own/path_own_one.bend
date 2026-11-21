# eukhe: the proof of LAW path_own_one
#
# PROOF: one rule answers Own at place 0 when it names the path, else the
# judge's class (LA.po.one, by the rule's test).

import Base
import ../../bend/path_own.bend as Po
import ../../laws/path_own.bend as PathOwn
import ./base.bend as LA

def PathOwn.path_own_one(r, at, c):
  LA.po.one(Po.names(r, at), c)
