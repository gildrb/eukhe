# eukhe: the proof of LAW replace_relation_exact

import Base
import ../../laws/replace.bend as Replace
import ./base.bend as LA

def Replace.replace_relation_exact(c, d):
  LA.rk.relation_exact(c, d)
