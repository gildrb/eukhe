# eukhe: the proof of LAW replace_never_downgrades_spec
#
# PROOF of LAW replace_never_downgrades_spec: the spec order of the
# daemons is the model's never_back (replace_never_back_exact), which
# replace_never_downgrades proves True.

import Base
import ../../bend/replace.bend as Rp
import ../../laws/replace.bend as Replace
import ./replace_never_back_exact.bend as PReplaceNeverBackExact
import ./replace_never_downgrades.bend as PReplaceNeverDowngrades

def rnd.go(+ss: List<&2, Rp.Start>) -> {Replace.rp_never_back_spec(Rp.daemons(ss)) == True{} : Bool}:
  %Replace.replace_never_back_exact(Rp.daemons(ss)) : {_ == True{} : Bool}
  Replace.replace_never_downgrades(ss)

def Replace.replace_never_downgrades_spec(ss):
  rnd.go(ss)
