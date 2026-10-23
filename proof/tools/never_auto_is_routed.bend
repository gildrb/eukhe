# eukhe: the proof of LAW never_auto_is_routed

import Base
import ../../LAWS.bend as Laws
import ./base.bend as LA

def Laws.never_auto_is_routed(auto, es, c, has, held, ds):
  LA.pa.never_auto(auto, es, c, has, held, ds)
