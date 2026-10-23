# eukhe: the proof of LAW never_auto_is_routed

import Base
import ../../laws/tools.bend as Tools
import ./base.bend as LA

def Tools.never_auto_is_routed(auto, es, c, has, held, ds):
  LA.pa.never_auto(auto, es, c, has, held, ds)
