# eukhe: the proof of LAW rmw_applies_change

import Base
import ../../bend/config.bend as Cf
import ../../laws/config.bend as Config
import ./base/config.bend as LA

# LAW rmw_applies_change
def Config.rmw_applies_change(d, k, v):
  LA.pcf.set_hit(d, k, v)
