# eukhe: the proof of LAW merge_find_exact

import Base
import ../../bend/config.bend as Cf
import ../../laws/config.bend as Config
import ../../spec/config_rules.bend as CR
import ./base/config.bend as LA

def Config.merge_find_exact(g, p, n):
  LA.pcf.mf.merged(g, p, n)
