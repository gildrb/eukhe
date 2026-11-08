# eukhe: the proof of LAW find_exact

import Base
import ../../bend/config.bend as Cf
import ../../laws/config.bend as Config
import ../../spec/settings/config_rules.bend as CR
import ./base/config.bend as LA

def Config.find_exact(es, n):
  LA.pcf.mf.find(es, n)
