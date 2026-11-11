# eukhe: the proof of LAW slot_exact

import Base
import ../../bend/config.bend as Cf
import ../../laws/config.bend as Config
import ../../spec/settings/config_rules.bend as CR
import ./base/config.bend as LA

def Config.slot_exact(es, p):
  LA.pcf.slot(es, p)
