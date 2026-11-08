# eukhe: the proof of LAW limit_exact
# The one-provider step of limits_exact (LA.pcf.limit).

import Base
import ../../bend/config.bend as Cf
import ../../laws/config.bend as Config
import ../../spec/settings/config_rules.bend as CR
import ./base/config.bend as LA

def Config.limit_exact(s, p):
  LA.pcf.limit(s, p)
