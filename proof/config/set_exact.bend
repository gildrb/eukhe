# eukhe: the proof of LAW set_exact
# The set is the write of a Set over the parsed document
# (LA.pcf.set_spec, the rmw_written_exact lemmas).

import Base
import ../../bend/config.bend as Cf
import ../../laws/config.bend as Config
import ../../spec/settings/config_rules.bend as CR
import ./base/config.bend as LA

def Config.set_exact(d, k, v):
  LA.pcf.set_spec(d, k, v)
