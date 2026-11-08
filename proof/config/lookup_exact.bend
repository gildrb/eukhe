# eukhe: the proof of LAW lookup_exact
# Entry by entry (LA.pcf.lookup, an induction on the document).

import Base
import ../../bend/config.bend as Cf
import ../../laws/config.bend as Config
import ../../spec/settings/config_rules.bend as CR
import ./base/config.bend as LA

def Config.lookup_exact(d, j):
  LA.pcf.lookup(d, j)
