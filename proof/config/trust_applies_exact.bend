# eukhe: the proof of LAW trust_applies_exact
# Every trust, scope and class: a finite check.

import Base
import ../../bend/config.bend as Cf
import ../../laws/config.bend as Config
import ./base/config.bend as LA

def Config.trust_applies_exact(t, s):
  LA.pcf.applies(t, s)
