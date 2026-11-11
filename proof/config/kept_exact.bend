# eukhe: the proof of LAW kept_exact

import Base
import ../../bend/config.bend as Cf
import ../../laws/config.bend as Config
import ../../spec/settings/config_rules.bend as CR
import ./base/config.bend as LA

def Config.kept_exact(w, j):
  match w:
    case Cf.Refused{}:
      {==}
    case Cf.Wrote{d}:
      LA.pcf.lookup(d, j)
