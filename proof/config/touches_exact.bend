# eukhe: the proof of LAW touches_exact

import Base
import ../../bend/config.bend as Cf
import ../../laws/config.bend as Config
import ../../spec/settings/config_rules.bend as CR

def Config.touches_exact(e, j):
  match e:
    case Cf.Set{k, v}:
      {==}
    case Cf.Del{k}:
      {==}
