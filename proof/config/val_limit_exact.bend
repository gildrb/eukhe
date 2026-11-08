# eukhe: the proof of LAW val_limit_exact

import Base
import ../../bend/config.bend as Cf
import ../../laws/config.bend as Config
import ../../spec/settings/config_rules.bend as CR

def Config.val_limit_exact(v):
  match v:
    case Cf.Num{n}:
      match n:
        case 0n:
          {==}
        case 1n+q:
          {==}
    case Cf.Malformed{}:
      {==}
