# eukhe: the proof of LAW malformed_at_exact

import Base
import ../../bend/config.bend as Cf
import ../../laws/config.bend as Config
import ../../spec/config_rules.bend as CR
import ./base/config.bend as LA

def pm.bad(m: Maybe<&2, Cf.Val>) -> {Cf.malformed_val(m) == CR.cr_bad(m) : Bool}:
  match m:
    case None{}:
      {==}
    case Some{v}:
      match v:
        case Cf.Num{n}:
          {==}
        case Cf.Malformed{}:
          {==}

def Config.malformed_at_exact(s, p):
  match s:
    case Cf.Unset{}:
      {==}
    case Cf.Entries{+es}:
      %LA.pcf.slot(es, p) : {Cf.malformed_val(Cf.slot(es, p)) == CR.cr_bad(_) : Bool}
      pm.bad(Cf.slot(es, p))
    case Cf.NotMap{}:
      {==}
