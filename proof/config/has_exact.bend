# eukhe: the proof of LAW has_exact

import Base
import ../../bend/config.bend as Cf
import ../../laws/config.bend as Config
import ../../spec/config_rules.bend as CR

def Config.has_exact(es, n):
  match es:
    case Nil{}:
      {==}
    case x <> +t:
      match x:
        case Cf.Named{+m, fs}:
          %Config.has_exact(t, n) : {Bool.or(Nat.is_eq(m, n), Cf.has(t, n)) == Bool.or(Nat.is_eq(m, n), _) : Bool}
          {==}
