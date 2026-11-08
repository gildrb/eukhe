# eukhe: the proof of LAW listed_exact

import Base
import ../../bend/config.bend as Cf
import ../../laws/config.bend as Config
import ../../spec/settings/config_rules.bend as CR

def Config.listed_exact(ns, n):
  match ns:
    case Nil{}:
      {==}
    case +x <> +t:
      %Config.listed_exact(t, n) : {Bool.or(Nat.is_eq(x, n), Cf.listed(t, n)) == Bool.or(Nat.is_eq(x, n), _) : Bool}
      {==}
