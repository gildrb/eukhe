# eukhe: the proof of LAW leaf_in_exact

import Base
import ../../bend/config.bend as Cf
import ../../laws/config.bend as Config
import ../../spec/config_rules.bend as CR

def Config.leaf_in_exact(l, ls):
  match ls:
    case Nil{}:
      {==}
    case +x <> +t:
      %Config.leaf_in_exact(l, t) : {Or({l == x : Cf.Leaf}, Cf.In(l, t)) == Or({l == x : Cf.Leaf}, _) : Type}
      {==}
