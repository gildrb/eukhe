# eukhe: the proof of LAW leaf_path_exact

import Base
import ../../bend/config.bend as Cf
import ../../laws/config.bend as Config
import ../../spec/settings/config_rules.bend as CR

def Config.leaf_path_exact(l):
  match l:
    case Cf.Leaf{p, o}:
      {==}
