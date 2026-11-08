# eukhe: the proof of LAW finds_exact

import Base
import ../../bend/config.bend as Cf
import ../../laws/config.bend as Config
import ../../spec/settings/config_rules.bend as CR
import ./base/config.bend as LA

def Config.finds_exact(es, qs):
  match qs:
    case Nil{}:
      {==}
    case +q <> +t:
      %LA.pcf.mf.find(es, q) : {Cf.find(es, q) <> Cf.finds(es, t) == _ <> Config.cf_finds(es, t) : List<&2, Maybe<&2, List<&2, Cf.Entry>>>}
      %Config.finds_exact(es, t) : {Cf.find(es, q) <> Cf.finds(es, t) == Cf.find(es, q) <> _ : List<&2, Maybe<&2, List<&2, Cf.Entry>>>}
      {==}
