# eukhe: the proof of LAW limits_exact
# One provider at a time: the first slot of the provider decides, as in
# the laws' restatement (an induction on the slots, then on the providers).

import Base
import ../../bend/config.bend as Cf
import ../../laws/config.bend as Config
import ./base/config.bend as LA

def Config.limits_exact(s, qs):
  match qs:
    case Nil{}:
      {==}
    case +q <> +rest:
      %LA.pcf.limit(s, q) : {Cf.limit(s, q) <> Cf.limits(s, rest) == _ <> Config.cf_limits(s, rest) : List<&2, Cf.Lim>}
      %Config.limits_exact(s, rest) : {Cf.limit(s, q) <> Cf.limits(s, rest) == Cf.limit(s, q) <> _ : List<&2, Cf.Lim>}
      {==}
