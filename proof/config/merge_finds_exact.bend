# eukhe: the proof of LAW merge_finds_exact
# The merged map lists the project entries before the global ones: a name
# is found among the project entries first (an induction on them), then
# among the global ones.

import Base
import ../../bend/config.bend as Cf
import ../../laws/config.bend as Config
import ./base/config.bend as LA

def Config.merge_finds_exact(g, p, qs):
  match qs:
    case Nil{}:
      {==}
    case +q <> +rest:
      %LA.pcf.mf.merged(g, p, q) : {Cf.find(Cf.merge(g, p), q) <> Cf.finds(Cf.merge(g, p), rest) == _ <> Config.cf_merged(g, p, rest) : List<&2, Maybe<&2, List<&2, Cf.Entry>>>}
      %Config.merge_finds_exact(g, p, rest) : {Cf.find(Cf.merge(g, p), q) <> Cf.finds(Cf.merge(g, p), rest) == Cf.find(Cf.merge(g, p), q) <> _ : List<&2, Maybe<&2, List<&2, Cf.Entry>>>}
      {==}
