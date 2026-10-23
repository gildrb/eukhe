# eukhe: the proof of LAW trusted_project_applies

import Base
import ../../bend/config.bend as Cf
import ../../laws/config.bend as Config
import ../base.bend as L

# LAW trusted_project_applies
def pcf.trusted_project_applies(g: List<&2, Cf.Entry>, +k: Nat, kind: Cf.Class, v: Nat, items: List<&2, Cf.Item>) -> {Cf.lookup(Cf.effective(Cf.Trusted{}, g, Cf.Item{k, kind, v} <> items), k) == Some{v} : Maybe<&2, Nat>}:
  %Equal.sym(Bool, Nat.is_eq(k, k), True{}, L.ppr.nat_eq_refl(k)) : {Cf.pick(_, v, Cf.lookup(Cf.effective(Cf.Trusted{}, g, items), k)) == Some{v} : Maybe<&2, Nat>}
  {==}

def Config.trusted_project_applies(g, k, kind, v, items):
  pcf.trusted_project_applies(g, k, kind, v, items)
