# eukhe: the proof of LAW rmw_applies_change

import Base
import ../../bend/config.bend as Cf
import ../../LAWS.bend as Laws
import ../base.bend as L

# LAW rmw_applies_change
def pcf.rmw_applies_change(+d: List<&2, Cf.Entry>, +k: Nat, +v: Nat) -> {Cf.kept(Cf.rmw(Cf.Parsed{d}, Cf.Set{k, v}), k) == Some{v} : Maybe<&2, Nat>}:
  %Equal.sym(Bool, Nat.is_eq(k, k), True{}, L.ppr.nat_eq_refl(k)) : {Cf.pick(_, v, Cf.lookup(Cf.del(d, k), k)) == Some{v} : Maybe<&2, Nat>}
  {==}

def Laws.rmw_applies_change(d, k, v):
  pcf.rmw_applies_change(d, k, v)
