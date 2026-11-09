# eukhe: the proof of LAW limit_values
# The first entry of the map is p's: the slot is its value.

import Base
import ../../bend/config.bend as Cf
import ../../laws/config.bend as Config
import ../base/nat.bend as LNat

def plv.first(+p: Nat, v: Cf.Val, es: List<&2, Cf.Slot>) -> {Cf.limit(Cf.Entries{Cf.Slot{p, v} <> es}, p) == Cf.val_limit(v) : Cf.Lim}:
  %Equal.sym(Bool, Nat.is_eq(p, p), True{}, LNat.ppr.nat_eq_refl(p)) : {Cf.slot_limit(Cf.slot.pick(_, v, Cf.slot(es, p))) == Cf.val_limit(v) : Cf.Lim}
  {==}

def Config.limit_values(p, q, es):
  ({==}, {==}, {==}, plv.first(p, Cf.Num{0n}, es), plv.first(p, Cf.Num{1n+q}, es), plv.first(p, Cf.Malformed{}, es))
