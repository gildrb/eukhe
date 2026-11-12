# eukhe: the proof of LAW limit_other_slot
# The slot of another provider is skipped.

import Base
import ../../bend/config.bend as Cf
import ../../laws/config.bend as Config

def Config.limit_other_slot(p, r, v, es, other):
  %Equal.sym(Bool, Nat.is_eq(r, p), False{}, other) : {Cf.slot_limit(Cf.slot.pick(_, v, Cf.slot(es, p))) == Cf.slot_limit(Cf.slot(es, p)) : Cf.Lim}
  {==}
