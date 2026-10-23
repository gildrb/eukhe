# eukhe: the proof of LAW limit_number_applies

import Base
import ../../bend/config.bend as Cf
import ../../laws/config.bend as Config

# LAW limit_number_applies
def pcf.limit_number_applies(es: List<&2, Cf.Slot>, +p: Nat, +n: Nat, h: {Cf.slot(es, p) == Some{Cf.Num{n}} : Maybe<&2, Cf.Val>}) -> {Cf.limit(Cf.Entries{es}, p) == Cf.val_limit(Cf.Num{n}) : Cf.Lim}:
  %Equal.sym(Maybe<&2, Cf.Val>, Cf.slot(es, p), Some{Cf.Num{n}}, h) : {Cf.slot_limit(_) == Cf.val_limit(Cf.Num{n}) : Cf.Lim}
  {==}

def Config.limit_number_applies(es, p, n, h):
  pcf.limit_number_applies(es, p, n, h)
