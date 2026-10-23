# eukhe: the proof of LAW dmw_sub_round_trip

import Base
import ../../bend/default_model.bend as Dm
import ../../bend/ffi_default_model.bend as FDm
import ../../bend/wire.bend as Wr
import ../../LAWS.bend as Laws
import ./base.bend as LA

def Laws.dmw_sub_round_trip(s, rest, h):
  match s:
    case Dm.Kept{}:
      {==}
    case Dm.Swapped{+k}:
      %LA.pdw.key(k, rest, h) : {FDm.get_sub.k(_) == Wr.Got{Dm.Swapped{k}, rest} : Wr.Dec<Dm.Sub>}
      {==}
