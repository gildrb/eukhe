# eukhe: the proof of LAW dmw_pick_round_trip

import Base
import ../../bend/default_model.bend as Dm
import ../../bend/ffi_default_model.bend as FDm
import ../../bend/wire.bend as Wr
import ../../laws/default_model.bend as DefaultModel
import ./base.bend as LA

def DefaultModel.dmw_pick_round_trip(p, rest, h):
  match p:
    case Dm.Saved{}:
      {==}
    case Dm.Other{+n}:
      %LA.pdw.nat(n, rest, h) : {FDm.get_pick.n(_) == Wr.Got{Dm.Other{n}, rest} : Wr.Dec<Dm.Pick>}
      {==}
