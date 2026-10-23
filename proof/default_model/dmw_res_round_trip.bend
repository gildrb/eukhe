# eukhe: the proof of LAW dmw_res_round_trip

import Base
import ../../bend/default_model.bend as Dm
import ../../bend/ffi_default_model.bend as FDm
import ../../bend/wire.bend as Wr
import ../../laws/default_model.bend as DefaultModel
import ../base.bend as L
import ./base.bend as LA
import ./dmw_pick_round_trip.bend as PDmwPickRoundTrip
import ./dmw_sub_round_trip.bend as PDmwSubRoundTrip

# a pick reads back (turned around for rewriting)
def pdw.pick(+p: Dm.Pick, +rest: String, h: {DefaultModel.dmw_pick_fits(p) == True{} : Bool}) -> {Wr.Got{p, rest} == FDm.get_pick(FDm.put_pick(p, rest)) : Wr.Dec<Dm.Pick>}:
  Equal.sym(Wr.Dec<Dm.Pick>, FDm.get_pick(FDm.put_pick(p, rest)), Wr.Got{p, rest}, DefaultModel.dmw_pick_round_trip(p, rest, h))

# a sub reads back (turned around for rewriting)
def pdw.sub(+s: Dm.Sub, +rest: String, h: {DefaultModel.dmw_sub_fits(s) == True{} : Bool}) -> {Wr.Got{s, rest} == FDm.get_sub(FDm.put_sub(s, rest)) : Wr.Dec<Dm.Sub>}:
  Equal.sym(Wr.Dec<Dm.Sub>, FDm.get_sub(FDm.put_sub(s, rest)), Wr.Got{s, rest}, DefaultModel.dmw_sub_round_trip(s, rest, h))

def DefaultModel.dmw_res_round_trip(r, rest, h):
  match r:
    case Dm.Runs{+p, +s}:
      +z = rest
      +hh = h
      %pdw.pick(p, FDm.put_sub(s, z), L.wr_and_l(DefaultModel.dmw_pick_fits(p), DefaultModel.dmw_sub_fits(s), hh)) : {FDm.get_res.pick(_) == Wr.Got{Dm.Runs{p, s}, z} : Wr.Dec<Dm.Res>}
      %pdw.sub(s, z, L.wr_and_r(DefaultModel.dmw_pick_fits(p), DefaultModel.dmw_sub_fits(s), hh)) : {FDm.get_res.sub(p, _) == Wr.Got{Dm.Runs{p, s}, z} : Wr.Dec<Dm.Res>}
      {==}
    case Dm.Nothing{}:
      {==}
    case Dm.Refused{+k}:
      %LA.pdw.key(k, rest, h) : {FDm.get_res.refused(_) == Wr.Got{Dm.Refused{k}, rest} : Wr.Dec<Dm.Res>}
      {==}
