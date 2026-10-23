# eukhe: the proof of LAW adw_lv_round_trip

import Base
import ../../bend/admission.bend as Ad
import ../../bend/ffi_admission.bend as FAd
import ../../bend/wire.bend as Wr
import ../../laws/admission.bend as Admission
import ./base.bend as LA
import ./adw_sts_round_trip.bend as PAdwStsRoundTrip

# a sts reads back (turned around for rewriting)
def paw.sts(+s: Ad.Sts, +rest: String) -> {Wr.Got{s, rest} == FAd.get_sts(FAd.put_sts(s, rest)) : Wr.Dec<Ad.Sts>}:
  Equal.sym(Wr.Dec<Ad.Sts>, FAd.get_sts(FAd.put_sts(s, rest)), Wr.Got{s, rest}, Admission.adw_sts_round_trip(s, rest))

def Admission.adw_lv_round_trip(t, rest, h):
  match t:
    case Ad.Lv{+k, +c, +s}:
      +r = rest
      %LA.paw.nat(k, FAd.put_cls(c, FAd.put_sts(s, r)), h) : {FAd.get_lv.go(_) == Wr.Got{Ad.Lv{k, c, s}, r} : Wr.Dec<Ad.Lv>}
      %LA.paw.cls(c, FAd.put_sts(s, r)) : {FAd.get_lv.cls(k, _) == Wr.Got{Ad.Lv{k, c, s}, r} : Wr.Dec<Ad.Lv>}
      %paw.sts(s, r) : {FAd.get_lv.sts(k, c, _) == Wr.Got{Ad.Lv{k, c, s}, r} : Wr.Dec<Ad.Lv>}
      {==}
