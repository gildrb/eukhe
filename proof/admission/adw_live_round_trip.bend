# eukhe: the proof of LAW adw_live_round_trip

import Base
import ../../bend/admission.bend as Ad
import ../../bend/ffi_admission.bend as FAd
import ../../bend/wire.bend as Wr
import ../../laws/admission.bend as Admission
import ../../laws/base.bend as LawsBase
import ../base.bend as L
import ./base.bend as LA
import ./adw_lvs_round_trip.bend as PAdwLvsRoundTrip

# a list that fits reads back (turned around for rewriting)
def paw.lvs(+xs: List<&2, Ad.Lv>, +rest: String, h: {Bool.and(LawsBase.wire_fits(List.length(&2, Ad.Lv, xs)), Admission.adw_lvs_fit(xs)) == True{} : Bool}) ->
  {Wr.Got{xs, rest} == Wr.get_list(~Ad.Lv, ~FAd.get_lv, Wr.put_list(~Ad.Lv, ~FAd.put_lv, xs, rest)) : Wr.Dec<List<&2, Ad.Lv>>}:
  Equal.sym(Wr.Dec<List<&2, Ad.Lv>>, Wr.get_list(~Ad.Lv, ~FAd.get_lv, Wr.put_list(~Ad.Lv, ~FAd.put_lv, xs, rest)), Wr.Got{xs, rest}, Admission.adw_lvs_round_trip(xs, rest, h))

def Admission.adw_live_round_trip(x, rest, h):
  match x:
    case Ad.Live{+l, +q, +ts, +n}:
      +r = rest
      +hh = h
      +lt = Bool.and(LawsBase.wire_fits(List.length(&2, Ad.Lv, ts)), Admission.adw_lvs_fit(ts))
      +h1 = L.wr_and_r(Admission.adw_lim_fits(l), Bool.and(LawsBase.wire_fits(q), Bool.and(lt, LawsBase.wire_fits(n))), hh)
      +h2 = L.wr_and_r(LawsBase.wire_fits(q), Bool.and(lt, LawsBase.wire_fits(n)), h1)
      %LA.paw.lim(l, Wr.put_nat(q, Wr.put_list(~Ad.Lv, ~FAd.put_lv, ts, Wr.put_nat(n, r))), L.wr_and_l(Admission.adw_lim_fits(l), Bool.and(LawsBase.wire_fits(q), Bool.and(lt, LawsBase.wire_fits(n))), hh)) : {FAd.get_live.go(_) == Wr.Got{Ad.Live{l, q, ts, n}, r} : Wr.Dec<Ad.Live>}
      %LA.paw.nat(q, Wr.put_list(~Ad.Lv, ~FAd.put_lv, ts, Wr.put_nat(n, r)), L.wr_and_l(LawsBase.wire_fits(q), Bool.and(lt, LawsBase.wire_fits(n)), h1)) : {FAd.get_live.q(l, _) == Wr.Got{Ad.Live{l, q, ts, n}, r} : Wr.Dec<Ad.Live>}
      %paw.lvs(ts, Wr.put_nat(n, r), L.wr_and_l(lt, LawsBase.wire_fits(n), h2)) : {FAd.get_live.ts(l, q, _) == Wr.Got{Ad.Live{l, q, ts, n}, r} : Wr.Dec<Ad.Live>}
      %LA.paw.nat(n, r, L.wr_and_r(lt, LawsBase.wire_fits(n), h2)) : {FAd.get_live.next(l, q, ts, _) == Wr.Got{Ad.Live{l, q, ts, n}, r} : Wr.Dec<Ad.Live>}
      {==}
