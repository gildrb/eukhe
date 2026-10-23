# eukhe: the proof of LAW adw_lvs_round_trip

import Base
import ../../bend/admission.bend as Ad
import ../../bend/ffi_admission.bend as FAd
import ../../bend/wire.bend as Wr
import ../../laws/admission.bend as Admission
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../base/bool/and.bend as LBoolAnd
import ../base/wire.bend as LWire
import ./adw_lv_round_trip.bend as PAdwLvRoundTrip

# a lv reads back (turned around for rewriting)
def paw.lv(+t: Ad.Lv, +rest: String, h: {Admission.adw_lv_fits(t) == True{} : Bool}) -> {Wr.Got{t, rest} == FAd.get_lv(FAd.put_lv(t, rest)) : Wr.Dec<Ad.Lv>}:
  Equal.sym(Wr.Dec<Ad.Lv>, FAd.get_lv(FAd.put_lv(t, rest)), Wr.Got{t, rest}, Admission.adw_lv_round_trip(t, rest, h))

# the items of xs, then rest (Ad.Lv; a copy of PROOF.bend wire's wr_items)
def paw.lv_items(xs: List<&2, Ad.Lv>, rest: String) -> String:
  match xs:
    case Nil{}:
      rest
    case Con{x, t}:
      FAd.put_lv(x, paw.lv_items(t, rest))

def paw.lv_put_go(xs: List<&2, Ad.Lv>, -rest: String) ->
  {Wr.put_list.go(~Ad.Lv, ~FAd.put_lv, xs, rest) == (List.length(&2, Ad.Lv, xs), paw.lv_items(xs, rest)) : Nat & String}:
  match xs:
    case Nil{}:
      {==}
    case Con{x, +t}:
      %Equal.sym(Nat & String, Wr.put_list.go(~Ad.Lv, ~FAd.put_lv, t, rest), (List.length(&2, Ad.Lv, t), paw.lv_items(t, rest)), paw.lv_put_go(t, rest)) : {Wr.put_list.step(~Ad.Lv, ~FAd.put_lv, x, _) == (1n+List.length(&2, Ad.Lv, t), FAd.put_lv(x, paw.lv_items(t, rest))) : Nat & String}
      {==}

# a list is its count, then its items
def paw.lv_put(+xs: List<&2, Ad.Lv>, -rest: String) ->
  {Wr.put_list(~Ad.Lv, ~FAd.put_lv, xs, rest) == Wr.put_nat(List.length(&2, Ad.Lv, xs), paw.lv_items(xs, rest)) : String}:
  %Equal.sym(Nat & String, Wr.put_list.go(~Ad.Lv, ~FAd.put_lv, xs, rest), (List.length(&2, Ad.Lv, xs), paw.lv_items(xs, rest)), paw.lv_put_go(xs, rest)) : {Wr.put_list.fin(_) == Wr.put_nat(List.length(&2, Ad.Lv, xs), paw.lv_items(xs, rest)) : String}
  {==}

# the item loop reads back x then t (wr_list_go_rt for Ad.Lv)
def paw.lv_go_rt(+t: List<&2, Ad.Lv>, +x: Ad.Lv, +rest: String,
  +hf: {Admission.adw_lvs_fit(x <> t) == True{} : Bool}) ->
  {Wr.get_list.go(~Ad.Lv, ~FAd.get_lv, List.length(&2, Ad.Lv, t), FAd.get_lv(FAd.put_lv(x, paw.lv_items(t, rest)))) == Wr.Got{x <> t, rest} : Wr.Dec<List<&2, Ad.Lv>>}:
  match t:
    case Nil{}:
      %paw.lv(x, rest, LBoolAnd.wr_and_l(Admission.adw_lv_fits(x), True{}, hf)) : {Wr.get_list.go(~Ad.Lv, ~FAd.get_lv, 0n, _) == Wr.Got{[x], rest} : Wr.Dec<List<&2, Ad.Lv>>}
      {==}
    case Con{+y, +u}:
      %paw.lv(x, FAd.put_lv(y, paw.lv_items(u, rest)), LBoolAnd.wr_and_l(Admission.adw_lv_fits(x), Admission.adw_lvs_fit(y <> u), hf)) : {Wr.get_list.go(~Ad.Lv, ~FAd.get_lv, 1n+List.length(&2, Ad.Lv, u), _) == Wr.Got{x <> y <> u, rest} : Wr.Dec<List<&2, Ad.Lv>>}
      %Equal.sym(Wr.Dec<List<&2, Ad.Lv>>, Wr.get_list.go(~Ad.Lv, ~FAd.get_lv, List.length(&2, Ad.Lv, u), FAd.get_lv(FAd.put_lv(y, paw.lv_items(u, rest)))), Wr.Got{y <> u, rest}, paw.lv_go_rt(u, y, rest, LBoolAnd.wr_and_r(Admission.adw_lv_fits(x), Admission.adw_lvs_fit(y <> u), hf))) : {Wr.get_list.cons(Ad.Lv, x, _) == Wr.Got{x <> y <> u, rest} : Wr.Dec<List<&2, Ad.Lv>>}
      {==}

def Admission.adw_lvs_round_trip(xs, rest, h):
  match xs:
    case Nil{}:
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(0n, rest)), Wr.Got{0n, rest}, Wire.wire_nat_round_trip(0n, rest, LBoolAnd.wr_and_l(LawsBase.wire_fits(0n), True{}, h))) : {Wr.get_list.start(~Ad.Lv, ~FAd.get_lv, _) == Wr.Got{Nil{}, rest} : Wr.Dec<List<&2, Ad.Lv>>}
      {==}
    case Con{+x, +t}:
      +r = rest
      +hh = h
      %Equal.sym(String, Wr.put_list(~Ad.Lv, ~FAd.put_lv, x <> t, r), Wr.put_nat(List.length(&2, Ad.Lv, x <> t), paw.lv_items(x <> t, r)), paw.lv_put(x <> t, r)) : {Wr.get_list(~Ad.Lv, ~FAd.get_lv, _) == Wr.Got{x <> t, r} : Wr.Dec<List<&2, Ad.Lv>>}
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(List.length(&2, Ad.Lv, x <> t), paw.lv_items(x <> t, r))), Wr.Got{List.length(&2, Ad.Lv, x <> t), paw.lv_items(x <> t, r)}, Wire.wire_nat_round_trip(List.length(&2, Ad.Lv, x <> t), paw.lv_items(x <> t, r), LBoolAnd.wr_and_l(LawsBase.wire_fits(List.length(&2, Ad.Lv, x <> t)), Admission.adw_lvs_fit(x <> t), hh))) : {Wr.get_list.start(~Ad.Lv, ~FAd.get_lv, _) == Wr.Got{x <> t, r} : Wr.Dec<List<&2, Ad.Lv>>}
      paw.lv_go_rt(t, x, r, LBoolAnd.wr_and_r(LawsBase.wire_fits(List.length(&2, Ad.Lv, x <> t)), Admission.adw_lvs_fit(x <> t), hh))
