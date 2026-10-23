# eukhe: the proof of LAW afw_evs_round_trip

import Base
import ../../bend/aux_fallback.bend as Af
import ../../bend/ffi_aux_fallback.bend as FAf
import ../../bend/wire.bend as Wr
import ../../laws/aux_fallback.bend as AuxFallback
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../base/logic/bool.bend as LLogicBool
import ../base/wire.bend as LWire
import ./afw_ev_round_trip.bend as PAfwEvRoundTrip

# a ev reads back (turned around for rewriting)
def pfw.ev(+e: Af.Ev, +rest: String, h: {AuxFallback.afw_ev_fits(e) == True{} : Bool}) -> {Wr.Got{e, rest} == FAf.get_ev(FAf.put_ev(e, rest)) : Wr.Dec<Af.Ev>}:
  Equal.sym(Wr.Dec<Af.Ev>, FAf.get_ev(FAf.put_ev(e, rest)), Wr.Got{e, rest}, AuxFallback.afw_ev_round_trip(e, rest, h))

# the items of xs, then rest (Af.Ev; a copy of PROOF.bend wire's wr_items)
def pfw.ev_items(xs: List<&2, Af.Ev>, rest: String) -> String:
  match xs:
    case Nil{}:
      rest
    case Con{x, t}:
      FAf.put_ev(x, pfw.ev_items(t, rest))

def pfw.ev_put_go(xs: List<&2, Af.Ev>, -rest: String) ->
  {Wr.put_list.go(~Af.Ev, ~FAf.put_ev, xs, rest) == (List.length(&2, Af.Ev, xs), pfw.ev_items(xs, rest)) : Nat & String}:
  match xs:
    case Nil{}:
      {==}
    case Con{x, +t}:
      %Equal.sym(Nat & String, Wr.put_list.go(~Af.Ev, ~FAf.put_ev, t, rest), (List.length(&2, Af.Ev, t), pfw.ev_items(t, rest)), pfw.ev_put_go(t, rest)) : {Wr.put_list.step(~Af.Ev, ~FAf.put_ev, x, _) == (1n+List.length(&2, Af.Ev, t), FAf.put_ev(x, pfw.ev_items(t, rest))) : Nat & String}
      {==}

# a list is its count, then its items
def pfw.ev_put(+xs: List<&2, Af.Ev>, -rest: String) ->
  {Wr.put_list(~Af.Ev, ~FAf.put_ev, xs, rest) == Wr.put_nat(List.length(&2, Af.Ev, xs), pfw.ev_items(xs, rest)) : String}:
  %Equal.sym(Nat & String, Wr.put_list.go(~Af.Ev, ~FAf.put_ev, xs, rest), (List.length(&2, Af.Ev, xs), pfw.ev_items(xs, rest)), pfw.ev_put_go(xs, rest)) : {Wr.put_list.fin(_) == Wr.put_nat(List.length(&2, Af.Ev, xs), pfw.ev_items(xs, rest)) : String}
  {==}

# the item loop reads back x then t (wr_list_go_rt for Af.Ev)
def pfw.ev_go_rt(+t: List<&2, Af.Ev>, +x: Af.Ev, +rest: String,
  +hf: {AuxFallback.afw_evs_fit(x <> t) == True{} : Bool}) ->
  {Wr.get_list.go(~Af.Ev, ~FAf.get_ev, List.length(&2, Af.Ev, t), FAf.get_ev(FAf.put_ev(x, pfw.ev_items(t, rest)))) == Wr.Got{x <> t, rest} : Wr.Dec<List<&2, Af.Ev>>}:
  match t:
    case Nil{}:
      %pfw.ev(x, rest, LLogicBool.wr_and_l(AuxFallback.afw_ev_fits(x), True{}, hf)) : {Wr.get_list.go(~Af.Ev, ~FAf.get_ev, 0n, _) == Wr.Got{[x], rest} : Wr.Dec<List<&2, Af.Ev>>}
      {==}
    case Con{+y, +u}:
      %pfw.ev(x, FAf.put_ev(y, pfw.ev_items(u, rest)), LLogicBool.wr_and_l(AuxFallback.afw_ev_fits(x), AuxFallback.afw_evs_fit(y <> u), hf)) : {Wr.get_list.go(~Af.Ev, ~FAf.get_ev, 1n+List.length(&2, Af.Ev, u), _) == Wr.Got{x <> y <> u, rest} : Wr.Dec<List<&2, Af.Ev>>}
      %Equal.sym(Wr.Dec<List<&2, Af.Ev>>, Wr.get_list.go(~Af.Ev, ~FAf.get_ev, List.length(&2, Af.Ev, u), FAf.get_ev(FAf.put_ev(y, pfw.ev_items(u, rest)))), Wr.Got{y <> u, rest}, pfw.ev_go_rt(u, y, rest, LLogicBool.wr_and_r(AuxFallback.afw_ev_fits(x), AuxFallback.afw_evs_fit(y <> u), hf))) : {Wr.get_list.cons(Af.Ev, x, _) == Wr.Got{x <> y <> u, rest} : Wr.Dec<List<&2, Af.Ev>>}
      {==}

def AuxFallback.afw_evs_round_trip(xs, rest, h):
  match xs:
    case Nil{}:
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(0n, rest)), Wr.Got{0n, rest}, Wire.wire_nat_round_trip(0n, rest, LLogicBool.wr_and_l(LawsBase.wire_fits(0n), True{}, h))) : {Wr.get_list.start(~Af.Ev, ~FAf.get_ev, _) == Wr.Got{Nil{}, rest} : Wr.Dec<List<&2, Af.Ev>>}
      {==}
    case Con{+x, +t}:
      +r = rest
      +hh = h
      %Equal.sym(String, Wr.put_list(~Af.Ev, ~FAf.put_ev, x <> t, r), Wr.put_nat(List.length(&2, Af.Ev, x <> t), pfw.ev_items(x <> t, r)), pfw.ev_put(x <> t, r)) : {Wr.get_list(~Af.Ev, ~FAf.get_ev, _) == Wr.Got{x <> t, r} : Wr.Dec<List<&2, Af.Ev>>}
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(List.length(&2, Af.Ev, x <> t), pfw.ev_items(x <> t, r))), Wr.Got{List.length(&2, Af.Ev, x <> t), pfw.ev_items(x <> t, r)}, Wire.wire_nat_round_trip(List.length(&2, Af.Ev, x <> t), pfw.ev_items(x <> t, r), LLogicBool.wr_and_l(LawsBase.wire_fits(List.length(&2, Af.Ev, x <> t)), AuxFallback.afw_evs_fit(x <> t), hh))) : {Wr.get_list.start(~Af.Ev, ~FAf.get_ev, _) == Wr.Got{x <> t, r} : Wr.Dec<List<&2, Af.Ev>>}
      pfw.ev_go_rt(t, x, r, LLogicBool.wr_and_r(LawsBase.wire_fits(List.length(&2, Af.Ev, x <> t)), AuxFallback.afw_evs_fit(x <> t), hh))
