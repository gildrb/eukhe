# eukhe: the proof of LAW afw_pass_round_trip

import Base
import ../../bend/aux_fallback.bend as Af
import ../../bend/ffi_aux_fallback.bend as FAf
import ../../bend/wire.bend as Wr
import ../../LAWS.bend as Laws
import ../base.bend as L
import ./base.bend as LA
import ./afw_evs_round_trip.bend as PAfwEvsRoundTrip

# a list that fits reads back (turned around for rewriting)
def pfw.evs(+xs: List<&2, Af.Ev>, +rest: String, h: {Bool.and(Laws.wire_fits(List.length(&2, Af.Ev, xs)), Laws.afw_evs_fit(xs)) == True{} : Bool}) ->
  {Wr.Got{xs, rest} == Wr.get_list(~Af.Ev, ~FAf.get_ev, Wr.put_list(~Af.Ev, ~FAf.put_ev, xs, rest)) : Wr.Dec<List<&2, Af.Ev>>}:
  Equal.sym(Wr.Dec<List<&2, Af.Ev>>, Wr.get_list(~Af.Ev, ~FAf.get_ev, Wr.put_list(~Af.Ev, ~FAf.put_ev, xs, rest)), Wr.Got{xs, rest}, Laws.afw_evs_round_trip(xs, rest, h))

def Laws.afw_pass_round_trip(es, ks, rest, h):
  +z = rest
  +hh = h
  +le = Bool.and(Laws.wire_fits(List.length(&2, Af.Ev, es)), Laws.afw_evs_fit(es))
  +lk = Bool.and(Laws.wire_fits(List.length(&2, Af.Key, ks)), Laws.afw_keys_fit(ks))
  %pfw.evs(es, Wr.put_list(~Af.Key, ~FAf.put_key, ks, z), L.wr_and_l(le, lk, hh)) : {FAf.get_pass.go(_) == Wr.Got{(es, ks), z} : Wr.Dec<+Sigma<List<&2, Af.Ev>, x => List<&2, Af.Key>>>}
  %LA.pfw.keys(ks, z, L.wr_and_r(le, lk, hh)) : {FAf.get_pass.keys(es, _) == Wr.Got{(es, ks), z} : Wr.Dec<+Sigma<List<&2, Af.Ev>, x => List<&2, Af.Key>>>}
  {==}
