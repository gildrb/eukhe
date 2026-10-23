# eukhe: the proof of LAW afw_ev_round_trip

import Base
import ../../bend/aux_fallback.bend as Af
import ../../bend/ffi_aux_fallback.bend as FAf
import ../../bend/wire.bend as Wr
import ../../LAWS.bend as Laws
import ./base.bend as LA

def Laws.afw_ev_round_trip(e, rest, h):
  match e:
    case Af.Stay{}:
      {==}
    case Af.Went{}:
      {==}
    case Af.Sub{+k}:
      %LA.pfw.key(k, rest, h) : {FAf.get_ev.sub(_) == Wr.Got{Af.Sub{k}, rest} : Wr.Dec<Af.Ev>}
      {==}
    case Af.Note{+k}:
      %LA.pfw.key(k, rest, h) : {FAf.get_ev.note(_) == Wr.Got{Af.Note{k}, rest} : Wr.Dec<Af.Ev>}
      {==}
