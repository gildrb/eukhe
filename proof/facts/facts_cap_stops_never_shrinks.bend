# eukhe: the proof of LAW facts_cap_stops_never_shrinks

import Base
import ../../bend/facts.bend as Fx
import ../../laws/facts/model.bend as Facts

def Facts.facts_cap_stops_never_shrinks(caller, mm, needs, w, p, s, f, h1):
  match caller:
    case Some{x}:
      {==}
    case None{}:
      %Equal.sym(Bool, Facts.cap_unknown(None{}, mm, needs, Fx.Win{w, p, s, f, True{}}), False{}, h1) : {Fx.cap.none(_, mm, Fx.Win{w, p, s, f, True{}}) == Some{mm} : Maybe<&2, Nat>}
      {==}
