# eukhe: the proof of LAW facts_cap_omits_unknown

import Base
import ../../bend/facts.bend as Fx
import ../../laws/facts.bend as Facts
import ../base/logic/logic.bend as LLogicLogic

def Facts.facts_cap_omits_unknown(caller, mm, needs, win, h):
  match caller win:
    case Some{+x} Fx.Win{+w, +p, +s, +f, +st}:
      LLogicLogic.pq.absurdF({Fx.cap(Some{x}, mm, needs, Fx.Win{w, p, s, f, st}) == None{} : Maybe<&2, Nat>}, h)
    case None{} Fx.Win{+w, +p, +s, +f, +st}:
      %Equal.sym(Bool, Facts.cap_unknown(None{}, mm, needs, Fx.Win{w, p, s, f, st}), True{}, h) : {Fx.cap.none(_, mm, Fx.Win{w, p, s, f, st}) == None{} : Maybe<&2, Nat>}
      {==}
