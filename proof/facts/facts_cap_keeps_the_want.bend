# eukhe: the proof of LAW facts_cap_keeps_the_want

import Base
import ../../bend/facts.bend as Fx
import ../../laws/facts/model.bend as Facts
import ./base.bend as LA

def Facts.facts_cap_keeps_the_want(caller, mm, needs, win, h1, h2):
  match caller win:
    case Some{+x} Fx.Win{+w, +p, +s, +f, +st}:
      %LA.pf.shrink(x, w, p, s, f, st) : {Some{_} == Some{x} : Maybe<&2, Nat>}
      %Equal.sym(Bool, Facts.cap_conflict(x, Fx.Win{w, p, s, f, st}), False{}, h2) : {Some{Fx.cap.fit(_, x, w, p, s, f)} == Some{x} : Maybe<&2, Nat>}
      {==}
    case None{} Fx.Win{+w, +p, +s, +f, +st}:
      %Equal.sym(Bool, Facts.cap_left_out(None{}, needs), False{}, h1) : {Fx.cap.none(_, mm, Fx.Win{w, p, s, f, st}) == Some{mm} : Maybe<&2, Nat>}
      %LA.pf.shrink(mm, w, p, s, f, st) : {Some{_} == Some{mm} : Maybe<&2, Nat>}
      %Equal.sym(Bool, Facts.cap_conflict(mm, Fx.Win{w, p, s, f, st}), False{}, h2) : {Some{Fx.cap.fit(_, mm, w, p, s, f)} == Some{mm} : Maybe<&2, Nat>}
      {==}
