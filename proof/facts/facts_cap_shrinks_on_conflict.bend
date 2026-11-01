# eukhe: the proof of LAW facts_cap_shrinks_on_conflict

import Base
import ../../bend/facts.bend as Fx
import ../../laws/facts.bend as Facts
import ./base.bend as LA

def Facts.facts_cap_shrinks_on_conflict(caller, mm, needs, win, h1, h2):
  match caller win:
    case Some{+x} Fx.Win{+w, +p, +s, +f, +st}:
      %LA.pf.shrink(x, w, p, s, f, st) : {Some{_} == Some{Nat.max(f, Nat.sub(w, Nat.add(p, s)))} : Maybe<&2, Nat>}
      %Equal.sym(Bool, Facts.cap_conflict(x, Fx.Win{w, p, s, f, st}), True{}, h2) : {Some{Fx.cap.fit(_, x, w, p, s, f)} == Some{Nat.max(f, Nat.sub(w, Nat.add(p, s)))} : Maybe<&2, Nat>}
      %LA.pf.sub_sub(w, p, s) : {Some{Nat.max(f, Nat.sub(Nat.sub(w, p), s))} == Some{Nat.max(f, _)} : Maybe<&2, Nat>}
      {==}
    case None{} Fx.Win{+w, +p, +s, +f, +st}:
      %Equal.sym(Bool, Facts.cap_unknown(None{}, mm, needs, Fx.Win{w, p, s, f, st}), False{}, h1) : {Fx.cap.none(_, mm, Fx.Win{w, p, s, f, st}) == Some{Nat.max(f, Nat.sub(w, Nat.add(p, s)))} : Maybe<&2, Nat>}
      %LA.pf.shrink(mm, w, p, s, f, st) : {Some{_} == Some{Nat.max(f, Nat.sub(w, Nat.add(p, s)))} : Maybe<&2, Nat>}
      %Equal.sym(Bool, Facts.cap_conflict(mm, Fx.Win{w, p, s, f, st}), True{}, h2) : {Some{Fx.cap.fit(_, mm, w, p, s, f)} == Some{Nat.max(f, Nat.sub(w, Nat.add(p, s)))} : Maybe<&2, Nat>}
      %LA.pf.sub_sub(w, p, s) : {Some{Nat.max(f, Nat.sub(Nat.sub(w, p), s))} == Some{Nat.max(f, _)} : Maybe<&2, Nat>}
      {==}
