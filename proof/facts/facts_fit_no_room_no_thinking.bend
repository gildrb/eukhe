# eukhe: the proof of LAW facts_fit_no_room_no_thinking

import Base
import ../../bend/facts.bend as Fx
import ../../laws/facts/model.bend as Facts
import ./base.bend as LA

def Facts.facts_fit_no_room_no_thinking(base, mm, b, a, win, h):
  +M = Fx.cap.shrink(Fx.fit.cap(base, mm, b), win)
  %Equal.sym(Nat, Nat.sub(M, a), 0n, LA.pf.sub_zero_lt(M, a, h)) : {Nat.min(b, _) == 0n : Nat}
  LA.pf.min_zero(b)
