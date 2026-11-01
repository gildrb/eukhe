# eukhe: the proof of LAW facts_cap_never_below_floor

import Base
import ../../bend/facts.bend as Fx
import ../../laws/facts.bend as Facts
import ./base.bend as LA
import ./facts_cap_shrinks_on_conflict.bend as PShrinks

def Facts.facts_cap_never_below_floor(caller, mm, needs, w, p, s, f, st, h1, h2):
  %Equal.sym(Maybe<&2, Nat>, Fx.cap(caller, mm, needs, Fx.Win{w, p, s, f, st}), Some{Nat.max(f, Nat.sub(w, Nat.add(p, s)))}, Facts.facts_cap_shrinks_on_conflict(caller, mm, needs, Fx.Win{w, p, s, f, st}, h1, h2)) : {Nat.is_le(f, Maybe.default(&2, Nat, _, 0n)) == True{} : Bool}
  LA.pf.le_max_l(f, Nat.sub(w, Nat.add(p, s)))
