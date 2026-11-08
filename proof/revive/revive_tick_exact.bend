# eukhe: the proof of LAW revive_tick_exact
# r is r mod h (the premise); a tick takes r mod h to (r + 1) mod h
# (LRv.rvb.mod_step).

import Base
import ../../bend/revive.bend as Rv
import ../../laws/revive.bend as Revive
import ./base.bend as LRv

def Revive.revive_tick_exact(h, r, at):
  %at : {Rv.tick(h, _) == Nat.mod(1n+r, h) : Nat}
  Equal.sym(Nat, Nat.mod(1n+r, h), Rv.tick(h, Nat.mod(r, h)), LRv.rvb.mod_step(r, h))
