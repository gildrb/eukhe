# eukhe: the proof of LAW revive_since_exact
# r is r mod h (the premise); c more ms from r mod h leave (r + c) mod h
# (LRv.rvb.since_mod).

import Base
import ../../bend/revive.bend as Rv
import ../../laws/revive.bend as Revive
import ./base.bend as LRv

def Revive.revive_since_exact(h, r, c, at):
  %at : {Rv.since(c, h, _) == Nat.mod(Nat.add(r, c), h) : Nat}
  LRv.rvb.since_mod(c, h, r)
