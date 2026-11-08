# eukhe: the proof of LAW revive_age_exact
# The age adds d to the time since the last record from the run's start,
# which is c mod h (LRv.rvb.mod_since).

import Base
import ../../bend/revive.bend as Rv
import ../../laws/revive.bend as Revive
import ./base.bend as LRv

def Revive.revive_age_exact(h, c, d):
  %Equal.sym(Nat, Nat.mod(c, h), Rv.since(c, h, 0n), LRv.rvb.mod_since(c, h)) : {Nat.add(Rv.since(c, h, 0n), d) == Nat.add(_, d) : Nat}
  {==}
