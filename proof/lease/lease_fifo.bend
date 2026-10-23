# eukhe: the proof of LAW lease_fifo

import Base
import ../../bend/lease.bend as Ls
import ../../laws/lease.bend as Lease
import ./base.bend as LA

def pl.inv_fifo(+s: Ls.L, inv: LA.pl.Inv(s)) -> Ls.Fifo(s):
  match s:
    case Ls.L{n, h, q}:
      (a, _) = inv
      a

# The laws
# --------

def lease_fifo(+evs: List<&2, Ls.Ev>) -> Ls.Fifo(Ls.run(evs)):
  pl.inv_fifo(Ls.run(evs), LA.pl.inv_run(evs))

def Lease.lease_fifo(evs):
  lease_fifo(evs)
