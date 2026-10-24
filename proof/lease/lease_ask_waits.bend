# eukhe: the proof of LAW lease_ask_waits
# An ask appends a live waiter under the next key; the settle that follows
# keeps every live waiter waiting or holding (LKW.pl.settle_kept).

import Base
import ../../bend/lease.bend as Ls
import ../../laws/lease.bend as Lease
import ./lease_keeps_waiters.bend as LKW

# x is in q with x at its end
def aw.last(q: List<&2, Ls.Waiter>, +x: Ls.Waiter) -> Ls.In(x, List.append(&2, Ls.Waiter, q, [x])):
  match q:
    case Nil{}:
      Inl{{==}}
    case w <> t:
      Inr{aw.last(t, x)}

def Lease.lease_ask_waits(s, o):
  match s:
    case Ls.L{+n, h, +q}:
      LKW.pl.settle_kept(n, o, 1n+n, h, List.append(&2, Ls.Waiter, q, [Ls.Waiter{n, o, True{}}]), Inr{aw.last(q, Ls.Waiter{n, o, True{}})})
