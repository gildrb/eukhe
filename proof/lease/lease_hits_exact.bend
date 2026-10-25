# eukhe: the proof of LAW lease_hits_exact

import Base
import ../../bend/lease.bend as Ls
import ../../laws/lease.bend as Lease

def Lease.lease_hits_exact(e, k, o, l):
  match e:
    case Ls.Ask{p}:
      {==}
    case Ls.Release{j}:
      {==}
    case Ls.Stop{j}:
      {==}
    case Ls.Crash{p}:
      {==}
