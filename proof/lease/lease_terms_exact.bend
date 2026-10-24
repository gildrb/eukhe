# eukhe: the proof of LAW lease_terms_exact

import Base
import ../../bend/lease.bend as Ls
import ../../laws/lease.bend as Lease

def st.h(h: Maybe<&2, Ls.Lease>) -> {Ls.hkey(h) == Lease.lw_hkey(h) : Maybe<&2, Nat>}:
  match h:
    case None{}:
      {==}
    case Some{x}:
      match x:
        case Ls.Lease{k, o}:
          {==}

def Lease.lease_terms_exact(s, h, w):
  match s:
    case Ls.L{n, sh, q}:
      match w:
        case Ls.Waiter{k, o, l}:
          ({==}, ({==}, ({==}, (st.h(h), ({==}, {==})))))
