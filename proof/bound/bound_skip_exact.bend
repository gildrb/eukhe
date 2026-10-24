# eukhe: the proof of LAW bound_skip_exact: each branch of a skip computes the same on both sides

import Base
import ../../bend/bound.bend as Bd
import ../../bend/ffi_bound.bend as FBd
import ../../bend/wire.bend as Wr
import ../../laws/bound.bend as Bound
import ./base.bend as LBound

def bs.go(t: Bool, +c: Bd.Cap, +b: Nat, +nl: Nat, op: Bool, +sd: Nat, n: Nat, +k: Nat, o: Bool) -> {Bd.skip.go(t, c, b, nl, op, sd, n, k, o) == Bound.bd_skip.go(t, c, b, nl, op, sd, n, k, o) : Bd.St & Bool}:
  match t:
    case False{}:
      {==}
    case True{}:
      match n:
        case 0n:
          {==}
        case 1n++p:
          {==}

def Bound.bound_skip_exact(s, n, k, o):
  match s:
    case Bd.St{c, +b, +nl, op, +sd}:
      match c:
        case Bd.Cap{+cb, +ck, +ct}:
          bs.go(ct, Bd.Cap{cb, ck, ct}, b, nl, op, sd, n, k, o)
