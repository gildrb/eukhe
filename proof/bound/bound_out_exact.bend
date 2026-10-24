# eukhe: the proof of LAW bound_out_exact: each branch of a text's decision computes the same on both sides

import Base
import ../../bend/bound.bend as Bd
import ../../bend/ffi_bound.bend as FBd
import ../../bend/wire.bend as Wr
import ../../laws/bound.bend as Bound
import ./base.bend as LBound

def bo.head(f: Bool, +c: Bd.Cap, +b: Nat, +nl: Nat, o: Bool, +sd: Nat, +n: Nat) -> {Bd.out.head(f, c, b, nl, o, sd, n) == Bound.bd_out.head(f, c, b, nl, o, sd, n) : Bd.St & Bd.Act}:
  match f:
    case True{}:
      {==}
    case False{}:
      {==}

def bo.tail(tr: Bool, +c: Bd.Cap, +b: Nat, +nl: Nat, o: Bool, +sd: Nat) -> {Bd.out.tail(tr, c, b, nl, o, sd) == (Bd.St{c, b, nl, o, sd}, Bound.bd_out.tail(tr)) : Bd.St & Bd.Act}:
  match tr:
    case True{}:
      {==}
    case False{}:
      {==}

def bo.go(t: Bool, c: Bd.Cap, +b: Nat, +nl: Nat, +sd: Nat, +n: Nat, +k: Nat, o: Bool) -> {Bd.out.go(t, c, b, nl, sd, n, k, o) == Bound.bd_out.go(t, c, b, nl, sd, n, k, o) : Bd.St & Bd.Act}:
  match t:
    case False{}:
      match c:
        case Bd.Cap{+cb, +ck, +ct}:
          bo.head(Bool.or(Nat.is_lt(cb, b), Nat.is_le(ck, nl)), Bd.Cap{cb, ck, ct}, Nat.add(b, n), Nat.add(nl, k), o, sd, n)
    case True{}:
      match c:
        case Bd.Cap{+cb, +ck, +ct}:
          bo.tail(Nat.is_lt(Nat.add(Nat.add(cb, cb), 8n), Nat.add(sd, n)), Bd.Cap{cb, ck, ct}, Nat.add(b, n), Nat.add(nl, k), o, Nat.add(sd, n))

def Bound.bound_out_exact(s, n, k, o):
  match s:
    case Bd.St{c, +b, +nl, op, +sd}:
      match c:
        case Bd.Cap{+cb, +ck, +ct}:
          bo.go(ct, Bd.Cap{cb, ck, ct}, b, nl, sd, n, k, o)
