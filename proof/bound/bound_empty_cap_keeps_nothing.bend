# eukhe: the proof of LAW bound_empty_cap_keeps_nothing: keep answers nothing for no line before it reads the text, and for no byte once it has a line

import Base
import ../../bend/bound.bend as Bd
import ../../bend/ffi_bound.bend as FBd
import ../../bend/wire.bend as Wr
import ../../laws/bound.bend as Bound
import ./base.bend as LBound

def ek.zero_b(+xs: List<&2, Nat>, k: Nat, +c: Nat) -> {Bd.keep(xs, k, 0n, c) == Bd.Win{0n, 0n} : Bd.Win}:
  match k:
    case 0n:
      {==}
    case 1n+j:
      {==}

def Bound.bound_empty_cap_keeps_nothing(b, k, t, x):
  match t:
    case False{}:
      match x:
        case Bd.Body{+xs, o, +hc, tc, mc}:
          ({==}, ek.zero_b(xs, k, hc))
    case True{}:
      match x:
        case Bd.Body{+xs, o, hc, +tc, mc}:
          ({==}, ek.zero_b(List.reverse(&2, Nat, xs), k, tc))
