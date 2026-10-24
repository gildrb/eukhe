# eukhe: the proof of LAW bound_slice_exact: the text's bytes and window are the spec's; where the window lies computes

import Base
import ../../bend/bound.bend as Bd
import ../../bend/ffi_bound.bend as FBd
import ../../bend/wire.bend as Wr
import ../../laws/bound.bend as Bound
import ./base.bend as LBound

def bsl.of(w: Bd.Win, t: Bool, +len: Nat, +n: Nat) -> {Bd.slice.of(t, len, n, w) == Bound.bd_slice.of(t, len, n, w) : Bd.Slice}:
  match w:
    case Bd.Win{kb, kl}:
      match t:
        case False{}:
          {==}
        case True{}:
          {==}

def Bound.bound_slice_exact(c, x):
  match c:
    case Bd.Cap{+b, +k, +t}:
      match x:
        case Bd.Body{+xs, +o, +hc, +tc, +mc}:
          +cc = {Bd.Cap{b, k, t} : Bd.Cap}
          +bx = {Bd.Body{xs, o, hc, tc, mc} : Bd.Body}
          %LBound.bnd.total(xs) : {Bd.slice.of(t, Bd.total(xs), List.length(&2, Nat, xs), Bd.window(cc, bx)) == Bound.bd_slice.of(t, _, List.length(&2, Nat, xs), Bound.bd_window(cc, bx)) : Bd.Slice}
          %LBound.bnd.window(cc, bx) : {Bd.slice.of(t, Bd.total(xs), List.length(&2, Nat, xs), Bd.window(cc, bx)) == Bound.bd_slice.of(t, Bd.total(xs), List.length(&2, Nat, xs), _) : Bd.Slice}
          bsl.of(Bd.window(cc, bx), t, Bd.total(xs), List.length(&2, Nat, xs))
