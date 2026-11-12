# eukhe: the proof of LAW bound_slice_ends: a head span starts at 0, a tail span ends at the text's bytes, whatever the window

import Base
import ../../bend/bound.bend as Bd
import ../../bend/ffi_bound.bend as FBd
import ../../bend/wire.bend as Wr
import ../../laws/bound.bend as Bound
import ./base.bend as LBound

def se.head(w: Bd.Win, +len: Nat, +n: Nat) -> {Bound.bd_span_from(Bound.bd_slice_span(Bd.slice.of(False{}, len, n, w))) == 0n : Nat}:
  match w:
    case Bd.Win{kb, kl}:
      {==}

def se.tail(w: Bd.Win, +xs: List<&2, Nat>, +n: Nat) -> {Bound.bd_span_to(Bound.bd_slice_span(Bd.slice.of(True{}, Bd.total(xs), n, w))) == Bound.bd_total(xs) : Nat}:
  match w:
    case Bd.Win{kb, kl}:
      LBound.bnd.total(xs)

def Bound.bound_slice_ends(b, k, x):
  match x:
    case Bd.Body{+xs, +o, +hc, +tc, +mc}:
      (se.head(Bd.window(Bd.Cap{b, k, False{}}, Bd.Body{xs, o, hc, tc, mc}), Bd.total(xs), List.length(&2, Nat, xs)), se.tail(Bd.window(Bd.Cap{b, k, True{}}, Bd.Body{xs, o, hc, tc, mc}), xs, List.length(&2, Nat, xs)))
