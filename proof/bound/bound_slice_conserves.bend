# eukhe: the proof of LAW bound_slice_conserves: the window is within the text (whole lines are a part of it, a cut is within it), so its bytes and the rest add up

import Base
import ../../bend/bound.bend as Bd
import ../../bend/ffi_bound.bend as FBd
import ../../bend/wire.bend as Wr
import ../../laws/bound.bend as Bound
import ./base.bend as LBound

def bc.le_add_mono(y: Nat, +a: Nat, +b: Nat, h: {Nat.is_le(a, b) == True{} : Bool}) -> {Nat.is_le(Nat.add(y, a), Nat.add(y, b)) == True{} : Bool}:
  match y:
    case 0n:
      h
    case 1n++p:
      bc.le_add_mono(p, a, b, h)

def bc.take_le(ys: List<&2, Nat>, n: Nat) -> {Nat.is_le(Bound.bd_total(Bound.bd_take(ys, n)), Bound.bd_total(ys)) == True{} : Bool}:
  match ys:
    case Nil{}:
      {==}
    case +y <> +r:
      match n:
        case 0n:
          LBound.bnd.le0(Bound.bd_total(y <> r))
        case 1n++p:
          bc.le_add_mono(y, Bound.bd_total(Bound.bd_take(r, p)), Bound.bd_total(r), bc.take_le(r, p))

def bc.of(m: Nat, +ys: List<&2, Nat>, c: Nat, hc: {Nat.is_le(c, Bound.bd_total(ys)) == True{} : Bool}) -> {Nat.is_le(Bound.bd_win_bytes(Bd.keep.of(Bd.Win{Bound.bd_total(Bound.bd_take(ys, m)), m}, ys, c)), Bound.bd_total(ys)) == True{} : Bool}:
  match m:
    case 0n:
      match ys:
        case Nil{}:
          {==}
        case +y <> +r:
          match c:
            case 0n:
              LBound.bnd.le0(Bound.bd_total(y <> r))
            case 1n++p:
              hc
    case 1n++p:
      bc.take_le(ys, 1n+p)

def bc.keep(+ys: List<&2, Nat>, k: Nat, b: Nat, +c: Nat, hc: {Nat.is_le(c, Bound.bd_total(ys)) == True{} : Bool}) -> {Nat.is_le(Bound.bd_win_bytes(Bd.keep(ys, k, b, c)), Bound.bd_total(ys)) == True{} : Bool}:
  match k:
    case 0n:
      LBound.bnd.le0(Bound.bd_total(ys))
    case 1n++j:
      match b:
        case 0n:
          LBound.bnd.le0(Bound.bd_total(ys))
        case 1n++q:
          %LBound.bnd.fill(ys, 1n+j, 1n+q) : {Nat.is_le(Bound.bd_win_bytes(Bd.keep.of(_, ys, c)), Bound.bd_total(ys)) == True{} : Bool}
          bc.of(Bound.bd_count(ys, 1n+j, 1n+q), ys, c, hc)

def bc.head(w: Bd.Win, +len: Nat, n: Nat, hw: {Nat.is_le(Bound.bd_win_bytes(w), len) == True{} : Bool}) -> {Nat.add(Nat.sub(Bound.bd_span_to(Bound.bd_slice_span(Bd.slice.of(False{}, len, n, w))), Bound.bd_span_from(Bound.bd_slice_span(Bd.slice.of(False{}, len, n, w)))), Bound.bd_slice_bytes(Bd.slice.of(False{}, len, n, w))) == len : Nat}:
  match w:
    case Bd.Win{+kb, kl}:
      %Equal.sym(Nat, Nat.sub(kb, 0n), kb, LBound.bnd.sub_zero(kb)) : {Nat.add(_, Nat.sub(len, kb)) == len : Nat}
      LBound.bnd.add_sub(kb, len, hw)

def bc.tail(w: Bd.Win, +len: Nat, n: Nat) -> {Nat.add(Nat.sub(Bound.bd_span_to(Bound.bd_slice_span(Bd.slice.of(True{}, len, n, w))), Bound.bd_span_from(Bound.bd_slice_span(Bd.slice.of(True{}, len, n, w)))), Bound.bd_slice_bytes(Bd.slice.of(True{}, len, n, w))) == len : Nat}:
  match w:
    case Bd.Win{+kb, kl}:
      LBound.bnd.sub_add(Nat.sub(len, kb), len, LBound.bnd.sub_le(len, kb))

def Bound.bound_slice_conserves(c, x, hc, tc):
  match c:
    case Bd.Cap{+b, +k, t}:
      match t:
        case False{}:
          match x:
            case Bd.Body{+xs, o, +h, +tl, m}:
              +w = Bd.keep(xs, k, b, h)
              +n = List.length(&2, Nat, xs)
              %Equal.sym(Nat, Bd.total(xs), Bound.bd_total(xs), LBound.bnd.total(xs)) : {Nat.add(Nat.sub(Bound.bd_span_to(Bound.bd_slice_span(Bd.slice.of(False{}, _, n, w))), Bound.bd_span_from(Bound.bd_slice_span(Bd.slice.of(False{}, _, n, w)))), Bound.bd_slice_bytes(Bd.slice.of(False{}, _, n, w))) == Bound.bd_total(xs) : Nat}
              bc.head(w, Bound.bd_total(xs), n, bc.keep(xs, k, b, h, hc))
        case True{}:
          match x:
            case Bd.Body{+xs, o, +h, +tl, m}:
              +w = Bd.keep(List.reverse(&2, Nat, xs), k, b, tl)
              +n = List.length(&2, Nat, xs)
              %Equal.sym(Nat, Bd.total(xs), Bound.bd_total(xs), LBound.bnd.total(xs)) : {Nat.add(Nat.sub(Bound.bd_span_to(Bound.bd_slice_span(Bd.slice.of(True{}, _, n, w))), Bound.bd_span_from(Bound.bd_slice_span(Bd.slice.of(True{}, _, n, w)))), Bound.bd_slice_bytes(Bd.slice.of(True{}, _, n, w))) == Bound.bd_total(xs) : Nat}
              bc.tail(w, Bound.bd_total(xs), n)
