# eukhe: the proof of LAW bound_slice_keeps_window: the window's bytes are within the text (cuts within it) and its lines are some of the text's, so the span is the window's width and the dropped lines are the rest

import Base
import ../../bend/bound.bend as Bd
import ../../bend/ffi_bound.bend as FBd
import ../../bend/wire.bend as Wr
import ../../laws/bound.bend as Bound
import ./base.bend as LBound

def sk.of(t: Bool, w: Bd.Win, +len: Nat, +n: Nat, hb: {Nat.is_le(Bound.bd_win_bytes(w), len) == True{} : Bool}, hl: {Nat.is_le(Bound.bd_win_lines(w), n) == True{} : Bool}) -> {Nat.sub(Bound.bd_span_to(Bound.bd_slice_span(Bd.slice.of(t, len, n, w))), Bound.bd_span_from(Bound.bd_slice_span(Bd.slice.of(t, len, n, w)))) == Bound.bd_win_bytes(w) : Nat} & {Nat.add(Bound.bd_slice_lines(Bd.slice.of(t, len, n, w)), Bound.bd_win_lines(w)) == n : Nat}:
  match t:
    case False{}:
      match w:
        case Bd.Win{+kb, +kl}:
          (LBound.bnd.sub_zero(kb), LBound.bnd.sub_add(kl, n, hl))
    case True{}:
      match w:
        case Bd.Win{+kb, +kl}:
          (LBound.bnd.sub_sub(len, kb, hb), LBound.bnd.sub_add(kl, n, hl))

def sk.G(t: Bool, w: Bd.Win, len: Nat, n: Nat) -> Type:
  {Nat.sub(Bound.bd_span_to(Bound.bd_slice_span(Bd.slice.of(t, len, n, w))), Bound.bd_span_from(Bound.bd_slice_span(Bd.slice.of(t, len, n, w)))) == Bound.bd_win_bytes(w) : Nat} & {Nat.add(Bound.bd_slice_lines(Bd.slice.of(t, len, n, w)), Bound.bd_win_lines(w)) == n : Nat}

def Bound.bound_slice_keeps_window(c, x, hc, tc):
  match c:
    case Bd.Cap{+b, +k, +t}:
      match x:
        case Bd.Body{+xs, +o, +h, +tl, +m}:
          +w = Bd.window(Bd.Cap{b, k, t}, Bd.Body{xs, o, h, tl, m})
          +hb = LBound.bnd.win_bytes(Bd.Cap{b, k, t}, Bd.Body{xs, o, h, tl, m}, hc, tc)
          +hl = LBound.bnd.win_lines(Bd.Cap{b, k, t}, Bd.Body{xs, o, h, tl, m})
          %Equal.sym(Nat, Bd.total(xs), Bound.bd_total(xs), LBound.bnd.total(xs)) : sk.G(t, w, _, List.length(&2, Nat, xs))
          sk.of(t, w, Bound.bd_total(xs), List.length(&2, Nat, xs), hb, hl)
