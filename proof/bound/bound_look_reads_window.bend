# eukhe: the proof of LAW bound_look_reads_window: a look places its window as the slice does, and counts the stream's bytes and lines less the window's, which are within them (the window within the stored text, the stored text within the output)

import Base
import ../../bend/bound.bend as Bd
import ../../bend/ffi_bound.bend as FBd
import ../../bend/wire.bend as Wr
import ../../laws/bound.bend as Bound
import ./base.bend as LBound

def lr.lines(+nl: Nat, op: Bool, +kl: Nat, hl: {Nat.is_le(kl, Bound.bd_lines(nl, op)) == True{} : Bool}) -> {Nat.add(Nat.sub(Bd.lines(nl, op), kl), kl) == Bound.bd_lines(nl, op) : Nat}:
  match op:
    case False{}:
      LBound.bnd.sub_add(kl, nl, hl)
    case True{}:
      LBound.bnd.sub_add(kl, 1n+nl, hl)

def lr.of(w: Bd.Win, +c: Bd.Cap, +bs: Nat, +nl: Nat, +op: Bool, +x: Bd.Body, +len: Nat, +n: Nat, hb: {Nat.is_le(Bound.bd_win_bytes(w), bs) == True{} : Bool}, hl: {Nat.is_le(Bound.bd_win_lines(w), Bound.bd_lines(nl, op)) == True{} : Bool}) -> {Bound.bd_slice_span(Bound.bd_seen_slice(Bd.look.of(c, bs, nl, op, x, len, w))) == Bound.bd_slice_span(Bd.slice.of(Bd.Cap.tail(c), len, n, w)) : Bd.Span} & {Nat.add(Bound.bd_slice_bytes(Bound.bd_seen_slice(Bd.look.of(c, bs, nl, op, x, len, w))), Bound.bd_win_bytes(w)) == bs : Nat} & {Nat.add(Bound.bd_slice_lines(Bound.bd_seen_slice(Bd.look.of(c, bs, nl, op, x, len, w))), Bound.bd_win_lines(w)) == Bound.bd_lines(nl, op) : Nat}:
  match w:
    case Bd.Win{+kb, +kl}:
      ({==}, (LBound.bnd.sub_add(kb, bs, hb), lr.lines(nl, op, kl, hl)))

def Bound.bound_look_reads_window(c, bs, nl, op, sd, x, bytes, lines, hc, tc):
  match x:
    case Bd.Body{+xs, +o, +h, +tl, +m}:
      +bx = {Bd.Body{xs, o, h, tl, m} : Bd.Body}
      +w = Bd.window(c, bx)
      lr.of(w, c, bs, nl, op, bx, Bd.total(xs), List.length(&2, Nat, xs), LBound.bnd.le_trans(Bound.bd_win_bytes(w), Bound.bd_total(xs), bs, LBound.bnd.win_bytes(c, bx, hc, tc), bytes), LBound.bnd.le_trans(Bound.bd_win_lines(w), List.length(&2, Nat, xs), Bound.bd_lines(nl, op), LBound.bnd.win_lines(c, bx), lines))
