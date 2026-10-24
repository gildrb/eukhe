# eukhe: the proof of LAW bound_window_keeps_what_fits: lines within the cap all fit, so the window is all of them; the reverse holds the same bytes and lines

import Base
import ../../bend/bound.bend as Bd
import ../../bend/ffi_bound.bend as FBd
import ../../bend/wire.bend as Wr
import ../../laws/bound.bend as Bound
import ./base.bend as LBound

def bk.fill(ys: List<&2, Nat>, k: Nat, +b: Nat, +hb: {Nat.is_le(Bound.bd_total(ys), b) == True{} : Bool}, hl: {Nat.is_le(List.length(&2, Nat, ys), k) == True{} : Bool}) -> {Bd.fill(ys, k, b) == Bd.Win{Bound.bd_total(ys), List.length(&2, Nat, ys)} : Bd.Win}:
  match ys:
    case Nil{}:
      {==}
    case +y <> +r:
      match k:
        case 0n:
          LBound.bnd.ft({Bd.fill(y <> r, 0n, b) == Bd.Win{Bound.bd_total(y <> r), List.length(&2, Nat, y <> r)} : Bd.Win}, hl)
        case 1n++j:
          +ih = bk.fill(r, j, Nat.sub(b, y), LBound.bnd.le_add_r(y, Bound.bd_total(r), b, hb), hl)
          %Equal.sym(Bool, Nat.is_le(y, b), True{}, LBound.bnd.le_add_l(y, Bound.bd_total(r), b, hb)) : {Bd.fill.pick(_, y, Bd.fill(r, j, Nat.sub(b, y))) == Bd.Win{Nat.add(y, Bound.bd_total(r)), 1n+List.length(&2, Nat, r)} : Bd.Win}
          %Equal.sym(Bd.Win, Bd.fill(r, j, Nat.sub(b, y)), Bd.Win{Bound.bd_total(r), List.length(&2, Nat, r)}, ih) : {Bd.fill.pick(True{}, y, _) == Bd.Win{Nat.add(y, Bound.bd_total(r)), 1n+List.length(&2, Nat, r)} : Bd.Win}
          {==}

def bk.keep(k: Nat, b: Nat, +ys: List<&2, Nat>, +c: Nat, some: {Nat.is_lt(0n, b) == True{} : Bool}, hb: {Nat.is_le(Bound.bd_total(ys), b) == True{} : Bool}, hl: {Nat.is_le(List.length(&2, Nat, ys), k) == True{} : Bool}) -> {Bd.keep(ys, k, b, c) == Bd.Win{Bound.bd_total(ys), List.length(&2, Nat, ys)} : Bd.Win}:
  match k:
    case 0n:
      match ys:
        case Nil{}:
          {==}
        case +y <> +r:
          LBound.bnd.ft({Bd.keep(y <> r, 0n, b, c) == Bd.Win{Bound.bd_total(y <> r), List.length(&2, Nat, y <> r)} : Bd.Win}, hl)
    case 1n++j:
      match b:
        case 0n:
          LBound.bnd.ft({Bd.keep(ys, 1n+j, 0n, c) == Bd.Win{Bound.bd_total(ys), List.length(&2, Nat, ys)} : Bd.Win}, some)
        case 1n++q:
          match ys:
            case Nil{}:
              {==}
            case +y <> +r:
              %Equal.sym(Bd.Win, Bd.fill(y <> r, 1n+j, 1n+q), Bd.Win{Bound.bd_total(y <> r), List.length(&2, Nat, y <> r)}, bk.fill(y <> r, 1n+j, 1n+q, hb, hl)) : {Bd.keep.of(_, y <> r, c) == Bd.Win{Bound.bd_total(y <> r), List.length(&2, Nat, y <> r)} : Bd.Win}
              {==}

def bk.of(t: Bool, +len: Nat, +n: Nat) -> {Bd.slice.of(t, len, n, Bd.Win{len, n}) == Bd.Slice{Bd.Span{0n, len}, 0n, 0n} : Bd.Slice}:
  match t:
    case False{}:
      %Equal.sym(Nat, Nat.sub(len, len), 0n, LBound.bnd.sub_self(len)) : {Bd.Slice{Bd.Span{0n, len}, _, Nat.sub(n, n)} == Bd.Slice{Bd.Span{0n, len}, 0n, 0n} : Bd.Slice}
      %Equal.sym(Nat, Nat.sub(n, n), 0n, LBound.bnd.sub_self(n)) : {Bd.Slice{Bd.Span{0n, len}, 0n, _} == Bd.Slice{Bd.Span{0n, len}, 0n, 0n} : Bd.Slice}
      {==}
    case True{}:
      %Equal.sym(Nat, Nat.sub(len, len), 0n, LBound.bnd.sub_self(len)) : {Bd.Slice{Bd.Span{_, len}, _, Nat.sub(n, n)} == Bd.Slice{Bd.Span{0n, len}, 0n, 0n} : Bd.Slice}
      %Equal.sym(Nat, Nat.sub(n, n), 0n, LBound.bnd.sub_self(n)) : {Bd.Slice{Bd.Span{0n, len}, 0n, _} == Bd.Slice{Bd.Span{0n, len}, 0n, 0n} : Bd.Slice}
      {==}

def bk.rev_hb(+xs: List<&2, Nat>, +b: Nat, h: {Nat.is_le(Bound.bd_total(xs), b) == True{} : Bool}) -> {Nat.is_le(Bound.bd_total(Bound.bd_rev(xs)), b) == True{} : Bool}:
  %Equal.sym(Nat, Bound.bd_total(Bound.bd_rev(xs)), Bound.bd_total(xs), LBound.bnd.total_rev(xs)) : {Nat.is_le(_, b) == True{} : Bool}
  h

def bk.rev_hl(+xs: List<&2, Nat>, +k: Nat, h: {Nat.is_le(List.length(&2, Nat, xs), k) == True{} : Bool}) -> {Nat.is_le(List.length(&2, Nat, Bound.bd_rev(xs)), k) == True{} : Bool}:
  %Equal.sym(Nat, List.length(&2, Nat, Bound.bd_rev(xs)), List.length(&2, Nat, xs), LBound.bnd.len_rev(xs)) : {Nat.is_le(_, k) == True{} : Bool}
  h

def Bound.bound_window_keeps_what_fits(c, x, some, bytes, lines):
  match c:
    case Bd.Cap{+b, +k, t}:
      match t:
        case False{}:
          match x:
            case Bd.Body{+xs, o, +h, +tl, m}:
              %Equal.sym(Nat, Bd.total(xs), Bound.bd_total(xs), LBound.bnd.total(xs)) : {Bd.slice.of(False{}, _, List.length(&2, Nat, xs), Bd.keep(xs, k, b, h)) == Bd.Slice{Bd.Span{0n, Bound.bd_total(xs)}, 0n, 0n} : Bd.Slice}
              %Equal.sym(Bd.Win, Bd.keep(xs, k, b, h), Bd.Win{Bound.bd_total(xs), List.length(&2, Nat, xs)}, bk.keep(k, b, xs, h, some, bytes, lines)) : {Bd.slice.of(False{}, Bound.bd_total(xs), List.length(&2, Nat, xs), _) == Bd.Slice{Bd.Span{0n, Bound.bd_total(xs)}, 0n, 0n} : Bd.Slice}
              bk.of(False{}, Bound.bd_total(xs), List.length(&2, Nat, xs))
        case True{}:
          match x:
            case Bd.Body{+xs, o, +h, +tl, m}:
              +rs = Bound.bd_rev(xs)
              %Equal.sym(Nat, Bd.total(xs), Bound.bd_total(xs), LBound.bnd.total(xs)) : {Bd.slice.of(True{}, _, List.length(&2, Nat, xs), Bd.keep(List.reverse(&2, Nat, xs), k, b, tl)) == Bd.Slice{Bd.Span{0n, Bound.bd_total(xs)}, 0n, 0n} : Bd.Slice}
              %Equal.sym(List<&2, Nat>, List.reverse(&2, Nat, xs), rs, LBound.bnd.rev(xs)) : {Bd.slice.of(True{}, Bound.bd_total(xs), List.length(&2, Nat, xs), Bd.keep(_, k, b, tl)) == Bd.Slice{Bd.Span{0n, Bound.bd_total(xs)}, 0n, 0n} : Bd.Slice}
              %Equal.sym(Bd.Win, Bd.keep(rs, k, b, tl), Bd.Win{Bound.bd_total(rs), List.length(&2, Nat, rs)}, bk.keep(k, b, rs, tl, some, bk.rev_hb(xs, b, bytes), bk.rev_hl(xs, k, lines))) : {Bd.slice.of(True{}, Bound.bd_total(xs), List.length(&2, Nat, xs), _) == Bd.Slice{Bd.Span{0n, Bound.bd_total(xs)}, 0n, 0n} : Bd.Slice}
              %Equal.sym(Nat, Bound.bd_total(rs), Bound.bd_total(xs), LBound.bnd.total_rev(xs)) : {Bd.slice.of(True{}, Bound.bd_total(xs), List.length(&2, Nat, xs), Bd.Win{_, List.length(&2, Nat, rs)}) == Bd.Slice{Bd.Span{0n, Bound.bd_total(xs)}, 0n, 0n} : Bd.Slice}
              %Equal.sym(Nat, List.length(&2, Nat, rs), List.length(&2, Nat, xs), LBound.bnd.len_rev(xs)) : {Bd.slice.of(True{}, Bound.bd_total(xs), List.length(&2, Nat, xs), Bd.Win{Bound.bd_total(xs), _}) == Bd.Slice{Bd.Span{0n, Bound.bd_total(xs)}, 0n, 0n} : Bd.Slice}
              bk.of(True{}, Bound.bd_total(xs), List.length(&2, Nat, xs))
