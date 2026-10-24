# eukhe: the proof of LAW bound_window_within: a fill takes only lines within the bytes left and at most k of them; a cut is within the bytes

import Base
import ../../bend/bound.bend as Bd
import ../../bend/ffi_bound.bend as FBd
import ../../bend/wire.bend as Wr
import ../../laws/bound.bend as Bound
import ./base.bend as LBound

def bw.pick(fits: Bool, +x: Nat, w: Bd.Win, +b: Nat, +j: Nat, e: {Nat.is_le(x, b) == fits : Bool}, ih: {Nat.is_le(Bound.bd_win_bytes(w), Nat.sub(b, x)) == True{} : Bool} & {Nat.is_le(Bound.bd_win_lines(w), j) == True{} : Bool}) -> {Nat.is_le(Bound.bd_win_bytes(Bd.fill.pick(fits, x, w)), b) == True{} : Bool} & {Nat.is_le(Bound.bd_win_lines(Bd.fill.pick(fits, x, w)), 1n+j) == True{} : Bool}:
  match fits:
    case True{}:
      match w:
        case Bd.Win{+wb, +wl}:
          match ih:
            case (hb, hl):
              (LBound.bnd.le_add_sub(x, wb, b, e, hb), hl)
    case False{}:
      (LBound.bnd.le0(b), {==})

def bw.fill(xs: List<&2, Nat>, k: Nat, +b: Nat) -> {Nat.is_le(Bound.bd_win_bytes(Bd.fill(xs, k, b)), b) == True{} : Bool} & {Nat.is_le(Bound.bd_win_lines(Bd.fill(xs, k, b)), k) == True{} : Bool}:
  match xs:
    case Nil{}:
      (LBound.bnd.le0(b), LBound.bnd.le0(k))
    case +x <> +rest:
      match k:
        case 0n:
          (LBound.bnd.le0(b), {==})
        case 1n++j:
          bw.pick(Nat.is_le(x, b), x, Bd.fill(rest, j, Nat.sub(b, x)), b, j, {==}, bw.fill(rest, j, Nat.sub(b, x)))

def bw.of(w: Bd.Win, ys: List<&2, Nat>, c: Nat, +b: Nat, +j: Nat, hw: {Nat.is_le(Bound.bd_win_bytes(w), b) == True{} : Bool} & {Nat.is_le(Bound.bd_win_lines(w), 1n+j) == True{} : Bool}, hc: {Nat.is_le(c, b) == True{} : Bool}) -> {Nat.is_le(Bound.bd_win_bytes(Bd.keep.of(w, ys, c)), b) == True{} : Bool} & {Nat.is_le(Bound.bd_win_lines(Bd.keep.of(w, ys, c)), 1n+j) == True{} : Bool}:
  match w:
    case Bd.Win{wb, wl}:
      match wl:
        case 0n:
          match ys:
            case Nil{}:
              (LBound.bnd.le0(b), {==})
            case +y <> +r:
              match c:
                case 0n:
                  (LBound.bnd.le0(b), {==})
                case 1n++p:
                  (hc, LBound.bnd.le0(j))
        case 1n++m:
          hw

def bw.keep(+ys: List<&2, Nat>, k: Nat, b: Nat, +c: Nat, hc: {Nat.is_le(c, b) == True{} : Bool}) -> {Nat.is_le(Bound.bd_win_bytes(Bd.keep(ys, k, b, c)), b) == True{} : Bool} & {Nat.is_le(Bound.bd_win_lines(Bd.keep(ys, k, b, c)), k) == True{} : Bool}:
  match k:
    case 0n:
      (LBound.bnd.le0(b), {==})
    case 1n++j:
      match b:
        case 0n:
          ({==}, {==})
        case 1n++q:
          bw.of(Bd.fill(ys, 1n+j, 1n+q), ys, c, 1n+q, j, bw.fill(ys, 1n+j, 1n+q), hc)

def Bound.bound_window_within(c, x, hc, tc):
  match c:
    case Bd.Cap{+b, +k, t}:
      match t:
        case False{}:
          match x:
            case Bd.Body{+xs, o, +h, +tl, m}:
              bw.keep(xs, k, b, h, hc)
        case True{}:
          match x:
            case Bd.Body{+xs, o, +h, +tl, m}:
              bw.keep(List.reverse(&2, Nat, xs), k, b, tl, tc)
