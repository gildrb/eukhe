# eukhe: the proof of LAW bound_head_keeps_most_lines: by induction on the lines: when m first lines fit, the first fits, so the fill takes it and then at least m - 1 of the rest; a cut keeps no fewer lines than an empty fill

import Base
import ../../bend/bound.bend as Bd
import ../../bend/ffi_bound.bend as FBd
import ../../bend/wire.bend as Wr
import ../../laws/bound.bend as Bound
import ./base.bend as LBound

def hm.more(+m: Nat, +x: Nat, w: Bd.Win, ih: {Nat.is_le(m, Bound.bd_win_lines(w)) == True{} : Bool}) -> {Nat.is_le(1n+m, Bound.bd_win_lines(Bd.fill.more(x, w))) == True{} : Bool}:
  match w:
    case Bd.Win{bb, l}:
      ih

def hm.fill(xs: List<&2, Nat>, k: Nat, +b: Nat, +m: Nat, many: {Nat.is_le(m, k) == True{} : Bool}, have: {Nat.is_le(m, List.length(&2, Nat, xs)) == True{} : Bool}, +fit: {Nat.is_le(Bound.bd_total(Bound.bd_take(xs, m)), b) == True{} : Bool}) -> {Nat.is_le(m, Bound.bd_win_lines(Bd.fill(xs, k, b))) == True{} : Bool}:
  match xs:
    case Nil{}:
      have
    case +x <> +rest:
      match k:
        case 0n:
          many
        case 1n++j:
          match m:
            case 0n:
              LBound.bnd.le0(Bound.bd_win_lines(Bd.fill(x <> rest, 1n+j, b)))
            case 1n++p:
              +fx = LBound.bnd.le_add_l(x, Bound.bd_total(Bound.bd_take(rest, p)), b, fit)
              %Equal.sym(Bool, Nat.is_le(x, b), True{}, fx) : {Nat.is_le(1n+p, Bound.bd_win_lines(Bd.fill.pick(_, x, Bd.fill(rest, j, Nat.sub(b, x))))) == True{} : Bool}
              hm.more(p, x, Bd.fill(rest, j, Nat.sub(b, x)), hm.fill(rest, j, Nat.sub(b, x), p, many, have, LBound.bnd.le_add_r(x, Bound.bd_total(Bound.bd_take(rest, p)), b, fit)))

# m <= 0 is m <= anything
def hm.z(m: Nat, +n: Nat, h: {Nat.is_le(m, 0n) == True{} : Bool}) -> {Nat.is_le(m, n) == True{} : Bool}:
  match m:
    case 0n:
      LBound.bnd.le0(n)
    case 1n+p:
      LBound.bnd.ft({Nat.is_le(1n+p, n) == True{} : Bool}, h)

def hm.of(w: Bd.Win, xs: List<&2, Nat>, c: Nat, +m: Nat, h: {Nat.is_le(m, Bound.bd_win_lines(w)) == True{} : Bool}) -> {Nat.is_le(m, Bound.bd_win_lines(Bd.keep.of(w, xs, c))) == True{} : Bool}:
  match w:
    case Bd.Win{bb, l}:
      match l:
        case 0n:
          hm.z(m, Bound.bd_win_lines(Bd.keep.none(xs, c)), h)
        case 1n+n:
          h

def Bound.bound_head_keeps_most_lines(q, k, x, m, many, have, fit):
  match k:
    case 0n:
      match x:
        case Bd.Body{xs, o, hc, tc, mc}:
          many
    case 1n++j:
      match x:
        case Bd.Body{+xs, o, +hc, tc, mc}:
          hm.of(Bd.fill(xs, 1n+j, 1n+q), xs, hc, m, hm.fill(xs, 1n+j, 1n+q, m, many, have, fit))
