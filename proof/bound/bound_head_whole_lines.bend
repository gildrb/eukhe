# eukhe: the proof of LAW bound_head_whole_lines: the first line fits, so the fill takes it, and a fill's bytes are those of its first lines (LBound.bnd.fill)

import Base
import ../../bend/bound.bend as Bd
import ../../bend/ffi_bound.bend as FBd
import ../../bend/wire.bend as Wr
import ../../laws/bound.bend as Bound
import ./base.bend as LBound

def Bound.bound_head_whole_lines(q, k, y, ys, o, hc, tc, mc, fits):
  match k:
    case 0n:
      {==}
    case 1n++j:
      %Equal.sym(Bool, Nat.is_le(y, 1n+q), True{}, fits) : {Bound.bd_win_bytes(Bd.keep.of(Bd.fill.pick(_, y, Bd.fill(ys, j, Nat.sub(1n+q, y))), y <> ys, hc)) == Bound.bd_total(Bound.bd_take(y <> ys, Bound.bd_win_lines(Bd.keep.of(Bd.fill.pick(_, y, Bd.fill(ys, j, Nat.sub(1n+q, y))), y <> ys, hc)))) : Nat}
      %LBound.bnd.fill(ys, j, Nat.sub(1n+q, y)) : {Bound.bd_win_bytes(Bd.keep.of(Bd.fill.more(y, _), y <> ys, hc)) == Bound.bd_total(Bound.bd_take(y <> ys, Bound.bd_win_lines(Bd.keep.of(Bd.fill.more(y, _), y <> ys, hc)))) : Nat}
      {==}
