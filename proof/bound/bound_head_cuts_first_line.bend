# eukhe: the proof of LAW bound_head_cuts_first_line: the first line does not fit, so the fill keeps nothing and keep cuts that line

import Base
import ../../bend/bound.bend as Bd
import ../../bend/ffi_bound.bend as FBd
import ../../bend/wire.bend as Wr
import ../../laws/bound.bend as Bound
import ./base.bend as LBound

def Bound.bound_head_cuts_first_line(q, j, y, ys, o, p, tc, mc, over):
  %Equal.sym(Bool, Nat.is_le(y, 1n+q), False{}, over) : {Bd.keep.of(Bd.fill.pick(_, y, Bd.fill(ys, j, Nat.sub(1n+q, y))), y <> ys, 1n+p) == Bd.Win{1n+p, 1n} : Bd.Win} & {Bd.keep.of(Bd.fill.pick(_, y, Bd.fill(ys, j, Nat.sub(1n+q, y))), y <> ys, 0n) == Bd.Win{0n, 0n} : Bd.Win}
  ({==}, {==})
