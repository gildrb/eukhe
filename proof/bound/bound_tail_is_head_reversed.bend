# eukhe: the proof of LAW bound_tail_is_head_reversed: both windows keep the reversed lines; the library's reverse is the spec's (LBound.bnd.rev)

import Base
import ../../bend/bound.bend as Bd
import ../../bend/ffi_bound.bend as FBd
import ../../bend/wire.bend as Wr
import ../../laws/bound.bend as Bound
import ./base.bend as LBound

def Bound.bound_tail_is_head_reversed(b, k, xs, o, hc, tc, mc):
  %LBound.bnd.rev(xs) : {Bd.keep(List.reverse(&2, Nat, xs), k, b, tc) == Bd.keep(_, k, b, tc) : Bd.Win}
  {==}
