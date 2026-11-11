# eukhe: the proof of LAW bound_skip_tail_clears: a tail's skip of some bytes computes

import Base
import ../../bend/bound.bend as Bd
import ../../bend/ffi_bound.bend as FBd
import ../../bend/wire.bend as Wr
import ../../laws/bound.bend as Bound
import ./base.bend as LBound

def Bound.bound_skip_tail_clears(b, l, bs, nl, op, sd, p, k, o):
  {==}
