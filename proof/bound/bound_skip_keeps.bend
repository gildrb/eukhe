# eukhe: the proof of LAW bound_skip_keeps: a head's skip, and a skip of no byte, compute

import Base
import ../../bend/bound.bend as Bd
import ../../bend/ffi_bound.bend as FBd
import ../../bend/wire.bend as Wr
import ../../laws/bound.bend as Bound
import ./base.bend as LBound

def Bound.bound_skip_keeps(b, l, bs, nl, op, sd, n, k, o):
  ({==}, {==})
