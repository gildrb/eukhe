# eukhe: the proof of LAW bound_keep_exact: the model's keep is the spec's, by the count of lines that fit

import Base
import ../../bend/bound.bend as Bd
import ../../bend/ffi_bound.bend as FBd
import ../../bend/wire.bend as Wr
import ../../laws/bound.bend as Bound
import ./base.bend as LBound

def Bound.bound_keep_exact(xs, k, b, c):
  LBound.bnd.keep(xs, k, b, c)
