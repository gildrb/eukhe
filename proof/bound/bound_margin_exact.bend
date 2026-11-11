# eukhe: the proof of LAW bound_margin_exact: the margin's lines, reverse and least are the spec's

import Base
import ../../bend/bound.bend as Bd
import ../../bend/ffi_bound.bend as FBd
import ../../bend/wire.bend as Wr
import ../../laws/bound.bend as Bound
import ./base.bend as LBound

def Bound.bound_margin_exact(c, x):
  LBound.bnd.margin(c, x)
