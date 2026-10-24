# eukhe: the proof of LAW bound_window_exact: a head's window is its lines', a tail's its lines' reversed

import Base
import ../../bend/bound.bend as Bd
import ../../bend/ffi_bound.bend as FBd
import ../../bend/wire.bend as Wr
import ../../laws/bound.bend as Bound
import ./base.bend as LBound

def Bound.bound_window_exact(c, x):
  LBound.bnd.window(c, x)
