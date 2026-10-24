# eukhe: the proof of LAW infer_guard_ffi_open
# The window reads back (LWire.pw6.nat) and nothing is left.

import Base
import ../../bend/infer_guard.bend as M
import ../../bend/ffi_infer_guard.bend as FG
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/infer_guard.bend as InferGuard
import ../base/wire.bend as LWire

def InferGuard.infer_guard_ffi_open(k, fits):
  %LWire.pw6.nat(k, "", fits) : {FG.open.go(_) == (FG.Live{M.start(k)}, "") : FG.St & String}
  {==}
