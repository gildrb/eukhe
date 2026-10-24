# eukhe: the proof of LAW infer_guard_ffi_step
# The chunk reads back (LWire.pw6.nat) and nothing is left; the stepper
# writes the model's feed as the spec does.

import Base
import ../../bend/infer_guard.bend as M
import ../../bend/ffi_infer_guard.bend as FG
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/infer_guard.bend as InferGuard
import ../base/wire.bend as LWire

def gfs.of(n: M.Next) -> {FG.step.of(n) == InferGuard.spell_next(n) : FG.St & String}:
  match n:
    case M.Goes{g}:
      {==}
    case M.Cuts{at, p}:
      {==}

def InferGuard.infer_guard_ffi_step(g, x, fits):
  %LWire.pw6.nat(x, "", fits) : {FG.step.chunk(g, _) == InferGuard.spell_next(M.feed(g, x)) : FG.St & String}
  gfs.of(M.feed(g, x))
