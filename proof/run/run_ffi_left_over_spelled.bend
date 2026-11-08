# eukhe: the proof of LAW run_ffi_left_over_spelled
#
# PROOF: the spelled request is the entry's encoding of it (LSp.sp.ask)
# before input that is not empty, which the entry refuses
# (run_ffi_refuses_left_over).

import Base
import ../../bend/ffi_run.bend as FRn
import ../../bend/wire.bend as Wr
import ../../laws/run/entry.bend as Run
import ./run_ffi_refuses_left_over.bend as PRunFfiRefusesLeftOver
import ./run_ffi_answers_spelled/spell.bend as LSp

def Run.run_ffi_left_over_spelled(a, fits, c, t):
  %LSp.sp.ask(a, SCon{c, t}) : {FRn.ffi(_) == Wr.err("run: input left over after the request") : String}
  Run.run_ffi_refuses_left_over(a, SCon{c, t}, fits, {==})
