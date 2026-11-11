# eukhe: the proof of LAW dir_ffi_ended_stays_any_outcome
#
# PROOF: the entry answers the spelled request with the spelled loop after
# the model's tick (dir_ffi_answers_spelled), and the tick of an ended loop
# is that loop.

import Base
import ../../bend/director.bend as Dr
import ../../bend/ffi_director.bend as FDr
import ../../laws/director.bend as Director
import ./dir_ffi_answers_spelled.bend as PDirFfiAnswersSpelled

def Director.dir_ffi_ended_stays_any_outcome(c, n, s, o, vs, fits):
  Director.dir_ffi_answers_spelled(FDr.Req{c, Dr.Loop{n, s, Some{o}}, vs}, fits)
