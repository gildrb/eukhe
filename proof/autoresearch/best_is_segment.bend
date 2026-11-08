# eukhe: the proof of LAW best_is_segment

import Base
import ../../bend/autoresearch/state.bend as ArS
import ../../laws/autoresearch/history.bend as AutoresearchHistory
import ./step_refines_spec.bend as PStepRefinesSpec

def AutoresearchHistory.best_is_segment(s):
  match s:
    case ArS.St{c, +seg, mode, runs, pend}:
      PStepRefinesSpec.asr.last(runs, seg)
