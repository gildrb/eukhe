# eukhe: the proof of LAW run_compact_goes_on_with_room
#
# PROOF: by computation on the compaction's kind.

import Base
import ../../bend/run/decision.bend as RnDecision
import ../../bend/run/state.bend as RnState
import ../../laws/run/model.bend as Run

def Run.run_compact_goes_on_with_room(over):
  match over:
    case True{}:
      ({==}, {==}, {==})
    case False{}:
      ({==}, {==}, {==})
