# eukhe: the proof of LAW run_bound_exact
#
# PROOF: the bound of a configuration computes.

import Base
import ../../bend/run/measure.bend as RnMeasure
import ../../bend/run/state.bend as RnState
import ../../laws/run/model.bend as Run

def Run.run_bound_exact(cap, polls, retries, notes):
  {==}
