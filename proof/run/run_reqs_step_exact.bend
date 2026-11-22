# eukhe: the proof of LAW run_reqs_step_exact
#
# PROOF: run_reqs_exact's lemma rqx.step (case by case).

import Base
import ../../bend/run/request.bend as RnRequest
import ../../bend/run/state.bend as RnState
import ../../laws/run/machine.bend as RunMachine
import ./run_reqs_exact.bend as PRunReqsExact

def RunMachine.run_reqs_step_exact(t, pb, e, pa):
  PRunReqsExact.rqx.step(t, pb, e, pa)
