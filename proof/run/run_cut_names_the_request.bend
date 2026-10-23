# eukhe: the proof of LAW run_cut_names_the_request

import Base
import ../../bend/run/request.bend as RnRequest
import ../../bend/run/state.bend as RnState
import ../../laws/run.bend as Run

# a noted reply cuts the request the run sent, and the retry's note names
# the retry's attempt
def cut_names_the_request(-retryable: Bool, -fin: RnState.Fin, -got: RnState.Got, -pa: RnState.Ph, -ctx: Nat, -n: Nat, -note: Nat, -log: List<&2, RnRequest.Sent>) -> {RnRequest.Reqs.step(RnState.Call{}, RnState.Go{RnState.Error{retryable, True{}}, fin, got}, pa, RnRequest.Reqs{ctx, n, note, log}) == RnRequest.Reqs{ctx, 1n+n, 1n+n, RnRequest.Cut{RnRequest.Req{ctx, note}} <> log} : RnRequest.Reqs}:
  {==}

def Run.run_cut_names_the_request(retryable, fin, got, pa, ctx, n, note, log):
  cut_names_the_request(retryable, fin, got, pa, ctx, n, note, log)
