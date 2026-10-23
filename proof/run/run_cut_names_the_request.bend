# eukhe: the proof of LAW run_cut_names_the_request

import Base
import ../../bend/run.bend as Rn
import ../../LAWS.bend as Laws

# a noted reply cuts the request the run sent, and the retry's note names
# the retry's attempt
def cut_names_the_request(-retryable: Bool, -fin: Rn.Fin, -got: Rn.Got, -pa: Rn.Ph, -ctx: Nat, -n: Nat, -note: Nat, -log: List<&2, Rn.Sent>) -> {Rn.Reqs.step(Rn.Call{}, Rn.Go{Rn.Error{retryable, True{}}, fin, got}, pa, Rn.Reqs{ctx, n, note, log}) == Rn.Reqs{ctx, 1n+n, 1n+n, Rn.Cut{Rn.Req{ctx, note}} <> log} : Rn.Reqs}:
  {==}

def Laws.run_cut_names_the_request(retryable, fin, got, pa, ctx, n, note, log):
  cut_names_the_request(retryable, fin, got, pa, ctx, n, note, log)
