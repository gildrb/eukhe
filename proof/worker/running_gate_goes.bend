# eukhe: the proof of LAW running_gate_goes
#
# PROOF of LAW running_gate_goes: by the kind: 0 and 2 or more compute;
# kind 1 contradicts the premise.

import Base
import ../../bend/worker.bend as Wk
import ../../laws/worker.bend as Worker
import ./base.bend as LAWorker

def Worker.running_gate_goes(p, k, n, kind, id, other):
  match kind:
    case 0n:
      {==}
    case 1n:
      LAWorker.wb_absurd_tf({Wk.step(Wk.St{Wk.Run{}, p, k, n}, Wk.Gate{1n, id}) == (Wk.St{Wk.Run{}, None{}, k, n}, Wk.Go{}) : Wk.St & Wk.Verdict}, other)
    case 2n+x:
      {==}
