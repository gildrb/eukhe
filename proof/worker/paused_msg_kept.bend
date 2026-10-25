# eukhe: the proof of LAW paused_msg_kept
#
# PROOF of LAW paused_msg_kept: the step computes on a paused state; the
# model's append of the id is the spec's snoc (wb_snoc).

import Base
import ../../bend/worker.bend as Wk
import ../../laws/worker.bend as Worker
import ./base.bend as LAWorker

def Worker.paused_msg_kept(p, k, n, id):
  %LAWorker.wb_snoc(k, id) : {Wk.step(Wk.St{Wk.Paused{}, p, k, n}, Wk.Msg{id, False{}}) == (Wk.St{Wk.Paused{}, p, _, n}, Wk.Kept{}) : Wk.St & Wk.Verdict}
  {==}
