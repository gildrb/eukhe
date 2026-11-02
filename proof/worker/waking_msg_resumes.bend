# eukhe: the proof of LAW waking_msg_resumes
#
# PROOF of LAW waking_msg_resumes: the step computes on a paused state;
# the model's append of the id is the spec's snoc (wb_snoc).

import Base
import ../../bend/worker.bend as Wk
import ../../laws/worker.bend as Worker
import ./base.bend as LAWorker

def Worker.waking_msg_resumes(p, k, n, id):
  %LAWorker.wb_snoc(k, id) : {Wk.step(Wk.St{Wk.Paused{}, p, k, n}, Wk.Msg{id, True{}}) == (Wk.St{Wk.Run{}, p, Nil{}, n}, Wk.Release{_}) : Wk.St & Wk.Verdict}
  {==}
