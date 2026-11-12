# eukhe: the proof of LAW forward_picks_one
#
# PROOF of LAW forward_picks_one: one message is kept past the cursor by
# the model's comparison c < q; either way its seqs are fw_one's (wb_one).

import Base
import ../../bend/worker.bend as Wk
import ../../laws/worker/forward.bend as WorkerForward
import ./base.bend as LAWorker

def WorkerForward.forward_picks_one(c, q, t, note):
  LAWorker.wb_one(Nat.is_lt(c, q), q, t)
