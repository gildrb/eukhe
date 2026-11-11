# eukhe: the proof of LAW worker_reply_pick_unambiguous
#
# PROOF of LAW worker_reply_pick_unambiguous: field by field (wr_pick).

import Base
import ../../laws/worker.bend as Worker
import ./base/entry.bend as LAWorkerEntry

def Worker.worker_reply_pick_unambiguous(x, rest, h):
  LAWorkerEntry.wr_pick(x, rest, h)
