# eukhe: the proof of LAW worker_reply_verdict_unambiguous
#
# PROOF of LAW worker_reply_verdict_unambiguous: by the verdict
# (wr_verdict).

import Base
import ../../laws/worker.bend as Worker
import ./base/entry.bend as LAWorkerEntry

def Worker.worker_reply_verdict_unambiguous(x, rest, h):
  LAWorkerEntry.wr_verdict(x, rest, h)
