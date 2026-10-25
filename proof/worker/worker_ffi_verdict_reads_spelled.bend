# eukhe: the proof of LAW worker_ffi_verdict_reads_spelled
#
# PROOF of LAW worker_ffi_verdict_reads_spelled: by the verdict (wr_verdict).

import Base
import ../../laws/worker.bend as Worker
import ./base/entry.bend as LAWorkerEntry

def Worker.worker_ffi_verdict_reads_spelled(x, rest, h):
  LAWorkerEntry.wr_verdict(x, rest, h)
