# eukhe: the proof of LAW worker_ffi_pick_reads_spelled
#
# PROOF of LAW worker_ffi_pick_reads_spelled: field by field (wr_pick).

import Base
import ../../laws/worker.bend as Worker
import ./base/entry.bend as LAWorkerEntry

def Worker.worker_ffi_pick_reads_spelled(x, rest, h):
  LAWorkerEntry.wr_pick(x, rest, h)
