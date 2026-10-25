# eukhe: the proof of LAW worker_ffi_st_reads_spelled
#
# PROOF of LAW worker_ffi_st_reads_spelled: field by field (wr_st).

import Base
import ../../laws/worker.bend as Worker
import ./base/entry.bend as LAWorkerEntry

def Worker.worker_ffi_st_reads_spelled(x, rest, h):
  LAWorkerEntry.wr_st(x, rest, h)
