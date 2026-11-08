# eukhe: the proof of LAW headless_settle_kernel_jobs_never_done
#
# PROOF: whatever comes before it, a running kernel job makes the run
# pending (hs.stays).

import Base
import ../../laws/headless_settle.bend as HeadlessSettle
import ./base.bend as LAHeadlessSettle

def HeadlessSettle.headless_settle_kernel_jobs_never_done(b, j, k, c, w, x, u, l):
  match b:
    case True{}:
      LAHeadlessSettle.hs.stays(l)
    case False{}:
      match j:
        case 0n:
          LAHeadlessSettle.hs.stays(l)
        case 1n+p:
          LAHeadlessSettle.hs.stays(l)
