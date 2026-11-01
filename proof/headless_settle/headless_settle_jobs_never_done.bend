# eukhe: the proof of LAW headless_settle_jobs_never_done
#
# PROOF: busy or not, a running job makes the run pending (hs.stays).

import Base
import ../../laws/headless_settle.bend as HeadlessSettle
import ./base.bend as LAHeadlessSettle

def HeadlessSettle.headless_settle_jobs_never_done(b, j, k, c, w, x, u, l):
  match b:
    case True{}:
      LAHeadlessSettle.hs.stays(l)
    case False{}:
      LAHeadlessSettle.hs.stays(l)
