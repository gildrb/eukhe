# eukhe: the proof of LAW headless_settle_busy_never_done
#
# PROOF: a busy conversation makes the run pending at once (hs.stays).

import Base
import ../../laws/headless_settle.bend as HeadlessSettle
import ./base.bend as LAHeadlessSettle

def HeadlessSettle.headless_settle_busy_never_done(j, k, c, w, x, u, l):
  LAHeadlessSettle.hs.stays(l)
