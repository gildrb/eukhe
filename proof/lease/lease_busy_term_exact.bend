# eukhe: the proof of LAW lease_busy_term_exact
# Both ways by induction (proof/lease/base/terms.bend).

import Base
import ../../laws/lease.bend as Lease
import ./base/terms.bend as LT

def Lease.lease_busy_term_exact(s):
  (i => LT.lt.busy_sound(s, i), h => LT.lt.busy_complete(s, h))
