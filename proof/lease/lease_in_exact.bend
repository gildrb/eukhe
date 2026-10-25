# eukhe: the proof of LAW lease_in_exact
# Both ways by induction (proof/lease/base/terms.bend).

import Base
import ../../laws/lease.bend as Lease
import ./base/terms.bend as LT

def Lease.lease_in_exact(x, q):
  (i => LT.lt.in_sound(x, q, i), h => LT.lt.in_complete(x, q, h))
