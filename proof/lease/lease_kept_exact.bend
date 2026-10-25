# eukhe: the proof of LAW lease_kept_exact
# Both ways by induction (proof/lease/base/terms.bend).

import Base
import ../../laws/lease.bend as Lease
import ./base/terms.bend as LT

def Lease.lease_kept_exact(k, o, s):
  (i => LT.lt.kept_sound(k, o, s, i), h => LT.lt.kept_complete(k, o, s, h))
