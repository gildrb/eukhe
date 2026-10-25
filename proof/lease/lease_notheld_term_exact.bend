# eukhe: the proof of LAW lease_notheld_term_exact
# Both ways by induction (proof/lease/base/terms.bend).

import Base
import ../../laws/lease.bend as Lease
import ./base/terms.bend as LT

def Lease.lease_notheld_term_exact(k, h):
  (i => LT.lt.notheld_sound(k, h, i), c => LT.lt.notheld_complete(k, h, c))
