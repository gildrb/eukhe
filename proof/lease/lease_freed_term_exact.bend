# eukhe: the proof of LAW lease_freed_term_exact
# Both ways by induction (proof/lease/base/terms.bend).

import Base
import ../../laws/lease.bend as Lease
import ./base/terms.bend as LT

def Lease.lease_freed_term_exact(o, s):
  (i => LT.lt.freed_sound(o, s, i), c => LT.lt.freed_complete(o, s, c))
