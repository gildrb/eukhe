# eukhe: the proof of LAW scan_lists_stores
#
# PROOF: the code's scan is the spec's verdicts (ls.scan_go); an entry's verdict lists n as a storage exactly when it is a storage directory named n (lsv.store1), folded over the entries (lsv.stores).

import Base
import ../../bend/staging.bend as Sg
import ../../bend/listing.bend as Ls
import ../../laws/listing.bend as Listing
import ./base/scan.bend as LA
import ./base/verdict.bend as LV

def Listing.scan_lists_stores(es, n):
  %Equal.sym(List<&2, Ls.Pick>, Ls.scan.go(es, es), LA.ls.sp_scan.go(es, es), LA.ls.scan_go(es, es)) : {Listing.sp_has_store(n, _) == Listing.sp_store_named(n, es) : Bool}
  LV.lsv.stores(n, es, es)
