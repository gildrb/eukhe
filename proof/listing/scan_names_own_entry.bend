# eukhe: the proof of LAW scan_names_own_entry
#
# PROOF: the code's scan is the spec's verdicts entry by entry (ls.scan_go); each verdict is about its own entry (lsv.owns).

import Base
import ../../bend/staging.bend as Sg
import ../../bend/listing.bend as Ls
import ../../laws/listing.bend as Listing
import ./base/scan.bend as LA
import ./base/verdict.bend as LV

def Listing.scan_names_own_entry(es):
  %Equal.sym(List<&2, Ls.Pick>, Ls.scan.go(es, es), LA.ls.sp_scan.go(es, es), LA.ls.scan_go(es, es)) : {Listing.sp_own(_, es) == True{} : Bool}
  LV.lsv.owns(es, es)
