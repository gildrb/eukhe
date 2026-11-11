# eukhe: the proof of LAW scan_lists_legacy
#
# PROOF: the code's scan is the spec's verdicts (ls.scan_go); an entry's verdict lists n as a legacy file exactly when it is `<n>.jsonl` (lst.same_stem: the stem the code cuts is n exactly then) and n is free among all entries (lsv.legacy1), folded over the entries (lsv.legacies).

import Base
import ../../bend/staging.bend as Sg
import ../../bend/listing.bend as Ls
import ../../laws/listing.bend as Listing
import ./base/scan.bend as LA
import ./base/verdict.bend as LV

def Listing.scan_lists_legacy(es, n):
  %Equal.sym(List<&2, Ls.Pick>, Ls.scan.go(es, es), LA.ls.sp_scan.go(es, es), LA.ls.scan_go(es, es)) : {Listing.sp_has_legacy(n, _) == Bool.and(Listing.sp_file_named(n, es), Listing.sp_legacy_free(n, es)) : Bool}
  LV.lsv.legacies(n, es, es)
