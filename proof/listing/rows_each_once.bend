# eukhe: the proof of LAW rows_each_once

import Base
import ../../bend/staging.bend as Sg
import ../../bend/listing.bend as Ls
import ../../laws/listing.bend as Listing
import ./base/order.bend as LO
import ./base/rows.bend as LR

# PROOF of LAW rows_each_once: the sort keeps the count of every place
# (lr.count_sort), and rows.go makes one row per listed entry, at its
# place (lr.count_go).

def Listing.rows_each_once(os, i):
  %LR.lr.seens(os) : {Listing.sp_count(i, Listing.sp_ats(Ls.rows(os))) == Listing.sp_count_listed(os, _, 0n, i) : Nat}
  Equal.trans(Nat, Listing.sp_count(i, Listing.sp_ats(Ls.sort(Ls.rows.go(os, Ls.seens(os), 0n)))), Listing.sp_count(i, Listing.sp_ats(Ls.rows.go(os, Ls.seens(os), 0n))), Listing.sp_count_listed(os, Ls.seens(os), 0n, i),
    LR.lr.count_sort(Ls.rows.go(os, Ls.seens(os), 0n), i), LR.lr.count_go(os, Ls.seens(os), 0n, i))
