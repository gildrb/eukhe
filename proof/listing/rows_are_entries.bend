# eukhe: the proof of LAW rows_are_entries

import Base
import ../../bend/staging.bend as Sg
import ../../bend/listing.bend as Ls
import ../../laws/listing.bend as Listing
import ./base/order.bend as LO
import ./base/rows.bend as LR

# PROOF of LAW rows_are_entries: every row of rows.go is its entry's row
# (lr.Gk_go), the sort keeps that (lr.Gk_sort), and rows that are each
# their entry's row are the rows of their places (lr.fill).

def Listing.rows_are_entries(os):
  %LR.lr.seens(os) : {Ls.rows(os) == Listing.sp_fill(Listing.sp_ats(Ls.rows(os)), os, _) : List<&2, Ls.Row>}
  LR.lr.fill(Ls.rows(os), os, Ls.seens(os), LR.lr.Gk_sort(Ls.rows.go(os, Ls.seens(os), 0n), os, Ls.seens(os), 0n, LR.lr.Gk_go(os, Ls.seens(os), 0n)))
