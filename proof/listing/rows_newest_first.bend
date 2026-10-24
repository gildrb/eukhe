# eukhe: the proof of LAW rows_newest_first

import Base
import ../../bend/staging.bend as Sg
import ../../bend/listing.bend as Ls
import ../../laws/listing.bend as Listing
import ./base/order.bend as LO
import ./base/rows.bend as LR

# PROOF of LAW rows_newest_first: rows.go makes rows of distinct places
# (lr.dist_go), and insertion of a row of a fresh place into rows in
# order keeps them in order (lr.sorted_sort): the order is strict, total
# on distinct places and transitive (proof/listing/base/order.bend).

def Listing.rows_newest_first(os):
  LR.lr.sorted_sort(Ls.rows.go(os, Ls.seens(os), 0n), LR.lr.dist_go(os, Ls.seens(os), 0n))
