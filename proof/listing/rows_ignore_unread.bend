# eukhe: the proof of LAW rows_ignore_unread

import Base
import ../../bend/staging.bend as Sg
import ../../bend/listing.bend as Ls
import ../../laws/listing.bend as Listing
import ./base/order.bend as LO
import ./base/rows.bend as LR

# PROOF of LAW rows_ignore_unread: blanking keeps the entries
# (lr.seens_blank), and an entry the scan skips has no row whatever its
# cwd and times (lr.go_blank).

def Listing.rows_ignore_unread(os):
  %LR.lr.seens(os) : {Ls.rows(Listing.sp_blank(os, _)) == Ls.rows(os) : List<&2, Ls.Row>}
  %Equal.sym(List<&2, Sg.Seen>, Ls.seens(Listing.sp_blank(os, Ls.seens(os))), Ls.seens(os), LR.lr.seens_blank(os, Ls.seens(os))) : {Ls.sort(Ls.rows.go(Listing.sp_blank(os, Ls.seens(os)), _, 0n)) == Ls.rows(os) : List<&2, Ls.Row>}
  %Equal.sym(List<&2, Ls.Row>, Ls.rows.go(Listing.sp_blank(os, Ls.seens(os)), Ls.seens(os), 0n), Ls.rows.go(os, Ls.seens(os), 0n), LR.lr.go_blank(os, Ls.seens(os), 0n)) : {Ls.sort(_) == Ls.rows(os) : List<&2, Ls.Row>}
  {==}
