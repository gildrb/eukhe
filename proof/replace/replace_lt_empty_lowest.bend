# eukhe: the proof of LAW replace_lt_empty_lowest
#
# PROOF of LAW replace_lt_empty_lowest: split the rank xs; both answers
# compute.

import Base
import ../../bend/replace.bend as Rp
import ../../laws/replace.bend as Replace

def Replace.replace_lt_empty_lowest(xs, y, ys):
  match xs:
    case Nil{}:
      {==}
    case x <> xr:
      {==}
