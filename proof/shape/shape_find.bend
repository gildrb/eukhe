# eukhe: the proof of LAW shape_find
#
# PROOF: LSe.shf2.find, by induction along the search, the answer at each
# place by shape_first_reading.

import Base
import ../../bend/shape.bend as S
import ../../laws/shape/match.bend as Shape
import ../../laws/shape/search.bend as ShapeSearch
import ./base/search.bend as LSe

def ShapeSearch.shape_find(f, sh, a):
  LSe.shf2.find(f, sh, a)
