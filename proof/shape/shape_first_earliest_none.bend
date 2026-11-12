# eukhe: the proof of LAW shape_first_earliest_none
#
# PROOF: every shape answers none alone, so each one's search answers none
# and `first` reaches the end of the list (LE.sfe.none).

import Base
import ../../bend/shape.bend as S
import ../../laws/shape/match.bend as Shape
import ../../laws/shape/search.bend as ShapeSearch
import ./base/earliest.bend as LE

def ShapeSearch.shape_first_earliest_none(shs, text, none):
  LE.sfe.none(shs, text, 0n, none)
