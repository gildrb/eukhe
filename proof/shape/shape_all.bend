# eukhe: the proof of LAW shape_all
#
# PROOF: LSe.shf2.all, place by place, the answer at each tried place by the
# matcher's proof (proof/shape/base/seek.bend).

import Base
import ../../bend/shape.bend as S
import ../../laws/shape/match.bend as Shape
import ../../laws/shape/search.bend as ShapeSearch
import ./base/search.bend as LSe

def ShapeSearch.shape_all(sh, text):
  LSe.shf2.all(sh, text)
