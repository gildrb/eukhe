# eukhe: the proof of LAW shape_first_of
#
# PROOF: LSe.shf2.first, shape by shape, each place's answer by the
# matcher's proof (proof/shape/base/seek.bend).

import Base
import ../../bend/shape.bend as S
import ../../laws/shape/match.bend as Shape
import ../../laws/shape/search.bend as ShapeSearch
import ./base/search.bend as LSe

def ShapeSearch.shape_first_of(shs, text):
  LSe.shf2.first(shs, text, 0n)
