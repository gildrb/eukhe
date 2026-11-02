# eukhe: the proof of LAW shape_first_of
#
# PROOF: LSe.shf2.first, shape by shape, each search by shape_find.

import Base
import ../../bend/shape.bend as S
import ../../laws/shape/match.bend as Shape
import ../../laws/shape/search.bend as ShapeSearch
import ./base/search.bend as LSe

def ShapeSearch.shape_first_of(shs, text):
  LSe.shf2.first(shs, 1n+String.length(text), ShapeSearch.sp_start(text), 0n)
