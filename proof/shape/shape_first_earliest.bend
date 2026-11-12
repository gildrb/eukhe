# eukhe: the proof of LAW shape_first_earliest
#
# PROOF: `first` tries the shapes in order from index 0; each shape of pre
# answers none alone, so its search answers none and the index counts on;
# sh answers its fit alone, so `first` answers it at the count of pre
# (LE.sfe.go).

import Base
import ../../bend/shape.bend as S
import ../../laws/shape/match.bend as Shape
import ../../laws/shape/search.bend as ShapeSearch
import ./base/earliest.bend as LE

def ShapeSearch.shape_first_earliest(pre, sh, post, text, f, none, fit):
  +L = List.length(&2, S.Shape, pre)
  %LE.sfe.add_zero(L) : {S.first(List.append(&2, S.Shape, pre, sh <> post), text) == Some{S.Found{_, f}} : Maybe<&2, S.Found>}
  LE.sfe.go(pre, sh, post, text, 0n, f, none, fit)
