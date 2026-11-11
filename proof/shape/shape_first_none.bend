# eukhe: the proof of LAW shape_first_none
#
# PROOF: `first` of one shape is the spec's search from the text start
# (shape_first_of), so the walk answers none (LM.slm.gone); an Anywhere walk
# then passes every place with no answer (LM.slm.nl, by induction on the
# text before the place), an AtStart one may start only at the text start,
# whose answer is its first test (LM.slm.none_top).

import Base
import ../../bend/shape.bend as S
import ../../laws/shape/match.bend as Shape
import ../../laws/shape/search.bend as ShapeSearch
import ./base/leftmost.bend as LM
import ./shape_first_of.bend as PFO

def ShapeSearch.shape_first_none(st, ps, ends, text, h, u, v, split, may):
  +sh = {S.Shape{st, ps, ends} : S.Shape}
  +f = {1n+String.length(text) : Nat}
  +n = Shape.sp_ncaps(ps)
  +G0 = LM.slm.G(st, ps, ends, f, n, SNil{}, text)
  +h1 = Equal.trans(Maybe<&2, S.Found>, ShapeSearch.sp_first.hit(G0, 0n, k => None{}), S.first([sh], text), None{}, Equal.sym(Maybe<&2, S.Found>, S.first([sh], text), ShapeSearch.sp_first([sh], text), ShapeSearch.shape_first_of([sh], text)), h)
  +g0 = LM.slm.gone(G0, G0, {==}, h1)
  +hG = Equal.trans(Maybe<&2, S.Hit>, LM.slm.G(st, ps, ends, f, n, SNil{}, String.append(u, v)), G0, None{}, Equal.cong(String, Maybe<&2, S.Hit>, z => LM.slm.G(st, ps, ends, f, n, SNil{}, z), String.append(u, v), text, split), g0)
  LM.slm.none_top(st, u, ps, ends, f, n, v, may, hG)
