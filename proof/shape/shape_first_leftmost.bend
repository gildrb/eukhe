# eukhe: the proof of LAW shape_first_leftmost
#
# PROOF: `first` of one shape is the spec's search from the text start
# (shape_first_of), the walk sp_find.go over the places of the text in
# order; its answer at char p is a reading at that place (LM.slm.got), and
# the walk passes every place before p with no answer there (LM.slm.lm, by
# induction on the text before the place, u).

import Base
import ../../bend/shape.bend as S
import ../../laws/shape/match.bend as Shape
import ../../laws/shape/search.bend as ShapeSearch
import ./base/leftmost.bend as LM
import ./shape_first_of.bend as PFO

def sfl.go(+st: S.Start, +ps: List<&2, S.Piece>, +ends: Bool, +text: String, +p: Nat, +q: Nat, +cs: List<&2, Maybe<&2, String>>, +u: String, +v: String, split: {String.append(u, v) == text : String}, early: {Nat.is_lt(String.length(u), p) == True{} : Bool}, g: Sigma<&1, &1, S.St, r => {LM.slm.G(st, ps, ends, 1n+String.length(text), Shape.sp_ncaps(ps), SNil{}, text) == Some{S.Hit{r, p}} : Maybe<&2, S.Hit>} & {ShapeSearch.sp_fit(p, r) == S.Fit{p, q, cs} : S.Fit}>) -> {ShapeSearch.sp_answer_at(ps, ends, text, u, v) == None{} : Maybe<&2, S.St>}:
  (+r, (eg, ef)) = g
  +f = {1n+String.length(text) : Nat}
  +n = Shape.sp_ncaps(ps)
  +hG = Equal.trans(Maybe<&2, S.Hit>, LM.slm.G(st, ps, ends, f, n, SNil{}, String.append(u, v)), LM.slm.G(st, ps, ends, f, n, SNil{}, text), Some{S.Hit{r, p}}, Equal.cong(String, Maybe<&2, S.Hit>, z => LM.slm.G(st, ps, ends, f, n, SNil{}, z), String.append(u, v), text, split), eg)
  LM.slm.lm(u, st, ps, ends, f, n, SNil{}, v, r, p, LM.slm.A(ps, ends, f, n, SNil{}, String.append(u, v)), {==}, hG, early)

def ShapeSearch.shape_first_leftmost(st, ps, ends, text, p, q, cs, h, u, v, split, early):
  +sh = {S.Shape{st, ps, ends} : S.Shape}
  +G0 = LM.slm.G(st, ps, ends, 1n+String.length(text), Shape.sp_ncaps(ps), SNil{}, text)
  +h1 = Equal.trans(Maybe<&2, S.Found>, ShapeSearch.sp_first.hit(G0, 0n, k => None{}), S.first([sh], text), Some{S.Found{0n, S.Fit{p, q, cs}}}, Equal.sym(Maybe<&2, S.Found>, S.first([sh], text), ShapeSearch.sp_first([sh], text), ShapeSearch.shape_first_of([sh], text)), h)
  sfl.go(st, ps, ends, text, p, q, cs, u, v, split, early, LM.slm.got(G0, G0, {==}, p, q, cs, h1))
