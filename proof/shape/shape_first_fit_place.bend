# eukhe: the proof of LAW shape_first_fit_place
#
# PROOF: `first` of one shape is the spec's search from the text start
# (shape_first_of); its answer at char p is a reading r spelling the fit
# (LM.slm.got), found by the walk at the place after p chars (LM.slm.fp, by
# induction on the text); an AtStart walk answers only at the text start
# (LM.slm.may).

import Base
import ../../bend/shape.bend as S
import ../../laws/shape/match.bend as Shape
import ../../laws/shape/search.bend as ShapeSearch
import ./base/leftmost.bend as LM
import ./shape_first_of.bend as PFO

# the law's answer, from the place the walk found
def sfp.fin(+st: S.Start, +ps: List<&2, S.Piece>, +ends: Bool, +text: String, +p: Nat, +q: Nat, +cs: List<&2, Maybe<&2, String>>, +r: S.St, may: {ShapeSearch.sp_may(st, p) == True{} : Bool}, ef: {ShapeSearch.sp_fit(p, r) == S.Fit{p, q, cs} : S.Fit}, fp: LM.slm.FP(ps, ends, 1n+String.length(text), Shape.sp_ncaps(ps), SNil{}, text, r, p)) -> Sigma<&1, &1, String, u => Sigma<&1, &1, String, v => Sigma<&1, &1, S.St, r2 => {String.append(u, v) == text : String} & ({String.length(u) == p : Nat} & ({ShapeSearch.sp_may(st, p) == True{} : Bool} & ({ShapeSearch.sp_answer_at(ps, ends, text, u, v) == Some{r2} : Maybe<&2, S.St>} & {ShapeSearch.sp_fit(p, r2) == S.Fit{p, q, cs} : S.Fit})))>>>:
  (+a, (+b, (et, (el, ea)))) = fp
  (a, (b, (r, (Equal.sym(String, text, String.append(a, b), et), (el, (may, (ea, ef)))))))

def sfp.go(+st: S.Start, +ps: List<&2, S.Piece>, +ends: Bool, +text: String, +p: Nat, +q: Nat, +cs: List<&2, Maybe<&2, String>>, g: Sigma<&1, &1, S.St, r => {LM.slm.G(st, ps, ends, 1n+String.length(text), Shape.sp_ncaps(ps), SNil{}, text) == Some{S.Hit{r, p}} : Maybe<&2, S.Hit>} & {ShapeSearch.sp_fit(p, r) == S.Fit{p, q, cs} : S.Fit}>) -> Sigma<&1, &1, String, u => Sigma<&1, &1, String, v => Sigma<&1, &1, S.St, r2 => {String.append(u, v) == text : String} & ({String.length(u) == p : Nat} & ({ShapeSearch.sp_may(st, p) == True{} : Bool} & ({ShapeSearch.sp_answer_at(ps, ends, text, u, v) == Some{r2} : Maybe<&2, S.St>} & {ShapeSearch.sp_fit(p, r2) == S.Fit{p, q, cs} : S.Fit})))>>>:
  (+r, (+eg, ef)) = g
  +f = {1n+String.length(text) : Nat}
  +n = Shape.sp_ncaps(ps)
  sfp.fin(st, ps, ends, text, p, q, cs, r, LM.slm.may(st, ps, ends, f, n, text, r, p, eg), ef, LM.slm.fp(text, st, ps, ends, f, n, SNil{}, r, p, LM.slm.A(ps, ends, f, n, SNil{}, text), {==}, eg))

def ShapeSearch.shape_first_fit_place(st, ps, ends, text, p, q, cs, h):
  +sh = {S.Shape{st, ps, ends} : S.Shape}
  +G0 = LM.slm.G(st, ps, ends, 1n+String.length(text), Shape.sp_ncaps(ps), SNil{}, text)
  +h1 = Equal.trans(Maybe<&2, S.Found>, ShapeSearch.sp_first.hit(G0, 0n, k => None{}), S.first([sh], text), Some{S.Found{0n, S.Fit{p, q, cs}}}, Equal.sym(Maybe<&2, S.Found>, S.first([sh], text), ShapeSearch.sp_first([sh], text), ShapeSearch.shape_first_of([sh], text)), h)
  sfp.go(st, ps, ends, text, p, q, cs, LM.slm.got(G0, G0, {==}, p, q, cs, h1))
