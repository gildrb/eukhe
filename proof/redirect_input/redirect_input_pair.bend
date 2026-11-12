# eukhe: the proof of LAW redirect_input_pair
#
# PROOF: the pair is calm, so it cleans to itself (LQ.qa.clean); with no `?` or `://` it is cut at its `#` (LP.rp.split_hit), and neither value holds a code=, state= or error= pair (LQ.qa.nocarry), so the head is the code and the fragment the state.

import Base
import ../../bend/redirect_input.bend as Ri
import ../../laws/redirect_input.bend as RedirectInput
import ./base/text.bend as LT
import ./base/parse.bend as LP
import ./base/carry.bend as LC
import ./base/query.bend as LQ

def ri_pr.go(+c0: Char, +c1: String, +s0: Char, +s1: String, vc: {RedirectInput.ri_value(SCon{c0, c1}) == True{} : Bool}, vs: {RedirectInput.ri_value(SCon{s0, s1}) == True{} : Bool}) -> {Ri.parse(String.append(SCon{c0, c1}, SCon{'#', SCon{s0, s1}})) == Ri.Pasted{SCon{c0, c1}, Some{SCon{s0, s1}}} : Ri.Answer}:
  +hc = vc
  +hs = vs
  +C = {SCon{c0, c1} : String}
  +S = {SCon{s0, s1} : String}
  +T = {SCon{c0, String.append(c1, SCon{'#', S})} : String}
  +cT = LT.rt.calm_app(C, SCon{'#', S}, LC.rq.calm(C, hc), LC.rq.calm(S, hs))
  %Equal.sym(String, Ri.clean(T), T, LQ.qa.clean(c0, String.append(c1, SCon{'#', S}), cT)) : {Ri.parse.at(Ri.split(_, '?'), _) == Ri.Pasted{SCon{c0, c1}, Some{SCon{s0, s1}}} : Ri.Answer}
  %Equal.sym(Maybe<&2, Ri.Cut>, Ri.split(T, '?'), None{}, LP.rp.split_none(T, '?', LT.rt.lacks_app(C, SCon{'#', S}, LT.rt.mark(5n), LC.rq.lacks(C, 5n, hc), LC.rq.lacks(S, 5n, hs)))) : {Ri.parse.at(_, T) == Ri.Pasted{SCon{c0, c1}, Some{SCon{s0, s1}}} : Ri.Answer}
  %Equal.sym(Maybe<&2, String>, Ri.scheme(T), None{}, LP.rp.scheme_none(T, LT.rt.lacks_app(C, SCon{'#', S}, LT.rt.mark(6n), LC.rq.lacks(C, 6n, hc), LC.rq.lacks(S, 6n, hs)))) : {Ri.parse.scheme(_, T) == Ri.Pasted{SCon{c0, c1}, Some{SCon{s0, s1}}} : Ri.Answer}
  %Equal.sym(Maybe<&2, Ri.Cut>, Ri.split(T, '#'), Some{Ri.Cut{C, S}}, LP.rp.split_hit(C, '#', S, {==}, LC.rq.lacks(C, 4n, hc))) : {Ri.parse.hash(_, T) == Ri.Pasted{SCon{c0, c1}, Some{SCon{s0, s1}}} : Ri.Answer}
  %Equal.sym(Bool, Ri.carries(C), False{}, LQ.qa.nocarry(C, hc)) : {Ri.bare.at(_, Ri.carries(S), String.is_empty(C), C, S) == Ri.Pasted{SCon{c0, c1}, Some{SCon{s0, s1}}} : Ri.Answer}
  %Equal.sym(Bool, Ri.carries(S), False{}, LQ.qa.nocarry(S, hs)) : {Ri.bare.at(False{}, _, String.is_empty(C), C, S) == Ri.Pasted{SCon{c0, c1}, Some{SCon{s0, s1}}} : Ri.Answer}
  {==}

def RedirectInput.redirect_input_pair(c, s, vc, vs):
  match c:
    case SNil{}:
      LT.rt.absurdF({Ri.parse(String.append(SNil{}, SCon{'#', s})) == Ri.Pasted{SNil{}, Some{s}} : Ri.Answer}, vc)
    case SCon{+c0, +c1}:
      match s:
        case SNil{}:
          LT.rt.absurdF({Ri.parse(String.append(SCon{c0, c1}, SCon{'#', SNil{}})) == Ri.Pasted{SCon{c0, c1}, Some{SNil{}}} : Ri.Answer}, vs)
        case SCon{+s0, +s1}:
          ri_pr.go(c0, c1, s0, s1, vc, vs)
