# eukhe: the proof of LAW redirect_input_bare_code
#
# PROOF: the value is calm, so it cleans to itself (LQ.qa.clean); with no `?`, `://` or `#`, and no code=, state= or error= pair (LQ.qa.nocarry), the head is the code and there is no fragment.

import Base
import ../../bend/redirect_input.bend as Ri
import ../../laws/redirect_input.bend as RedirectInput
import ./base/text.bend as LT
import ./base/parse.bend as LP
import ./base/carry.bend as LC
import ./base/query.bend as LQ

def ri_bc.go(+c0: Char, +c1: String, vc: {RedirectInput.ri_value(SCon{c0, c1}) == True{} : Bool}) -> {Ri.parse(SCon{c0, c1}) == Ri.Pasted{SCon{c0, c1}, None{}} : Ri.Answer}:
  +hc = vc
  +C = {SCon{c0, c1} : String}
  %Equal.sym(String, Ri.clean(C), C, LQ.qa.clean(c0, c1, LC.rq.calm(C, hc))) : {Ri.parse.at(Ri.split(_, '?'), _) == Ri.Pasted{SCon{c0, c1}, None{}} : Ri.Answer}
  %Equal.sym(Maybe<&2, Ri.Cut>, Ri.split(C, '?'), None{}, LP.rp.split_none(C, '?', LC.rq.lacks(C, 5n, hc))) : {Ri.parse.at(_, C) == Ri.Pasted{SCon{c0, c1}, None{}} : Ri.Answer}
  %Equal.sym(Maybe<&2, String>, Ri.scheme(C), None{}, LP.rp.scheme_none(C, LC.rq.lacks(C, 6n, hc))) : {Ri.parse.scheme(_, C) == Ri.Pasted{SCon{c0, c1}, None{}} : Ri.Answer}
  %Equal.sym(Maybe<&2, Ri.Cut>, Ri.split(C, '#'), None{}, LP.rp.split_none(C, '#', LC.rq.lacks(C, 4n, hc))) : {Ri.parse.hash(_, C) == Ri.Pasted{SCon{c0, c1}, None{}} : Ri.Answer}
  %Equal.sym(Bool, Ri.carries(C), False{}, LQ.qa.nocarry(C, hc)) : {Ri.bare.at(_, Ri.carries(SNil{}), String.is_empty(C), C, SNil{}) == Ri.Pasted{SCon{c0, c1}, None{}} : Ri.Answer}
  {==}

def RedirectInput.redirect_input_bare_code(c, vc):
  match c:
    case SNil{}:
      LT.rt.absurdF({Ri.parse(SNil{}) == Ri.Pasted{SNil{}, None{}} : Ri.Answer}, vc)
    case SCon{+c0, +c1}:
      ri_bc.go(c0, c1, vc)
