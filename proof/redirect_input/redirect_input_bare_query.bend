# eukhe: the proof of LAW redirect_input_bare_query
#
# PROOF: the text is calm, so it cleans to itself (LQ.qa.clean); it holds no `?`, `://` or `#` (LP.rp.split_none, LP.rp.scheme_none), and its first piece is a code= pair (LP.rp.split_hit), so its pieces code=c, state=s answer (LQ.qa.one).

import Base
import ../../bend/redirect_input.bend as Ri
import ../../laws/redirect_input.bend as RedirectInput
import ./base/text.bend as LT
import ./base/parse.bend as LP
import ./base/carry.bend as LC
import ./base/query.bend as LQ

def ri_bq.fin(+c: String, +s: String, hc: {RedirectInput.ri_value(c) == True{} : Bool}, hs: {RedirectInput.ri_value(s) == True{} : Bool}) -> {LQ.qa.ans([Ri.Param{Ri.decode("code"), c}, Ri.Param{Ri.decode("state"), s}]) == Ri.Pasted{c, Some{s}} : Ri.Answer}:
  match c:
    case SNil{}:
      LT.rt.absurdF({LQ.qa.ans([Ri.Param{Ri.decode("code"), SNil{}}, Ri.Param{Ri.decode("state"), s}]) == Ri.Pasted{SNil{}, Some{s}} : Ri.Answer}, hc)
    case SCon{+c0, +c1}:
      match s:
        case SNil{}:
          LT.rt.absurdF({LQ.qa.ans([Ri.Param{Ri.decode("code"), SCon{c0, c1}}, Ri.Param{Ri.decode("state"), SNil{}}]) == Ri.Pasted{SCon{c0, c1}, Some{SNil{}}} : Ri.Answer}, hs)
        case SCon{+s0, +s1}:
          {==}

def RedirectInput.redirect_input_bare_query(c, s, vc, vs):
  +hc = vc
  +hs = vs
  +S = String.append("state", SCon{'=', s})
  +X = String.append("code", SCon{'=', c})
  +F = String.append("code=", String.append(c, String.append("&state=", s)))
  +ps = {[Ri.Param{Ri.decode("code"), c}, Ri.Param{Ri.decode("state"), s}] : List<&2, Ri.Param>}
  +cF = LT.rt.calm_app(c, String.append("&state=", s), LC.rq.calm(c, hc), LC.rq.calm(s, hs))
  +hn = LC.rq.nofs_tail("code=", String.append(c, String.append("&state=", s)), LC.rq.nofs_tail(c, String.append("&state=", s), LC.rq.nofs_tail("&state=", s, LC.rq.nofs(s, hs), LC.rq.ne(s, hs)), {==}), LT.rt.ne_app(c, '&', String.append("state=", s)))
  +E = Equal.trans(List<&2, Ri.Param>, Ri.params(F), Ri.Param{Ri.decode("code"), c} <> Ri.params(String.append("state", SCon{'=', s})), ps, LQ.qa.kv("code", c, String.append("state", SCon{'=', s}), {==}, hc, LC.rq.lacks(c, 2n, hc)), Equal.cong(List<&2, Ri.Param>, List<&2, Ri.Param>, z => Ri.Param{Ri.decode("code"), c} <> z, Ri.params(String.append("state", SCon{'=', s})), [Ri.Param{Ri.decode("state"), s}], LQ.qa.kv1("state", s, {==}, hs, LC.rq.lacks(s, 2n, hs))))
  %Equal.sym(String, Ri.clean(F), F, LQ.qa.clean('c', String.append("ode=", String.append(c, String.append("&state=", s))), cF)) : {Ri.parse.at(Ri.split(_, '?'), _) == Ri.Pasted{c, Some{s}} : Ri.Answer}
  %Equal.sym(Maybe<&2, Ri.Cut>, Ri.split(F, '?'), None{}, LP.rp.split_none(F, '?', LT.rt.lacks_app(c, String.append("&state=", s), LT.rt.mark(5n), LC.rq.lacks(c, 5n, hc), LC.rq.lacks(s, 5n, hs)))) : {Ri.parse.at(_, F) == Ri.Pasted{c, Some{s}} : Ri.Answer}
  %Equal.sym(Maybe<&2, String>, Ri.scheme(F), None{}, LP.rp.scheme_none(F, LT.rt.lacks_app(c, String.append("&state=", s), LT.rt.mark(6n), LC.rq.lacks(c, 6n, hc), LC.rq.lacks(s, 6n, hs)))) : {Ri.parse.scheme(_, F) == Ri.Pasted{c, Some{s}} : Ri.Answer}
  %Equal.sym(Maybe<&2, Ri.Cut>, Ri.split(F, '#'), None{}, LP.rp.split_none(F, '#', LT.rt.lacks_app(c, String.append("&state=", s), LT.rt.mark(4n), LC.rq.lacks(c, 4n, hc), LC.rq.lacks(s, 4n, hs)))) : {Ri.parse.hash(_, F) == Ri.Pasted{c, Some{s}} : Ri.Answer}
  %Equal.sym(List<&2, String>, String.split(F, '&'), X <> String.split(S, '&'), LP.rp.bs2(X, S, LC.rq.lacks(c, 2n, hc))) : {Ri.bare.at(Ri.carries.go(_), Ri.carries(SNil{}), String.is_empty(F), F, SNil{}) == Ri.Pasted{c, Some{s}} : Ri.Answer}
  %Equal.sym(Maybe<&2, Ri.Cut>, Ri.split(X, '='), Some{Ri.Cut{"code", c}}, LP.rp.split_hit("code", '=', c, {==}, {==})) : {Ri.bare.at(Bool.or(Ri.key(_), Ri.carries.go(String.split(S, '&'))), Ri.carries(SNil{}), String.is_empty(F), F, SNil{}) == Ri.Pasted{c, Some{s}} : Ri.Answer}
  %Equal.sym(String, Ri.unslash(F), F, LQ.qa.keep(F, hn)) : {Ri.from_params([_]) == Ri.Pasted{c, Some{s}} : Ri.Answer}
  Equal.trans(Ri.Answer, Ri.from_params([F]), LQ.qa.ans(ps), Ri.Pasted{c, Some{s}}, LQ.qa.one(F, ps, E), ri_bq.fin(c, s, hc, hs))
