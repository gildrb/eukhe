# eukhe: the proof of LAW redirect_input_first_value
#
# PROOF: the query holds the pieces code= (empty value), code=c, code=d in order (LQ.qa.cons, LQ.qa.kv); the first name match with a non-empty value is c.

import Base
import ../../bend/redirect_input.bend as Ri
import ../../laws/redirect_input.bend as RedirectInput
import ./base/text.bend as LT
import ./base/parse.bend as LP
import ./base/carry.bend as LC
import ./base/query.bend as LQ

def ri_fv.fin(+c: String, +d: String, hc: {RedirectInput.ri_value(c) == True{} : Bool}) -> {LQ.qa.ans([Ri.Param{Ri.decode("code"), Ri.decode(SNil{})}, Ri.Param{Ri.decode("code"), c}, Ri.Param{Ri.decode("code"), d}]) == Ri.Pasted{c, None{}} : Ri.Answer}:
  match c:
    case SNil{}:
      LT.rt.absurdF({LQ.qa.ans([Ri.Param{Ri.decode("code"), Ri.decode(SNil{})}, Ri.Param{Ri.decode("code"), SNil{}}, Ri.Param{Ri.decode("code"), d}]) == Ri.Pasted{SNil{}, None{}} : Ri.Answer}, hc)
    case SCon{+c0, +c1}:
      {==}

def RedirectInput.redirect_input_first_value(b, c, d, nq, vc, vd):
  +hc = vc
  +hd = vd
  +X = String.append("&code=", d)
  +REST = String.append("code=", String.append(c, X))
  +q = String.append("code=", SCon{'&', REST})
  +ps = {[Ri.Param{Ri.decode("code"), Ri.decode(SNil{})}, Ri.Param{Ri.decode("code"), c}, Ri.Param{Ri.decode("code"), d}] : List<&2, Ri.Param>}
  +calm = LT.rt.calm_app(c, X, LC.rq.calm(c, hc), LC.rq.calm(d, hd))
  +nh = LT.rt.lacks_app(c, X, '#', LC.rq.lacks(c, 4n, hc), LC.rq.lacks(d, 4n, hd))
  +hn = LC.rq.nofs_tail("code=&code=", String.append(c, X), LC.rq.nofs_tail(c, X, LC.rq.nofs_tail("&code=", d, LC.rq.nofs(d, hd), LC.rq.ne(d, hd)), {==}), LT.rt.ne_app(c, '&', String.append("code=", d)))
  +E2 = Equal.trans(List<&2, Ri.Param>, Ri.params(REST), Ri.Param{Ri.decode("code"), c} <> Ri.params(String.append("code", SCon{'=', d})), [Ri.Param{Ri.decode("code"), c}, Ri.Param{Ri.decode("code"), d}], LQ.qa.kv("code", c, String.append("code", SCon{'=', d}), {==}, hc, LC.rq.lacks(c, 2n, hc)), Equal.cong(List<&2, Ri.Param>, List<&2, Ri.Param>, z => Ri.Param{Ri.decode("code"), c} <> z, Ri.params(String.append("code", SCon{'=', d})), [Ri.Param{Ri.decode("code"), d}], LQ.qa.kv1("code", d, {==}, hd, LC.rq.lacks(d, 2n, hd))))
  +e = Equal.trans(List<&2, Ri.Param>, Ri.params(q), Ri.Param{Ri.decode("code"), Ri.decode(SNil{})} <> Ri.params(REST), ps, LQ.qa.cons("code=", REST, {==}), Equal.cong(List<&2, Ri.Param>, List<&2, Ri.Param>, z => Ri.Param{Ri.decode("code"), Ri.decode(SNil{})} <> z, Ri.params(REST), [Ri.Param{Ri.decode("code"), c}, Ri.Param{Ri.decode("code"), d}], E2))
  Equal.trans(Ri.Answer, Ri.parse(String.append(b, SCon{'?', q})), LQ.qa.ans(ps), Ri.Pasted{c, None{}}, LQ.qa.addr(b, q, q, ps, nq, calm, nh, LQ.qa.keep(q, hn), e), ri_fv.fin(c, d, hc))
