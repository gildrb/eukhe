# eukhe: the proof of LAW redirect_input_error_wins
#
# PROOF: the query holds the pieces code=c, error=e, error_description=d (LQ.qa.kv); an error value wins and takes its description.

import Base
import ../../bend/redirect_input.bend as Ri
import ../../laws/redirect_input.bend as RedirectInput
import ./base/text.bend as LT
import ./base/parse.bend as LP
import ./base/carry.bend as LC
import ./base/query.bend as LQ

def ri_ew.fin(+e: String, +d: String, +c: String, he: {RedirectInput.ri_value(e) == True{} : Bool}, hd: {RedirectInput.ri_value(d) == True{} : Bool}) -> {LQ.qa.ans([Ri.Param{Ri.decode("code"), c}, Ri.Param{Ri.decode("error"), e}, Ri.Param{Ri.decode("error_description"), d}]) == Ri.Failed{Ri.FProvider{e, Some{d}}} : Ri.Answer}:
  match e:
    case SNil{}:
      LT.rt.absurdF({LQ.qa.ans([Ri.Param{Ri.decode("code"), c}, Ri.Param{Ri.decode("error"), SNil{}}, Ri.Param{Ri.decode("error_description"), d}]) == Ri.Failed{Ri.FProvider{SNil{}, Some{d}}} : Ri.Answer}, he)
    case SCon{+e0, +e1}:
      match d:
        case SNil{}:
          LT.rt.absurdF({LQ.qa.ans([Ri.Param{Ri.decode("code"), c}, Ri.Param{Ri.decode("error"), SCon{e0, e1}}, Ri.Param{Ri.decode("error_description"), SNil{}}]) == Ri.Failed{Ri.FProvider{SCon{e0, e1}, Some{SNil{}}}} : Ri.Answer}, hd)
        case SCon{+d0, +d1}:
          {==}

def RedirectInput.redirect_input_error_wins(b, c, e, d, nq, vc, ve, vd):
  +hc = vc
  +he = ve
  +hd = vd
  +X2 = String.append("&error_description=", d)
  +X1 = String.append("&error=", String.append(e, X2))
  +q = String.append("code=", String.append(c, X1))
  +R1 = String.append("error", SCon{'=', String.append(e, X2)})
  +R2 = String.append("error_description", SCon{'=', d})
  +ps = {[Ri.Param{Ri.decode("code"), c}, Ri.Param{Ri.decode("error"), e}, Ri.Param{Ri.decode("error_description"), d}] : List<&2, Ri.Param>}
  +calm = LT.rt.calm_app(c, X1, LC.rq.calm(c, hc), LT.rt.calm_app(e, X2, LC.rq.calm(e, he), LC.rq.calm(d, hd)))
  +nh = LT.rt.lacks_app(c, X1, '#', LC.rq.lacks(c, 4n, hc), LT.rt.lacks_app(e, X2, '#', LC.rq.lacks(e, 4n, he), LC.rq.lacks(d, 4n, hd)))
  +hn = LC.rq.nofs_tail("code=", String.append(c, X1), LC.rq.nofs_tail(c, X1, LC.rq.nofs_tail("&error=", String.append(e, X2), LC.rq.nofs_tail(e, X2, LC.rq.nofs_tail("&error_description=", d, LC.rq.nofs(d, hd), LC.rq.ne(d, hd)), {==}), LT.rt.ne_app(e, '&', String.append("error_description=", d))), {==}), LT.rt.ne_app(c, '&', String.append("error=", String.append(e, X2))))
  +E2 = Equal.trans(List<&2, Ri.Param>, Ri.params(R1), Ri.Param{Ri.decode("error"), e} <> Ri.params(R2), [Ri.Param{Ri.decode("error"), e}, Ri.Param{Ri.decode("error_description"), d}], LQ.qa.kv("error", e, R2, {==}, he, LC.rq.lacks(e, 2n, he)), Equal.cong(List<&2, Ri.Param>, List<&2, Ri.Param>, z => Ri.Param{Ri.decode("error"), e} <> z, Ri.params(R2), [Ri.Param{Ri.decode("error_description"), d}], LQ.qa.kv1("error_description", d, {==}, hd, LC.rq.lacks(d, 2n, hd))))
  +E = Equal.trans(List<&2, Ri.Param>, Ri.params(q), Ri.Param{Ri.decode("code"), c} <> Ri.params(R1), ps, LQ.qa.kv("code", c, R1, {==}, hc, LC.rq.lacks(c, 2n, hc)), Equal.cong(List<&2, Ri.Param>, List<&2, Ri.Param>, z => Ri.Param{Ri.decode("code"), c} <> z, Ri.params(R1), [Ri.Param{Ri.decode("error"), e}, Ri.Param{Ri.decode("error_description"), d}], E2))
  Equal.trans(Ri.Answer, Ri.parse(String.append(b, SCon{'?', q})), LQ.qa.ans(ps), Ri.Failed{Ri.FProvider{e, Some{d}}}, LQ.qa.addr(b, q, q, ps, nq, calm, nh, LQ.qa.keep(q, hn), E), ri_ew.fin(e, d, c, he, hd))
