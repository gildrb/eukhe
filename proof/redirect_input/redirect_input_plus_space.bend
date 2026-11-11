# eukhe: the proof of LAW redirect_input_plus_space
#
# PROOF: the query is the one piece code=c+d (LQ.qa.kv1d), whose value decodes with the `+` read as a space (LP.rp.dec_plus).

import Base
import ../../bend/redirect_input.bend as Ri
import ../../laws/redirect_input.bend as RedirectInput
import ./base/text.bend as LT
import ./base/parse.bend as LP
import ./base/carry.bend as LC
import ./base/query.bend as LQ

def ri_ps.fin(+c: String, +d: String, hc: {RedirectInput.ri_value(c) == True{} : Bool}) -> {LQ.qa.ans([Ri.Param{Ri.decode("code"), String.append(c, SCon{' ', d})}]) == Ri.Pasted{String.append(c, SCon{' ', d}), None{}} : Ri.Answer}:
  match c:
    case SNil{}:
      LT.rt.absurdF({LQ.qa.ans([Ri.Param{Ri.decode("code"), String.append(SNil{}, SCon{' ', d})}]) == Ri.Pasted{String.append(SNil{}, SCon{' ', d}), None{}} : Ri.Answer}, hc)
    case SCon{+c0, +c1}:
      {==}

def RedirectInput.redirect_input_plus_space(b, c, d, nq, vc, vd):
  +hc = vc
  +hd = vd
  +v = String.append(c, SCon{'+', d})
  +w = String.append(c, SCon{' ', d})
  +q = String.append("code=", v)
  +ps = {[Ri.Param{Ri.decode("code"), w}] : List<&2, Ri.Param>}
  +calm = LT.rt.calm_app(c, SCon{'+', d}, LC.rq.calm(c, hc), LC.rq.calm(d, hd))
  +nh = LT.rt.lacks_app(c, SCon{'+', d}, '#', LC.rq.lacks(c, 4n, hc), LC.rq.lacks(d, 4n, hd))
  +hn = LC.rq.nofs_tail("code=", v, LC.rq.nofs_tail(c, SCon{'+', d}, LC.rq.nofs_tail("+", d, LC.rq.nofs(d, hd), LC.rq.ne(d, hd)), {==}), LT.rt.ne_app(c, '+', d))
  +e = LQ.qa.kv1d("code", v, w, {==}, LP.rp.dec_plus(c, d, LC.rq.plain(c, hc), LC.rq.plain(d, hd)), LT.rt.lacks_app(c, SCon{'+', d}, '&', LC.rq.lacks(c, 2n, hc), LC.rq.lacks(d, 2n, hd)))
  Equal.trans(Ri.Answer, Ri.parse(String.append(b, SCon{'?', q})), LQ.qa.ans(ps), Ri.Pasted{w, None{}}, LQ.qa.addr(b, q, q, ps, nq, calm, nh, LQ.qa.keep(q, hn), e), ri_ps.fin(c, d, hc))
