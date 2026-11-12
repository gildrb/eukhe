# eukhe: the proof of LAW redirect_input_query_no_state
#
# PROOF: the query is the one piece code=c (LQ.qa.addr, LQ.qa.kv1); no piece is named state.

import Base
import ../../bend/redirect_input.bend as Ri
import ../../laws/redirect_input.bend as RedirectInput
import ./base/text.bend as LT
import ./base/parse.bend as LP
import ./base/carry.bend as LC
import ./base/query.bend as LQ

def ri_qns.fin(+c: String, hc: {RedirectInput.ri_value(c) == True{} : Bool}) -> {LQ.qa.ans([Ri.Param{Ri.decode("code"), c}]) == Ri.Pasted{c, None{}} : Ri.Answer}:
  match c:
    case SNil{}:
      LT.rt.absurdF({LQ.qa.ans([Ri.Param{Ri.decode("code"), SNil{}}]) == Ri.Pasted{SNil{}, None{}} : Ri.Answer}, hc)
    case SCon{+c0, +c1}:
      {==}

def RedirectInput.redirect_input_query_no_state(b, c, nq, vc):
  +hc = vc
  +q = String.append("code=", c)
  +ps = {[Ri.Param{Ri.decode("code"), c}] : List<&2, Ri.Param>}
  +us = LQ.qa.keep(q, LC.rq.nofs_tail("code=", c, LC.rq.nofs(c, hc), LC.rq.ne(c, hc)))
  Equal.trans(Ri.Answer, Ri.parse(String.append(b, SCon{'?', q})), LQ.qa.ans(ps), Ri.Pasted{c, None{}}, LQ.qa.addr(b, q, q, ps, nq, LC.rq.calm(c, hc), LC.rq.lacks(c, 4n, hc), us, LQ.qa.kv1("code", c, {==}, hc, LC.rq.lacks(c, 2n, hc))), ri_qns.fin(c, hc))
