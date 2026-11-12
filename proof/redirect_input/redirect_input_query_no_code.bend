# eukhe: the proof of LAW redirect_input_query_no_code
#
# PROOF: the query is the one piece state=s (LQ.qa.addr, LQ.qa.kv1): no piece is named error or code.

import Base
import ../../bend/redirect_input.bend as Ri
import ../../laws/redirect_input.bend as RedirectInput
import ./base/text.bend as LT
import ./base/parse.bend as LP
import ./base/carry.bend as LC
import ./base/query.bend as LQ

def RedirectInput.redirect_input_query_no_code(b, s, nq, vs):
  +hs = vs
  +q = String.append("state=", s)
  +ps = {[Ri.Param{Ri.decode("state"), s}] : List<&2, Ri.Param>}
  +us = LQ.qa.keep(q, LC.rq.nofs_tail("state=", s, LC.rq.nofs(s, hs), LC.rq.ne(s, hs)))
  Equal.trans(Ri.Answer, Ri.parse(String.append(b, SCon{'?', q})), LQ.qa.ans(ps), Ri.Failed{Ri.FMissing{}}, LQ.qa.addr(b, q, q, ps, nq, LC.rq.calm(s, hs), LC.rq.lacks(s, 4n, hs), us, LQ.qa.kv1("state", s, {==}, hs, LC.rq.lacks(s, 2n, hs))), {==})
