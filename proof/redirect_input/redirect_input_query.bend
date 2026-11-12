# eukhe: the proof of LAW redirect_input_query
#
# PROOF: the paste cleans to the address cleaned, then `?` and the query (LC.rq.query); the query without its trailing slashes (LP.rp.unslash) holds the pieces code=c and state=s (LQ.qa.kv), whose values decode to themselves.

import Base
import ../../bend/redirect_input.bend as Ri
import ../../laws/redirect_input.bend as RedirectInput
import ./base/text.bend as LT
import ./base/parse.bend as LP
import ./base/carry.bend as LC
import ./base/query.bend as LQ

def ri_q.fin(+c: String, +s: String, hc: {RedirectInput.ri_value(c) == True{} : Bool}, hs: {RedirectInput.ri_value(s) == True{} : Bool}) -> {LQ.qa.ans([Ri.Param{Ri.decode("code"), c}, Ri.Param{Ri.decode("state"), s}]) == Ri.Pasted{c, Some{s}} : Ri.Answer}:
  match c:
    case SNil{}:
      LT.rt.absurdF({LQ.qa.ans([Ri.Param{Ri.decode("code"), SNil{}}, Ri.Param{Ri.decode("state"), s}]) == Ri.Pasted{SNil{}, Some{s}} : Ri.Answer}, hc)
    case SCon{+c0, +c1}:
      match s:
        case SNil{}:
          LT.rt.absurdF({LQ.qa.ans([Ri.Param{Ri.decode("code"), SCon{c0, c1}}, Ri.Param{Ri.decode("state"), SNil{}}]) == Ri.Pasted{SCon{c0, c1}, Some{SNil{}}} : Ri.Answer}, hs)
        case SCon{+s0, +s1}:
          {==}

def RedirectInput.redirect_input_query(b, c, s, n, nq, vc, vs):
  +hc = vc
  +hs = vs
  +sl = RedirectInput.ri_slashes(n)
  +Y = String.append("&state=", s)
  +r = String.append("code=", String.append(c, Y))
  +q = String.append("code=", String.append(c, String.append(Y, sl)))
  +ps = {[Ri.Param{Ri.decode("code"), c}, Ri.Param{Ri.decode("state"), s}] : List<&2, Ri.Param>}
  +calm = LT.rt.calm_app(c, String.append(Y, sl), LC.rq.calm(c, hc), LT.rt.calm_app(s, sl, LC.rq.calm(s, hs), LT.rt.slash_calm(n)))
  +nh = LT.rt.lacks_app(c, String.append(Y, sl), '#', LC.rq.lacks(c, 4n, hc), LT.rt.lacks_app(s, sl, '#', LC.rq.lacks(s, 4n, hs), LC.rq.sl_lacks(n, '#', {==})))
  +A = Equal.cong(String, String, z => String.append("code=", z), String.append(String.append(c, Y), sl), String.append(c, String.append(Y, sl)), LT.rt.app_assoc(c, Y, sl))
  +hn = LC.rq.nofs_tail("code=", String.append(c, String.append("&state=", s)), LC.rq.nofs_tail(c, String.append("&state=", s), LC.rq.nofs_tail("&state=", s, LC.rq.nofs(s, hs), LC.rq.ne(s, hs)), {==}), LT.rt.ne_app(c, '&', String.append("state=", s)))
  +us = Equal.trans(String, Ri.unslash(q), Ri.unslash(String.append(r, sl)), r, Equal.cong(String, String, z => Ri.unslash(z), q, String.append(r, sl), Equal.sym(String, String.append(r, sl), q, A)), LP.rp.unslash(r, n, hn))
  +e = Equal.trans(List<&2, Ri.Param>, Ri.params(r), Ri.Param{Ri.decode("code"), c} <> Ri.params(String.append("state", SCon{'=', s})), ps, LQ.qa.kv("code", c, String.append("state", SCon{'=', s}), {==}, hc, LC.rq.lacks(c, 2n, hc)), Equal.cong(List<&2, Ri.Param>, List<&2, Ri.Param>, z => Ri.Param{Ri.decode("code"), c} <> z, Ri.params(String.append("state", SCon{'=', s})), [Ri.Param{Ri.decode("state"), s}], LQ.qa.kv1("state", s, {==}, hs, LC.rq.lacks(s, 2n, hs))))
  Equal.trans(Ri.Answer, Ri.parse(String.append(b, SCon{'?', q})), LQ.qa.ans(ps), Ri.Pasted{c, Some{s}}, LQ.qa.addr(b, q, r, ps, nq, calm, nh, us, e), ri_q.fin(c, s, hc, hs))
