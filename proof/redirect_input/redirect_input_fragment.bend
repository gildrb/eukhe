# eukhe: the proof of LAW redirect_input_fragment
#
# PROOF: the paste cleans to the scheme and address cleaned, `://` kept, then the calm fragment (LT.rt.clean_tail, LT.rt.unwrap_app); with no `?` the text after the first `://` (LP.rp.scheme_hit) is cut at its first `#` (LP.rp.split_hit), whose pieces code=c, state=s answer (LQ.qa.one).

import Base
import ../../bend/redirect_input.bend as Ri
import ../../laws/redirect_input.bend as RedirectInput
import ./base/text.bend as LT
import ./base/parse.bend as LP
import ./base/carry.bend as LC
import ./base/query.bend as LQ

def ri_fr.fin(+c: String, +s: String, hc: {RedirectInput.ri_value(c) == True{} : Bool}, hs: {RedirectInput.ri_value(s) == True{} : Bool}) -> {LQ.qa.ans([Ri.Param{Ri.decode("code"), c}, Ri.Param{Ri.decode("state"), s}]) == Ri.Pasted{c, Some{s}} : Ri.Answer}:
  match c:
    case SNil{}:
      LT.rt.absurdF({LQ.qa.ans([Ri.Param{Ri.decode("code"), SNil{}}, Ri.Param{Ri.decode("state"), s}]) == Ri.Pasted{SNil{}, Some{s}} : Ri.Answer}, hc)
    case SCon{+c0, +c1}:
      match s:
        case SNil{}:
          LT.rt.absurdF({LQ.qa.ans([Ri.Param{Ri.decode("code"), SCon{c0, c1}}, Ri.Param{Ri.decode("state"), SNil{}}]) == Ri.Pasted{SCon{c0, c1}, Some{SNil{}}} : Ri.Answer}, hs)
        case SCon{+s0, +s1}:
          {==}

def RedirectInput.redirect_input_fragment(b, h, c, s, nb, nh, vc, vs):
  +hc = vc
  +hs = vs
  +nb0 = nb
  +nh0 = nh
  +T = String.append(b, String.append("://", String.append(h, String.append("#code=", String.append(c, String.append("&state=", s))))))
  +F = String.append("code=", String.append(c, String.append("&state=", s)))
  +Q = {SCon{'#', F} : String}
  +H = Ri.compact(h)
  +B = Ri.unwrap(Ri.compact(b))
  +W = {SCon{'/', SCon{'/', H}} : String}
  +R = String.append(H, Q)
  +V = String.append(B, SCon{':', SCon{'/', SCon{'/', R}}})
  +Pp = String.append(b, String.append("://", h))
  +ps = {[Ri.Param{Ri.decode("code"), c}, Ri.Param{Ri.decode("state"), s}] : List<&2, Ri.Param>}
  +cq = LT.rt.calm_app(c, String.append("&state=", s), LC.rq.calm(c, hc), LC.rq.calm(s, hs))
  +E1 = Equal.sym(String, String.append(Pp, Q), String.append(b, String.append(String.append("://", h), Q)), LT.rt.app_assoc(b, String.append("://", h), Q))
  +E3 = Equal.trans(String, Ri.unwrap(Ri.compact(Pp)), Ri.unwrap(String.append(Ri.compact(b), SCon{':', W})), String.append(B, SCon{':', W}), Equal.cong(String, String, z => Ri.unwrap(z), Ri.compact(Pp), String.append(Ri.compact(b), SCon{':', W}), LT.rt.compact_app(b, String.append("://", h))), LT.rt.unwrap_app(Ri.compact(b), ':', W, {==}))
  +EV = Equal.trans(String, Ri.clean(T), Ri.clean(String.append(Pp, Q)), V, Equal.cong(String, String, z => Ri.clean(z), T, String.append(Pp, Q), E1), Equal.trans(String, Ri.clean(String.append(Pp, Q)), String.append(Ri.unwrap(Ri.compact(Pp)), Q), V, LT.rt.clean_tail(Pp, '#', F, cq), Equal.trans(String, String.append(Ri.unwrap(Ri.compact(Pp)), Q), String.append(String.append(B, SCon{':', W}), Q), V, Equal.cong(String, String, z => String.append(z, Q), Ri.unwrap(Ri.compact(Pp)), String.append(B, SCon{':', W}), E3), LT.rt.app_assoc(B, SCon{':', W}, Q))))
  +lkBc = LP.rp.lk_unwrap(Ri.compact(b), ':', LP.rp.lk_compact(b, ':', LT.rt.lacks_code(b, 58, LT.rt.and_l(RedirectInput.ri_lacks(b, 58), RedirectInput.ri_lacks(b, 63), nb0))))
  +lkBq = LP.rp.lk_unwrap(Ri.compact(b), '?', LP.rp.lk_compact(b, '?', LT.rt.lacks_code(b, 63, LT.rt.and_r(RedirectInput.ri_lacks(b, 58), RedirectInput.ri_lacks(b, 63), nb0))))
  +lkHq = LP.rp.lk_compact(h, '?', LT.rt.lacks_code(h, 63, LT.rt.and_l(RedirectInput.ri_lacks(h, 63), RedirectInput.ri_lacks(h, 35), nh0)))
  +lkHh = LP.rp.lk_compact(h, '#', LT.rt.lacks_code(h, 35, LT.rt.and_r(RedirectInput.ri_lacks(h, 63), RedirectInput.ri_lacks(h, 35), nh0)))
  +lkFq = LT.rt.lacks_app(c, String.append("&state=", s), '?', LC.rq.lacks(c, 5n, hc), LC.rq.lacks(s, 5n, hs))
  +lkV = LT.rt.lacks_app(B, SCon{':', SCon{'/', SCon{'/', R}}}, '?', lkBq, LT.rt.lacks_app(H, Q, '?', lkHq, lkFq))
  +E = Equal.trans(List<&2, Ri.Param>, Ri.params(F), Ri.Param{Ri.decode("code"), c} <> Ri.params(String.append("state", SCon{'=', s})), ps, LQ.qa.kv("code", c, String.append("state", SCon{'=', s}), {==}, hc, LC.rq.lacks(c, 2n, hc)), Equal.cong(List<&2, Ri.Param>, List<&2, Ri.Param>, z => Ri.Param{Ri.decode("code"), c} <> z, Ri.params(String.append("state", SCon{'=', s})), [Ri.Param{Ri.decode("state"), s}], LQ.qa.kv1("state", s, {==}, hs, LC.rq.lacks(s, 2n, hs))))
  %Equal.sym(String, Ri.clean(T), V, EV) : {Ri.parse.at(Ri.split(_, '?'), _) == Ri.Pasted{c, Some{s}} : Ri.Answer}
  %Equal.sym(Maybe<&2, Ri.Cut>, Ri.split(V, '?'), None{}, LP.rp.split_none(V, '?', lkV)) : {Ri.parse.at(_, V) == Ri.Pasted{c, Some{s}} : Ri.Answer}
  %Equal.sym(Maybe<&2, String>, Ri.scheme(V), Some{R}, LP.rp.scheme_hit(B, R, lkBc)) : {Ri.parse.scheme(_, V) == Ri.Pasted{c, Some{s}} : Ri.Answer}
  %Equal.sym(Maybe<&2, Ri.Cut>, Ri.split(R, '#'), Some{Ri.Cut{H, F}}, LP.rp.split_hit(H, '#', F, {==}, lkHh)) : {Ri.from_params([Ri.fragment(_)]) == Ri.Pasted{c, Some{s}} : Ri.Answer}
  Equal.trans(Ri.Answer, Ri.from_params([F]), LQ.qa.ans(ps), Ri.Pasted{c, Some{s}}, LQ.qa.one(F, ps, E), ri_fr.fin(c, s, hc, hs))
