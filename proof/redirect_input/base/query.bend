# eukhe: lemmas of the proofs of area redirect_input: the answer of
# parameters (qa.ans: the first non-empty `error`, then `code` with its
# `state`), the parameters of `name=value` pieces, and a paste of an
# address with a query (qa.addr).

import Base
import ../../../bend/redirect_input.bend as Ri
import ../../../laws/redirect_input.bend as RedirectInput
import ./text.bend as LT
import ./parse.bend as LP
import ./carry.bend as LC

# The answer of a parameter list
# ------------------------------

def qa.code(m: Maybe<&2, String>, ps: List<&2, Ri.Param>) -> Ri.Answer:
  match m:
    case None{}:
      Ri.Failed{Ri.FMissing{}}
    case Some{c}:
      Ri.Pasted{c, Ri.find("state", ps)}

def qa.err(m: Maybe<&2, String>, +ps: List<&2, Ri.Param>) -> Ri.Answer:
  match m:
    case Some{e}:
      Ri.Failed{Ri.FProvider{e, Ri.find("error_description", ps)}}
    case None{}:
      qa.code(Ri.find("code", ps), ps)

# what carriers whose names read as in ps answer
def qa.ans(+ps: List<&2, Ri.Param>) -> Ri.Answer:
  qa.err(Ri.find("error", ps), ps)

def qa.code_eq(m: Maybe<&2, String>, +cs: List<&2, String>, +ps: List<&2, Ri.Param>, gs: {Ri.get("state", cs) == Ri.find("state", ps) : Maybe<&2, String>}) -> {Ri.from_code(m, cs) == qa.code(m, ps) : Ri.Answer}:
  match m:
    case None{}:
      {==}
    case Some{c}:
      Equal.cong(Maybe<&2, String>, Ri.Answer, x => Ri.Pasted{c, x}, Ri.get("state", cs), Ri.find("state", ps), gs)

def qa.err_eq(m: Maybe<&2, String>, +cs: List<&2, String>, +ps: List<&2, Ri.Param>, gc: {Ri.get("code", cs) == Ri.find("code", ps) : Maybe<&2, String>}, gs: {Ri.get("state", cs) == Ri.find("state", ps) : Maybe<&2, String>}, gd: {Ri.get("error_description", cs) == Ri.find("error_description", ps) : Maybe<&2, String>}) -> {Ri.from_error(m, cs) == qa.err(m, ps) : Ri.Answer}:
  match m:
    case Some{e}:
      Equal.cong(Maybe<&2, String>, Ri.Answer, x => Ri.Failed{Ri.FProvider{e, x}}, Ri.get("error_description", cs), Ri.find("error_description", ps), gd)
    case None{}:
      Equal.trans(Ri.Answer, Ri.from_code(Ri.get("code", cs), cs), Ri.from_code(Ri.find("code", ps), cs), qa.code(Ri.find("code", ps), ps), Equal.cong(Maybe<&2, String>, Ri.Answer, x => Ri.from_code(x, cs), Ri.get("code", cs), Ri.find("code", ps), gc), qa.code_eq(Ri.find("code", ps), cs, ps, gs))

# carriers whose four names read as in ps answer as ps
def qa.from(+cs: List<&2, String>, +ps: List<&2, Ri.Param>, ge: {Ri.get("error", cs) == Ri.find("error", ps) : Maybe<&2, String>}, gc: {Ri.get("code", cs) == Ri.find("code", ps) : Maybe<&2, String>}, gs: {Ri.get("state", cs) == Ri.find("state", ps) : Maybe<&2, String>}, gd: {Ri.get("error_description", cs) == Ri.find("error_description", ps) : Maybe<&2, String>}) -> {Ri.from_params(cs) == qa.ans(ps) : Ri.Answer}:
  Equal.trans(Ri.Answer, Ri.from_error(Ri.get("error", cs), cs), Ri.from_error(Ri.find("error", ps), cs), qa.err(Ri.find("error", ps), ps), Equal.cong(Maybe<&2, String>, Ri.Answer, x => Ri.from_error(x, cs), Ri.get("error", cs), Ri.find("error", ps), ge), qa.err_eq(Ri.find("error", ps), cs, ps, gc, gs, gd))

# a carrier r of parameters ps, then an empty one
def qa.two(+r: String, +ps: List<&2, Ri.Param>, +e: {Ri.params(r) == ps : List<&2, Ri.Param>}) -> {Ri.from_params([r, SNil{}]) == qa.ans(ps) : Ri.Answer}:
  qa.from([r, SNil{}], ps, LP.rp.get2("error", r, ps, e), LP.rp.get2("code", r, ps, e), LP.rp.get2("state", r, ps, e), LP.rp.get2("error_description", r, ps, e))

# one carrier r of parameters ps
def qa.one(+r: String, +ps: List<&2, Ri.Param>, +e: {Ri.params(r) == ps : List<&2, Ri.Param>}) -> {Ri.from_params([r]) == qa.ans(ps) : Ri.Answer}:
  qa.from([r], ps, LP.rp.get1("error", r, ps, e), LP.rp.get1("code", r, ps, e), LP.rp.get1("state", r, ps, e), LP.rp.get1("error_description", r, ps, e))

# Pieces
# ------

# a piece k `=` v (k without `=`, v decoding to w): the parameter k, w
def qa.piece(+k: String, +v: String, w: String, +r: List<&2, Ri.Param>, hk: {LT.rt.lacks(k, '=') == True{} : Bool}, hd: {Ri.decode(v) == w : String}) -> {Ri.params.at(String.is_empty(String.append(k, SCon{'=', v})), String.append(k, SCon{'=', v}), r) == Ri.Param{Ri.decode(k), w} <> r : List<&2, Ri.Param>}:
  +X = String.append(k, SCon{'=', v})
  %Equal.sym(Bool, String.is_empty(X), False{}, LT.rt.ne_app(k, '=', v)) : {Ri.params.at(_, X, r) == Ri.Param{Ri.decode(k), w} <> r : List<&2, Ri.Param>}
  %Equal.sym(Maybe<&2, Ri.Cut>, Ri.split(X, '='), Some{Ri.Cut{k, v}}, LP.rp.split_hit(k, '=', v, {==}, hk)) : {Ri.param(_, X) <> r == Ri.Param{Ri.decode(k), w} <> r : List<&2, Ri.Param>}
  Equal.cong(String, List<&2, Ri.Param>, z => Ri.Param{Ri.decode(k), z} <> r, Ri.decode(v), w, hd)

# the parameters of x `&` y: those of x's piece, then y's
def qa.cons(+x: String, +y: String, hx: {LT.rt.lacks(x, '&') == True{} : Bool}) -> {Ri.params(String.append(x, SCon{'&', y})) == Ri.params.at(String.is_empty(x), x, Ri.params(y)) : List<&2, Ri.Param>}:
  Equal.cong(List<&2, String>, List<&2, Ri.Param>, z => Ri.params.go(z), String.split(String.append(x, SCon{'&', y}), '&'), x <> String.split(y, '&'), LP.rp.bs2(x, y, hx))

# the parameters of x without `&`: those of its piece
def qa.last(+x: String, hx: {LT.rt.lacks(x, '&') == True{} : Bool}) -> {Ri.params(x) == Ri.params.at(String.is_empty(x), x, []) : List<&2, Ri.Param>}:
  Equal.cong(List<&2, String>, List<&2, Ri.Param>, z => Ri.params.go(z), String.split(x, '&'), [x], LP.rp.bs1(x, hx))

# k `=` v `&` rest
def qa.kv(+k: String, +v: String, +rest: String, hk: {LT.rt.lacks(k, '=') == True{} : Bool}, hv: {RedirectInput.ri_value(v) == True{} : Bool}, hl: {LT.rt.lacks(String.append(k, SCon{'=', v}), '&') == True{} : Bool}) -> {Ri.params(String.append(String.append(k, SCon{'=', v}), SCon{'&', rest})) == Ri.Param{Ri.decode(k), v} <> Ri.params(rest) : List<&2, Ri.Param>}:
  +X = String.append(k, SCon{'=', v})
  Equal.trans(List<&2, Ri.Param>, Ri.params(String.append(X, SCon{'&', rest})), Ri.params.at(String.is_empty(X), X, Ri.params(rest)), Ri.Param{Ri.decode(k), v} <> Ri.params(rest), qa.cons(X, rest, hl), qa.piece(k, v, v, Ri.params(rest), hk, LC.rq.dec(v, hv)))

# k `=` v alone
def qa.kv1(+k: String, +v: String, hk: {LT.rt.lacks(k, '=') == True{} : Bool}, hv: {RedirectInput.ri_value(v) == True{} : Bool}, hl: {LT.rt.lacks(String.append(k, SCon{'=', v}), '&') == True{} : Bool}) -> {Ri.params(String.append(k, SCon{'=', v})) == [Ri.Param{Ri.decode(k), v}] : List<&2, Ri.Param>}:
  +X = String.append(k, SCon{'=', v})
  Equal.trans(List<&2, Ri.Param>, Ri.params(X), Ri.params.at(String.is_empty(X), X, []), [Ri.Param{Ri.decode(k), v}], qa.last(X, hl), qa.piece(k, v, v, [], hk, LC.rq.dec(v, hv)))

# k `=` v alone, v decoding to w
def qa.kv1d(+k: String, +v: String, +w: String, hk: {LT.rt.lacks(k, '=') == True{} : Bool}, hd: {Ri.decode(v) == w : String}, hl: {LT.rt.lacks(String.append(k, SCon{'=', v}), '&') == True{} : Bool}) -> {Ri.params(String.append(k, SCon{'=', v})) == [Ri.Param{Ri.decode(k), w}] : List<&2, Ri.Param>}:
  +X = String.append(k, SCon{'=', v})
  Equal.trans(List<&2, Ri.Param>, Ri.params(X), Ri.params.at(String.is_empty(X), X, []), [Ri.Param{Ri.decode(k), w}], qa.last(X, hl), qa.piece(k, v, w, [], hk, hd))

# Address and query
# -----------------

# an address b without `?`, then `?` and a calm query q without `#` whose
# trailing slashes dropped are r, of parameters ps: the answer of ps
def qa.addr(+b: String, +q: String, +r: String, +ps: List<&2, Ri.Param>, nq: {RedirectInput.ri_lacks(b, 63) == True{} : Bool}, hc: {LT.rt.calm(q) == True{} : Bool}, nh: {LT.rt.lacks(q, '#') == True{} : Bool}, us: {Ri.unslash(q) == r : String}, e: {Ri.params(r) == ps : List<&2, Ri.Param>}) -> {Ri.parse(String.append(b, SCon{'?', q})) == qa.ans(ps) : Ri.Answer}:
  Equal.trans(Ri.Answer, Ri.parse(String.append(b, SCon{'?', q})), Ri.from_params([Ri.unslash(q), SNil{}]), qa.ans(ps), LC.rq.query(b, q, nq, hc, nh), Equal.trans(Ri.Answer, Ri.from_params([Ri.unslash(q), SNil{}]), Ri.from_params([r, SNil{}]), qa.ans(ps), Equal.cong(String, Ri.Answer, z => Ri.from_params([z, SNil{}]), Ri.unslash(q), r, us), qa.two(r, ps, e)))

# a query that ends with a value keeps its end
def qa.keep(+q: String, h: {LP.rp.nofs(String.reverse(q)) == True{} : Bool}) -> {Ri.unslash(q) == q : String}:
  LP.rp.unslash0(q, h)

# a calm text cleans to itself
def qa.clean(+x: Char, +t: String, h: {LT.rt.calm(SCon{x, t}) == True{} : Bool}) -> {Ri.clean(SCon{x, t}) == SCon{x, t} : String}:
  LT.rt.clean_tail(SNil{}, x, t, h)

# a value holds no `code=`, `state=` or `error=` pair
def qa.nocarry(+c: String, +h: {RedirectInput.ri_value(c) == True{} : Bool}) -> {Ri.carries(c) == False{} : Bool}:
  %Equal.sym(List<&2, String>, String.split(c, '&'), [c], LP.rp.bs1(c, LC.rq.lacks(c, 2n, h))) : {Ri.carries.go(_) == False{} : Bool}
  %Equal.sym(Maybe<&2, Ri.Cut>, Ri.split(c, '='), None{}, LP.rp.split_none(c, '=', LC.rq.lacks(c, 3n, h))) : {Bool.or(Ri.key(_), Ri.carries.go([])) == False{} : Bool}
  {==}
