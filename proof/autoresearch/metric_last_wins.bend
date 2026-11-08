# eukhe: the proof of LAW metric_last_wins

import Base
import ../../bend/autoresearch/dec.bend as ArD
import ../../bend/autoresearch/line.bend as ArL
import ../../bend/autoresearch/state.bend as ArS
import ../../laws/autoresearch/model.bend as Autoresearch
import ./base/step.bend as AS

# the empty list: the new name is the only one
def lw.nil(b: Bool, d: ArD.Dec) -> {ArS.lookup.at(b, d, None{}) == Autoresearch.ar_pick(b, Some{d}, None{}) : Maybe<&2, ArD.Dec>}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# a hit replaced by its new value: n is x or not, the same either way
def lw.same(c: Bool, d: ArD.Dec, v: ArD.Dec, r: Maybe<&2, ArD.Dec>) -> {ArS.lookup.at(c, d, r) == Autoresearch.ar_pick(c, Some{d}, ArS.lookup.at(c, v, r)) : Maybe<&2, ArD.Dec>}:
  match c:
    case True{}:
      {==}
    case False{}:
      {==}

# k is x, n is x, but k is not n: impossible
def lw.eqx(+k: String, +n: String, +x: String, hk: {k == x : String}, hn: {n == x : String}) -> {String.eq(k, n) == True{} : Bool}:
  %Equal.sym(String, k, x, hk) : {String.eq(_, n) == True{} : Bool}
  %Equal.sym(String, n, x, hn) : {String.eq(x, _) == True{} : Bool}
  AS.as.str_refl(x)

def lw.clash(+k: String, +n: String, +x: String, hk: {k == x : String}, hn: {n == x : String}, eb: {String.eq(k, n) == False{} : Bool}) -> {False{} == True{} : Bool}:
  Equal.trans(Bool, False{}, String.eq(k, n), True{}, Equal.sym(Bool, String.eq(k, n), False{}, eb), lw.eqx(k, n, x, hk, hn))

def lw.swap(p: Bool, q: Bool, +k: String, +n: String, +x: String, ep: {String.eq(k, x) == p : Bool}, eq: {String.eq(n, x) == q : Bool}, eb: {String.eq(k, n) == False{} : Bool}, v: ArD.Dec, d: ArD.Dec, r: Maybe<&2, ArD.Dec>)
  -> {ArS.lookup.at(p, v, Autoresearch.ar_pick(q, Some{d}, r)) == Autoresearch.ar_pick(q, Some{d}, ArS.lookup.at(p, v, r)) : Maybe<&2, ArD.Dec>}:
  match p q:
    case True{} True{}:
      AS.as.absurd({Some{v} == Some{d} : Maybe<&2, ArD.Dec>}, lw.clash(k, n, x, AS.as.str_eq(k, x, ep), AS.as.str_eq(n, x, eq), eb))
    case True{} False{}:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      {==}

def lw.cons(b: Bool, +k: String, +v: ArD.Dec, +t: List<&2, ArL.Kv>, +n: String, +d: ArD.Dec, +x: String, eb: {String.eq(k, n) == b : Bool}, ih: {ArS.lookup(ArS.put(t, n, d), x) == Autoresearch.ar_pick(String.eq(n, x), Some{d}, ArS.lookup(t, x)) : Maybe<&2, ArD.Dec>})
  -> {ArS.lookup(ArS.put.at(b, k, v, t, n, d, ArS.put(t, n, d)), x) == Autoresearch.ar_pick(String.eq(n, x), Some{d}, ArS.lookup.at(String.eq(k, x), v, ArS.lookup(t, x))) : Maybe<&2, ArD.Dec>}:
  match b:
    case True{}:
      %Equal.sym(String, k, n, AS.as.str_eq(k, n, eb)) : {ArS.lookup.at(String.eq(n, x), d, ArS.lookup(t, x)) == Autoresearch.ar_pick(String.eq(n, x), Some{d}, ArS.lookup.at(String.eq(_, x), v, ArS.lookup(t, x))) : Maybe<&2, ArD.Dec>}
      lw.same(String.eq(n, x), d, v, ArS.lookup(t, x))
    case False{}:
      %Equal.sym(Maybe<&2, ArD.Dec>, ArS.lookup(ArS.put(t, n, d), x), Autoresearch.ar_pick(String.eq(n, x), Some{d}, ArS.lookup(t, x)), ih) : {ArS.lookup.at(String.eq(k, x), v, _) == Autoresearch.ar_pick(String.eq(n, x), Some{d}, ArS.lookup.at(String.eq(k, x), v, ArS.lookup(t, x))) : Maybe<&2, ArD.Dec>}
      lw.swap(String.eq(k, x), String.eq(n, x), k, n, x, {==}, {==}, eb, v, d, ArS.lookup(t, x))

def Autoresearch.metric_last_wins(kvs, n, d, x):
  match kvs:
    case Nil{}:
      lw.nil(String.eq(n, x), d)
    case ArL.Kv{+k, +v} <> +t:
      lw.cons(String.eq(k, n), k, v, t, n, d, x, {==}, Autoresearch.metric_last_wins(t, n, d, x))
