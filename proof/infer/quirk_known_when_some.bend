# eukhe: the proof of LAW quirk_known_when_some

import Base
import ../../bend/infer.bend as If
import ../../laws/infer.bend as Infer
import ../base.bend as L

def pq.or_and_f(c: Bool, -y: Bool, -z: Bool, h: {Bool.or(Bool.and(c, y), z) == True{} : Bool}, nc: {c == False{} : Bool}) -> {z == True{} : Bool}:
  match c:
    case True{}:
      L.pq.absurd({z == True{} : Bool}, nc)
    case False{}:
      h

def pq.better_at_k(c: Bool, x: If.Best, +r: If.Rule) -> {If.is_known(If.ans(If.better.at(c, x, r))) == True{} : Bool}:
  match c:
    case True{}:
      {==}
    case False{}:
      match x:
        case If.Best{k, v}:
          {==}

def pq.better_k(b: Maybe<&2, If.Best>, +r: If.Rule) -> {If.is_known(If.ans(If.better(b, r))) == True{} : Bool}:
  match b:
    case None{}:
      {==}
    case Some{+x}:
      pq.better_at_k(Nat.is_lt(If.Best.rank(x), If.Rule.rank(r)), x, r)

def pq.stay_k(rs: List<&2, If.Rule>, +q: If.Query, +d: Nat, +b: Maybe<&2, If.Best>, hit: Bool, pb: {If.is_known(If.ans(b)) == True{} : Bool}) -> {If.is_known(If.ans(If.look.go(rs, q, d, b, hit))) == True{} : Bool}:
  match rs:
    case Nil{}:
      pb
    case +r <> +rest:
      match hit:
        case True{}:
          pq.stay_k(rest, q, d, If.better(b, r), If.use.at(rest, q, d), pq.better_k(b, r))
        case False{}:
          pq.stay_k(rest, q, d, b, If.use.at(rest, q, d), pb)

def pq.found_k(rs: List<&2, If.Rule>, +q: If.Query, +d: Nat, +b: Maybe<&2, If.Best>, hit: Bool, eh: {If.use.at(rs, q, d) == hit : Bool}, some: {If.any_at(rs, q, d, 0n) == True{} : Bool}) -> {If.is_known(If.ans(If.look.go(rs, q, d, b, hit))) == True{} : Bool}:
  match rs:
    case Nil{}:
      L.pq.absurdF({If.is_known(If.ans(b)) == True{} : Bool}, some)
    case +r <> +rest:
      match hit:
        case True{}:
          pq.stay_k(rest, q, d, If.better(b, r), If.use.at(rest, q, d), pq.better_k(b, r))
        case False{}:
          +z = pq.or_and_f(Bool.and(If.applies(q, r), Nat.is_eq(If.Rule.dir(r), d)), Nat.is_le(0n, If.Rule.rank(r)), If.any_at(rest, q, d, 0n), some, eh)
          pq.found_k(rest, q, d, b, If.use.at(rest, q, d), {==}, z)

def pq.quirk_known_when_some(+rs: List<&2, If.Rule>, +q: If.Query, +d: Nat, some: {If.any_at(rs, q, d, 0n) == True{} : Bool}) -> {If.is_known(If.lookup(rs, q, d)) == True{} : Bool}:
  pq.found_k(rs, q, d, None{}, If.use.at(rs, q, d), {==}, some)

def Infer.quirk_known_when_some(rs, q, d, some):
  pq.quirk_known_when_some(rs, q, d, some)
