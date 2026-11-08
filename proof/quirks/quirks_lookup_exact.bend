# eukhe: the proof of LAW quirks_lookup_exact
# The model folds the rules that apply into the best so far (a strictly
# higher precedence replaces it). For any best so far b, the answer of the
# rest is the spec's first rule of each precedence above b's, else b
# (pq.res); by induction on the rules, each step a finite case split on
# the rule's layer and b's precedence (pq.top). With no best so far that
# is the spec's lookup.

import Base
import ../../bend/infer.bend as If
import ../../laws/quirks.bend as Quirks

# the answer for the best so far b, given the spec's first value at each
# precedence (2, 1, 0) of the rules still to come
def pq.res.f(b: Maybe<&2, If.Best>, f2: Maybe<&2, Nat>, f1: Maybe<&2, Nat>, f0: Maybe<&2, Nat>) -> If.Ans:
  match b:
    case None{}:
      Quirks.qs_answer(Quirks.qs_or(f2, Quirks.qs_or(f1, f0)))
    case Some{x}:
      match x:
        case If.Best{k, w}:
          match k:
            case 0n:
              Quirks.qs_answer(Quirks.qs_or(f2, Quirks.qs_or(f1, Some{w})))
            case 1n:
              Quirks.qs_answer(Quirks.qs_or(f2, Some{w}))
            case 2n+p:
              If.Known{w}

def pq.res(b: Maybe<&2, If.Best>, +rs: List<&2, If.Rule>, +q: If.Query, +d: Nat) -> If.Ans:
  pq.res.f(b, Quirks.qs_first(rs, q, d, 2n), Quirks.qs_first(rs, q, d, 1n), Quirks.qs_first(rs, q, d, 0n))

def pq.nil(b: Maybe<&2, If.Best>, -q: If.Query, -d: Nat) -> {If.ans(b) == pq.res(b, Nil{}, q, d) : If.Ans}:
  match b:
    case None{}:
      {==}
    case Some{x}:
      match x:
        case If.Best{k, w}:
          match k:
            case 0n:
              {==}
            case 1n:
              {==}
            case 2n+p:
              {==}

# a rule that applies, kept over (or under) the best so far, as the spec
# reads it among the first values of the rules after it
def pq.top(r: If.Rule, b: Maybe<&2, If.Best>, f2: Maybe<&2, Nat>, f1: Maybe<&2, Nat>, f0: Maybe<&2, Nat>)
  -> {pq.res.f(If.better(b, r), f2, f1, f0) == pq.res.f(b, Quirks.qs_first.is(Nat.is_eq(Quirks.qs_rule_rank(r), 2n), Quirks.qs_val(r), f2), Quirks.qs_first.is(Nat.is_eq(Quirks.qs_rule_rank(r), 1n), Quirks.qs_val(r), f1), Quirks.qs_first.is(Nat.is_eq(Quirks.qs_rule_rank(r), 0n), Quirks.qs_val(r), f0)) : If.Ans}:
  match r:
    case If.Rule{l, t, dd, v}:
      match l b:
        case If.Fam{} None{}:
          {==}
        case If.Fam{} Some{If.Best{0n, w}}:
          {==}
        case If.Fam{} Some{If.Best{1n, w}}:
          {==}
        case If.Fam{} Some{If.Best{2n, w}}:
          {==}
        case If.Fam{} Some{If.Best{3n+p, w}}:
          {==}
        case If.Mod{} None{}:
          {==}
        case If.Mod{} Some{If.Best{0n, w}}:
          {==}
        case If.Mod{} Some{If.Best{1n, w}}:
          {==}
        case If.Mod{} Some{If.Best{2n, w}}:
          {==}
        case If.Mod{} Some{If.Best{3n+p, w}}:
          {==}
        case If.Host{} None{}:
          {==}
        case If.Host{} Some{If.Best{0n, w}}:
          {==}
        case If.Host{} Some{If.Best{1n, w}}:
          {==}
        case If.Host{} Some{If.Best{2n, w}}:
          {==}
        case If.Host{} Some{If.Best{3n+p, w}}:
          {==}

# one rule r, for either test hit of it: the induction hypotheses for the
# best so far kept (ih_f) and for r folded in (ih_t)
def pq.step(hit: Bool, +r: If.Rule, +rest: List<&2, If.Rule>, +q: If.Query, +d: Nat, +b: Maybe<&2, If.Best>,
  ih_t: {If.ans(If.look.go(rest, q, d, If.better(b, r), If.use.at(rest, q, d))) == pq.res(If.better(b, r), rest, q, d) : If.Ans},
  ih_f: {If.ans(If.look.go(rest, q, d, b, If.use.at(rest, q, d))) == pq.res(b, rest, q, d) : If.Ans})
  -> {If.ans(If.look.go(r <> rest, q, d, b, hit)) == pq.res.f(b, Quirks.qs_first.at(hit, r, Quirks.qs_first(rest, q, d, 2n), 2n), Quirks.qs_first.at(hit, r, Quirks.qs_first(rest, q, d, 1n), 1n), Quirks.qs_first.at(hit, r, Quirks.qs_first(rest, q, d, 0n), 0n)) : If.Ans}:
  match hit:
    case True{}:
      Equal.trans(If.Ans, If.ans(If.look.go(rest, q, d, If.better(b, r), If.use.at(rest, q, d))), pq.res(If.better(b, r), rest, q, d), pq.res.f(b, Quirks.qs_first.is(Nat.is_eq(Quirks.qs_rule_rank(r), 2n), Quirks.qs_val(r), Quirks.qs_first(rest, q, d, 2n)), Quirks.qs_first.is(Nat.is_eq(Quirks.qs_rule_rank(r), 1n), Quirks.qs_val(r), Quirks.qs_first(rest, q, d, 1n)), Quirks.qs_first.is(Nat.is_eq(Quirks.qs_rule_rank(r), 0n), Quirks.qs_val(r), Quirks.qs_first(rest, q, d, 0n))), ih_t, pq.top(r, b, Quirks.qs_first(rest, q, d, 2n), Quirks.qs_first(rest, q, d, 1n), Quirks.qs_first(rest, q, d, 0n)))
    case False{}:
      ih_f

# the model's test of the first rule is the spec's
def pq.hit(r: If.Rule, -rest: List<&2, If.Rule>, q: If.Query, +d: Nat) -> {If.use.at(r <> rest, q, d) == Bool.and(Quirks.qs_applies(q, r), Nat.is_eq(Quirks.qs_dir(r), d)) : Bool}:
  match r q:
    case If.Rule{If.Fam{}, t, dd, v} If.Query{f, m, h}:
      {==}
    case If.Rule{If.Mod{}, t, dd, v} If.Query{f, m, h}:
      {==}
    case If.Rule{If.Host{}, t, dd, v} If.Query{f, m, h}:
      {==}

def pq.go(rs: List<&2, If.Rule>, +q: If.Query, +d: Nat, +b: Maybe<&2, If.Best>) -> {If.ans(If.look.go(rs, q, d, b, If.use.at(rs, q, d))) == pq.res(b, rs, q, d) : If.Ans}:
  match rs:
    case Nil{}:
      pq.nil(b, q, d)
    case +r <> +rest:
      %pq.hit(r, rest, q, d) : {If.ans(If.look.go(r <> rest, q, d, b, If.use.at(r <> rest, q, d))) == pq.res.f(b, Quirks.qs_first.at(_, r, Quirks.qs_first(rest, q, d, 2n), 2n), Quirks.qs_first.at(_, r, Quirks.qs_first(rest, q, d, 1n), 1n), Quirks.qs_first.at(_, r, Quirks.qs_first(rest, q, d, 0n), 0n)) : If.Ans}
      pq.step(If.use.at(r <> rest, q, d), r, rest, q, d, b, pq.go(rest, q, d, If.better(b, r)), pq.go(rest, q, d, b))

def Quirks.quirks_lookup_exact(rs, q, d):
  pq.go(rs, q, d, None{})
