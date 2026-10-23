# eukhe: the proof of LAW fit_reaches_budget

import Base
import ../../bend/optchat.bend as O
import ../../bend/spec.bend as S
import ../../laws/optchat.bend as Optchat
import ../base.bend as L
import ./base.bend as LA

# a type picked by a Maybe: a rewrite through it refutes Some == None
def pf.NoneT(m: Maybe<&2, O.Node>, A: Type) -> Type:
  match m:
    case None{}:
      A
    case Some{x}:
      Unit

def pf.some_none(-A: Type, -x: O.Node, e: {Some{x} == None{} : Maybe<&2, O.Node>}) -> A:
  %e : pf.NoneT(_, A)
  Unit{}

# not above is at most
def pf.cmp_le(c: Cmp, e: {False{} == Cmp.is_gt(c) : Bool}) -> {Cmp.is_le(c) == True{} : Bool}:
  match c:
    case LT{}:
      {==}
    case EQ{}:
      {==}
    case GT{}:
      L.pf.absurd_ft({False{} == True{} : Bool}, e)

# a merge at a pair of v drops one line
def pf.mlen.pick(h: Bool, +info: O.Info, +a: O.Node, +x: O.Node, +y: O.Node, +more: List<&2, O.Node>,
  ih: {LA.pf.Has(info, y <> more, a) == True{} : Bool} -> {List.length(&2, O.Node, y <> more) == 1n+List.length(&2, O.Node, O.merge(info, y <> more, a)) : Nat},
  e: {Bool.or(h, LA.pf.Has(info, y <> more, a)) == True{} : Bool})
  -> {2n+List.length(&2, O.Node, more) == 1n+List.length(&2, O.Node, O.merge.pick(h, x, y, more, O.merge(info, y <> more, a))) : Nat}:
  match h:
    case True{}:
      {==}
    case False{}:
      %ih(e) : {2n+List.length(&2, O.Node, more) == 1n+_ : Nat}
      {==}

def pf.mlen.here(+info: O.Info, +a: O.Node, +x: O.Node, rest: List<&2, O.Node>,
  ih: {LA.pf.Has(info, rest, a) == True{} : Bool} -> {List.length(&2, O.Node, rest) == 1n+List.length(&2, O.Node, O.merge(info, rest, a)) : Nat},
  e: {LA.pf.Has.at(info, a, x, rest, LA.pf.Has(info, rest, a)) == True{} : Bool})
  -> {1n+List.length(&2, O.Node, rest) == 1n+List.length(&2, O.Node, O.merge.here(info, a, x, rest, O.merge(info, rest, a))) : Nat}:
  match rest:
    case Nil{}:
      L.pf.absurd_ft({1n == 2n : Nat}, e)
    case +y <> +more:
      pf.mlen.pick(Bool.and(O.Node.eq(x, a), O.mergeable(info, x, y)), info, a, x, y, more, ih, e)

def pf.merge_len(v: List<&2, O.Node>, +info: O.Info, +a: O.Node) -> {LA.pf.Has(info, v, a) == True{} : Bool} -> {List.length(&2, O.Node, v) == 1n+List.length(&2, O.Node, O.merge(info, v, a)) : Nat}:
  match v:
    case Nil{}:
      e => L.pf.absurd_ft({0n == 1n : Nat}, e)
    case +x <> +rest:
      e => pf.mlen.here(info, a, x, rest, pf.merge_len(rest, info, a), e)

# Best is complete
# ----------------

def pf.bnone.or(-x: Bool, -b: Bool, e: {False{} == x : Bool}, eb: {b == False{} : Bool}) -> {Bool.or(x, b) == False{} : Bool}:
  %e : {Bool.or(_, b) == False{} : Bool}
  eb

def pf.btake_none(cur: Maybe<&2, O.Node>, +m: O.Age, +t: List<&2, Bool>, +a: O.Node, -A: Type, e: {O.best.take(m, t, a, cur) == None{} : Maybe<&2, O.Node>}) -> A:
  match cur:
    case None{}:
      pf.some_none(A, a, e)
    case Some{+c}:
      pf.some_none(A, O.best.vs(O.more_due(m, t, a, c), a, c), e)

def pf.bnone.pick(ok: Bool, +m: O.Age, +t: List<&2, Bool>, +info: O.Info, +a: O.Node, +y: O.Node, +more: List<&2, O.Node>,
  e: {ok == O.mergeable(info, a, y) : Bool}, +cur: Maybe<&2, O.Node>,
  ep: {O.best.pick(ok, m, t, a, cur) == None{} : Maybe<&2, O.Node>}, ec: {S.can_merge(info, y <> more) == False{} : Bool})
  -> ({cur == None{} : Maybe<&2, O.Node>} & {Bool.or(O.mergeable(info, a, y), S.can_merge(info, y <> more)) == False{} : Bool}):
  match ok:
    case False{}:
      (ep, pf.bnone.or(O.mergeable(info, a, y), S.can_merge(info, y <> more), e, ec))
    case True{}:
      pf.btake_none(cur, m, t, a, ({cur == None{} : Maybe<&2, O.Node>} & {Bool.or(O.mergeable(info, a, y), S.can_merge(info, y <> more)) == False{} : Bool}), ep)

def pf.bnone.pair(rest: List<&2, O.Node>, +m: O.Age, +t: List<&2, Bool>, +info: O.Info, +a: O.Node, +cur: Maybe<&2, O.Node>,
  ep: {O.best.pair(m, t, info, a, List.head(&2, O.Node, rest), cur) == None{} : Maybe<&2, O.Node>}, ec: {S.can_merge(info, rest) == False{} : Bool})
  -> ({cur == None{} : Maybe<&2, O.Node>} & {Bool.or(O.pair.ok(info, a, List.head(&2, O.Node, rest)), S.can_merge(info, rest)) == False{} : Bool}):
  match rest:
    case Nil{}:
      (ep, {==})
    case +y <> +more:
      pf.bnone.pick(O.mergeable(info, a, y), m, t, info, a, y, more, {==}, cur, ep, ec)

def pf.bnone.step(+rest: List<&2, O.Node>, +m: O.Age, +t: List<&2, Bool>, +info: O.Info, +a: O.Node, +cur: Maybe<&2, O.Node>,
  ih: ({O.best.pair(m, t, info, a, List.head(&2, O.Node, rest), cur) == None{} : Maybe<&2, O.Node>} & {S.can_merge(info, rest) == False{} : Bool}))
  -> ({cur == None{} : Maybe<&2, O.Node>} & {S.can_merge(info, a <> rest) == False{} : Bool}):
  (ep, ec) = ih
  pf.bnone.pair(rest, m, t, info, a, cur, ep, ec)

def pf.best_none(v: List<&2, O.Node>, +m: O.Age, +t: List<&2, Bool>, +info: O.Info, +cur: Maybe<&2, O.Node>, e: {O.best.go(m, t, info, v, cur) == None{} : Maybe<&2, O.Node>})
  -> ({cur == None{} : Maybe<&2, O.Node>} & {S.can_merge(info, v) == False{} : Bool}):
  match v:
    case Nil{}:
      (e, {==})
    case +a <> +rest:
      pf.bnone.step(rest, m, t, info, a, cur, pf.best_none(rest, m, t, info, O.best.pair(m, t, info, a, List.head(&2, O.Node, rest), cur), e))

# A fit reaches its budget
# ------------------------

def pf.Goal(+ph: Nat, +info: O.Info, +budget: Nat, +w: List<&2, O.Node>) -> Type:
  Or({Nat.is_le(O.view_size(ph, info, w), budget) == True{} : Bool}, {S.can_merge(info, w) == False{} : Bool})

def pf.LE(a: Nat, b: Nat) -> Type:
  match a b:
    case 0n y:
      Unit
    case 1n+x 0n:
      Empty
    case 1n+x 1n+y:
      pf.LE(x, y)

def fit.pf.le_refl(n: Nat) -> pf.LE(n, n):
  match n:
    case 0n:
      Unit{}
    case 1n+p:
      fit.pf.le_refl(p)

def pf.le_down(-x: Nat, -y: Nat, -f: Nat, e: {x == 1n+y : Nat}, le: pf.LE(x, 1n+f)) -> pf.LE(y, f):
  %e : pf.LE(_, 1n+f)
  le

def pf.none_best(-v: List<&2, O.Node>, -info: O.Info, -ph: Nat, -budget: Nat, p: ({None{} == None{} : Maybe<&2, O.Node>} & {S.can_merge(info, v) == False{} : Bool})) -> pf.Goal(ph, info, budget, v):
  (x, y) = p
  Inr{y}

def pf.none_goal(over: Bool, +m: O.Age, +t: List<&2, Bool>, +budget: Nat, +ph: Nat, +info: O.Info, +v: List<&2, O.Node>,
  eo: {over == Nat.is_gt(O.view_size(ph, info, v), budget) : Bool}, en: {O.choose.if(over, m, t, info, v) == None{} : Maybe<&2, O.Node>})
  -> pf.Goal(ph, info, budget, v):
  match over:
    case False{}:
      Inl{pf.cmp_le(Nat.cmp(O.view_size(ph, info, v), budget), eo)}
    case True{}:
      pf.none_best(v, info, ph, budget, pf.best_none(v, m, t, info, None{}, en))

def pf.reach.zero(v: List<&2, O.Node>, +ph: Nat, +info: O.Info, +budget: Nat, le: pf.LE(List.length(&2, O.Node, v), 0n)) -> pf.Goal(ph, info, budget, v):
  match v:
    case Nil{}:
      Inr{{==}}
    case x <> r:
      match le:

def pf.reach.cand(+m: O.Age, +t: List<&2, Bool>, +budget: Nat, +ph: Nat, +info: O.Info, +v: List<&2, O.Node>, -a: O.Node,
  eq: {O.choose(m, t, budget, ph, info, v) == Some{a} : Maybe<&2, O.Node>}) -> LA.pf.Cand(info, v, Some{a}):
  %eq : LA.pf.Cand(info, v, _)
  LA.pf.choose_sound(m, t, budget, ph, info, v)

def pf.reach.le(+info: O.Info, +v: List<&2, O.Node>, +a: O.Node, -f: Nat, le: pf.LE(List.length(&2, O.Node, v), 1n+f), cm: LA.pf.Cand(info, v, Some{a}))
  -> pf.LE(List.length(&2, O.Node, O.merge(info, v, a)), f):
  (hs, bs) = cm
  pf.le_down(List.length(&2, O.Node, v), List.length(&2, O.Node, O.merge(info, v, a)), f, pf.merge_len(v, info, a)(hs), le)

def pf.fit_reach(fuel: Nat, c: Maybe<&2, O.Node>, +m: O.Age, +t: List<&2, Bool>, +budget: Nat, +ph: Nat, +info: O.Info, +v: List<&2, O.Node>,
  le: pf.LE(List.length(&2, O.Node, v), fuel), eq: {O.choose(m, t, budget, ph, info, v) == c : Maybe<&2, O.Node>})
  -> pf.Goal(ph, info, budget, Pair.snd(List<&2, O.Node>, List<&2, O.Node>, O.fit.go(fuel, c, m, t, budget, ph, info, v))):
  match fuel c:
    case 0n _:
      pf.reach.zero(v, ph, info, budget, le)
    case 1n+f None{}:
      pf.none_goal(Nat.is_gt(O.view_size(ph, info, v), budget), m, t, budget, ph, info, v, {==}, eq)
    case 1n++f Some{+a}:
      %LA.pf.snd_cons(O.Node.parent(a), O.fit.go(f, O.choose(m, t, budget, ph, info, O.merge(info, v, a)), m, t, budget, ph, info, O.merge(info, v, a))) : pf.Goal(ph, info, budget, _)
      pf.fit_reach(f, O.choose(m, t, budget, ph, info, O.merge(info, v, a)), m, t, budget, ph, info, O.merge(info, v, a), pf.reach.le(info, v, a, f, le, pf.reach.cand(m, t, budget, ph, info, v, a, eq)), {==})

def fit_reaches_budget(+m: O.Age, +t: List<&2, Bool>, +budget: Nat, +ph: Nat, +info: O.Info, +v: List<&2, O.Node>)
  -> Or({Nat.is_le(O.view_size(ph, info, O.fit.view(m, t, budget, ph, info, v)), budget) == True{} : Bool}, {S.can_merge(info, O.fit.view(m, t, budget, ph, info, v)) == False{} : Bool}):
  pf.fit_reach(List.length(&2, O.Node, v), O.choose(m, t, budget, ph, info, v), m, t, budget, ph, info, v, fit.pf.le_refl(List.length(&2, O.Node, v)), {==})

# (e) A batch

def Optchat.fit_reaches_budget(m, t, budget, ph, info, v):
  fit_reaches_budget(m, t, budget, ph, info, v)
