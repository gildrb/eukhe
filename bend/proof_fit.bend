# proof_fit: the laws of a fit, of the summaries along a history, and of
# a compaction's view (LAWS.bend (e), (g)). A fit's merge is sound: best
# picks the first line of a mergeable pair (Has), so each merge drops a
# line and records a built parent; and complete: best finds none only
# when no pair can merge. Summarized survives every step: Info.set only
# adds built nodes, a merge inserts a built parent, a message a leaf.

import Base
import ./optchat.bend as O
import ./spec.bend as S

# Logic
# -----

# a type picked by a Bool: a rewrite through it refutes True == False
def pf.BD(b: Bool, t: Type, f: Type) -> Type:
  match b:
    case True{}:
      t
    case False{}:
      f

def pf.absurd_tf(-A: Type, e: {True{} == False{} : Bool}) -> A:
  %e : pf.BD(_, Unit, A)
  Unit{}

def pf.absurd_ft(-A: Type, e: {False{} == True{} : Bool}) -> A:
  %e : pf.BD(_, A, Unit)
  Unit{}

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

def pf.IsSome(m: Maybe<&2, Nat>) -> Type:
  match m:
    case None{}:
      Empty
    case Some{x}:
      Unit

def pf.to_some(m: Maybe<&2, Nat>, e: {Maybe.is_some(&2, Nat, m) == True{} : Bool}) -> pf.IsSome(m):
  match m:
    case None{}:
      pf.absurd_ft(Empty, e)
    case Some{x}:
      Unit{}

def pf.from_some(m: Maybe<&2, Nat>, s: pf.IsSome(m)) -> {Maybe.is_some(&2, Nat, m) == True{} : Bool}:
  match m:
    case None{}:
      match s:
    case Some{x}:
      {==}

def pf.and_l(a: Bool, -b: Bool, e: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case False{}:
      pf.absurd_ft({False{} == True{} : Bool}, e)
    case True{}:
      {==}

def pf.and_r(a: Bool, -b: Bool, e: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case False{}:
      pf.absurd_ft({b == True{} : Bool}, e)
    case True{}:
      e

def pf.or_r(a: Bool, -b: Bool, e: {b == True{} : Bool}) -> {Bool.or(a, b) == True{} : Bool}:
  match a:
    case False{}:
      e
    case True{}:
      {==}

def pf.implies_true(p: Bool, -b: Bool, e: {b == True{} : Bool}) -> {O.Bool.implies(p, b) == True{} : Bool}:
  match p:
    case False{}:
      {==}
    case True{}:
      e

# not above is at most
def pf.cmp_le(c: Cmp, e: {False{} == Cmp.is_gt(c) : Bool}) -> {Cmp.is_le(c) == True{} : Bool}:
  match c:
    case LT{}:
      {==}
    case EQ{}:
      {==}
    case GT{}:
      pf.absurd_ft({False{} == True{} : Bool}, e)

# Node equality is reflexive
# --------------------------

def pf.nat_eq_refl(n: Nat) -> {True{} == Nat.is_eq(n, n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      pf.nat_eq_refl(p)

def pf.bool_cmp_refl(b: Bool) -> {EQ{} == Bool.cmp(b, b) : Cmp}:
  match b:
    case False{}:
      {==}
    case True{}:
      {==}

def pf.bits_cmp_refl(bs: List<&2, Bool>) -> {EQ{} == O.Bits.cmp(bs, bs) : Cmp}:
  match bs:
    case Nil{}:
      {==}
    case +b <> +r:
      %pf.bits_cmp_refl(r) : {EQ{} == O.Cmp.then(_, Bool.cmp(b, b)) : Cmp}
      pf.bool_cmp_refl(b)

def pf.node_eq_refl(n: O.Node) -> {True{} == O.Node.eq(n, n) : Bool}:
  match n:
    case O.Node{+l, +i}:
      %pf.nat_eq_refl(l) : {True{} == Bool.and(_, O.Bits.same(i, i)) : Bool}
      %pf.bits_cmp_refl(i) : {True{} == Cmp.is_eq(_) : Bool}
      {==}

# Has: a heads an adjacent pair of v that merge.here takes
# --------------------------------------------------------

def pf.Has.at(+info: O.Info, +a: O.Node, +x: O.Node, rest: List<&2, O.Node>, rec: Bool) -> Bool:
  match rest:
    case Nil{}:
      rec
    case +y <> more:
      Bool.or(Bool.and(O.Node.eq(x, a), O.mergeable(info, x, y)), rec)

def pf.Has(+info: O.Info, v: List<&2, O.Node>, +a: O.Node) -> Bool:
  match v:
    case Nil{}:
      False{}
    case +x <> +rest:
      pf.Has.at(info, a, x, rest, pf.Has(info, rest, a))

def pf.has_at(+info: O.Info, +a: O.Node, +x: O.Node, rest: List<&2, O.Node>, -rec: Bool, e: {rec == True{} : Bool}) -> {pf.Has.at(info, a, x, rest, rec) == True{} : Bool}:
  match rest:
    case Nil{}:
      e
    case +y <> more:
      pf.or_r(Bool.and(O.Node.eq(x, a), O.mergeable(info, x, y)), rec, e)

# v with p's lines before it, p reversed
def pf.rapp(p: List<&2, O.Node>, v: List<&2, O.Node>) -> List<&2, O.Node>:
  match p:
    case Nil{}:
      v
    case h <> t:
      pf.rapp(t, h <> v)

def pf.has_rapp(p: List<&2, O.Node>, +info: O.Info, +a: O.Node, +v: List<&2, O.Node>, e: {pf.Has(info, v, a) == True{} : Bool}) -> {pf.Has(info, pf.rapp(p, v), a) == True{} : Bool}:
  match p:
    case Nil{}:
      e
    case +h <> t:
      pf.has_rapp(t, info, a, h <> v, pf.has_at(info, a, h, v, pf.Has(info, v, a), e))

# a merge at a pair of v drops one line
def pf.mlen.pick(h: Bool, +info: O.Info, +a: O.Node, +x: O.Node, +y: O.Node, +more: List<&2, O.Node>,
  ih: {pf.Has(info, y <> more, a) == True{} : Bool} -> {List.length(&2, O.Node, y <> more) == 1n+List.length(&2, O.Node, O.merge(info, y <> more, a)) : Nat},
  e: {Bool.or(h, pf.Has(info, y <> more, a)) == True{} : Bool})
  -> {2n+List.length(&2, O.Node, more) == 1n+List.length(&2, O.Node, O.merge.pick(h, x, y, more, O.merge(info, y <> more, a))) : Nat}:
  match h:
    case True{}:
      {==}
    case False{}:
      %ih(e) : {2n+List.length(&2, O.Node, more) == 1n+_ : Nat}
      {==}

def pf.mlen.here(+info: O.Info, +a: O.Node, +x: O.Node, rest: List<&2, O.Node>,
  ih: {pf.Has(info, rest, a) == True{} : Bool} -> {List.length(&2, O.Node, rest) == 1n+List.length(&2, O.Node, O.merge(info, rest, a)) : Nat},
  e: {pf.Has.at(info, a, x, rest, pf.Has(info, rest, a)) == True{} : Bool})
  -> {1n+List.length(&2, O.Node, rest) == 1n+List.length(&2, O.Node, O.merge.here(info, a, x, rest, O.merge(info, rest, a))) : Nat}:
  match rest:
    case Nil{}:
      pf.absurd_ft({1n == 2n : Nat}, e)
    case +y <> +more:
      pf.mlen.pick(Bool.and(O.Node.eq(x, a), O.mergeable(info, x, y)), info, a, x, y, more, ih, e)

def pf.merge_len(v: List<&2, O.Node>, +info: O.Info, +a: O.Node) -> {pf.Has(info, v, a) == True{} : Bool} -> {List.length(&2, O.Node, v) == 1n+List.length(&2, O.Node, O.merge(info, v, a)) : Nat}:
  match v:
    case Nil{}:
      e => pf.absurd_ft({0n == 1n : Nat}, e)
    case +x <> +rest:
      e => pf.mlen.here(info, a, x, rest, pf.merge_len(rest, info, a), e)

# Best is sound
# -------------
# Cand(info, v, r): the candidate r, if any, heads a pair of v that
# merges, and its parent is built

def pf.Cand(+info: O.Info, +v: List<&2, O.Node>, r: Maybe<&2, O.Node>) -> Type:
  match r:
    case None{}:
      Unit
    case Some{+a}:
      ({pf.Has(info, v, a) == True{} : Bool} & {O.Info.built(info, O.Node.parent(a)) == True{} : Bool})

def pf.merge_built(+info: O.Info, +a: O.Node, +y: O.Node, e: {O.mergeable(info, a, y) == True{} : Bool}) -> {O.Info.built(info, O.Node.parent(a)) == True{} : Bool}:
  pf.and_r(O.Node.sib(a, y), O.Info.built(info, O.Node.parent(a)), e)

def pf.here_has(+info: O.Info, +a: O.Node, +y: O.Node, +more: List<&2, O.Node>, e: {True{} == O.mergeable(info, a, y) : Bool}) -> {pf.Has(info, a <> y <> more, a) == True{} : Bool}:
  %pf.node_eq_refl(a) : {Bool.or(Bool.and(_, O.mergeable(info, a, y)), pf.Has(info, y <> more, a)) == True{} : Bool}
  %e : {Bool.or(Bool.and(True{}, _), pf.Has(info, y <> more, a)) == True{} : Bool}
  {==}

def pf.bvs(more: Bool, +info: O.Info, +w: List<&2, O.Node>, +a: O.Node, +c: O.Node, cw: pf.Cand(info, w, Some{c}),
  hw: {pf.Has(info, w, a) == True{} : Bool}, bw: {O.Info.built(info, O.Node.parent(a)) == True{} : Bool})
  -> pf.Cand(info, w, Some{O.best.vs(more, a, c)}):
  match more:
    case True{}:
      (hw, bw)
    case False{}:
      cw

def pf.btake(cur: Maybe<&2, O.Node>, +m: O.Age, +t: List<&2, Bool>, +info: O.Info, +w: List<&2, O.Node>, +a: O.Node, cw: pf.Cand(info, w, cur),
  hw: {pf.Has(info, w, a) == True{} : Bool}, bw: {O.Info.built(info, O.Node.parent(a)) == True{} : Bool})
  -> pf.Cand(info, w, O.best.take(m, t, a, cur)):
  match cur:
    case None{}:
      (hw, bw)
    case Some{+c}:
      pf.bvs(O.more_due(m, t, a, c), info, w, a, c, cw, hw, bw)

def pf.bpick(ok: Bool, +m: O.Age, +t: List<&2, Bool>, +info: O.Info, +pre: List<&2, O.Node>, +a: O.Node, +y: O.Node, +more: List<&2, O.Node>,
  +e: {ok == O.mergeable(info, a, y) : Bool}, cur: Maybe<&2, O.Node>, cw: pf.Cand(info, pf.rapp(pre, a <> y <> more), cur))
  -> pf.Cand(info, pf.rapp(pre, a <> y <> more), O.best.pick(ok, m, t, a, cur)):
  match ok:
    case False{}:
      cw
    case True{}:
      pf.btake(cur, m, t, info, pf.rapp(pre, a <> y <> more), a, cw, pf.has_rapp(pre, info, a, a <> y <> more, pf.here_has(info, a, y, more, e)), pf.merge_built(info, a, y, Equal.sym(Bool, True{}, O.mergeable(info, a, y), e)))

def pf.bpair(rest: List<&2, O.Node>, +m: O.Age, +t: List<&2, Bool>, +info: O.Info, +pre: List<&2, O.Node>, +a: O.Node, cur: Maybe<&2, O.Node>, cw: pf.Cand(info, pf.rapp(pre, a <> rest), cur))
  -> pf.Cand(info, pf.rapp(pre, a <> rest), O.best.pair(m, t, info, a, List.head(&2, O.Node, rest), cur)):
  match rest:
    case Nil{}:
      cw
    case +y <> +more:
      pf.bpick(O.mergeable(info, a, y), m, t, info, pre, a, y, more, {==}, cur, cw)

def pf.best_sound(v: List<&2, O.Node>, +m: O.Age, +t: List<&2, Bool>, +info: O.Info, +pre: List<&2, O.Node>, +cur: Maybe<&2, O.Node>, cw: pf.Cand(info, pf.rapp(pre, v), cur))
  -> pf.Cand(info, pf.rapp(pre, v), O.best.go(m, t, info, v, cur)):
  match v:
    case Nil{}:
      cw
    case +a <> +rest:
      pf.best_sound(rest, m, t, info, a <> pre, O.best.pair(m, t, info, a, List.head(&2, O.Node, rest), cur), pf.bpair(rest, m, t, info, pre, a, cur, cw))

def pf.csound.if(over: Bool, +m: O.Age, +t: List<&2, Bool>, +info: O.Info, +v: List<&2, O.Node>) -> pf.Cand(info, v, O.choose.if(over, m, t, info, v)):
  match over:
    case False{}:
      Unit{}
    case True{}:
      pf.best_sound(v, m, t, info, Nil{}, None{}, Unit{})

def pf.choose_sound(+m: O.Age, +t: List<&2, Bool>, +budget: Nat, +ph: Nat, +info: O.Info, +v: List<&2, O.Node>) -> pf.Cand(info, v, O.choose(m, t, budget, ph, info, v)):
  pf.csound.if(Nat.is_gt(O.view_size(ph, info, v), budget), m, t, info, v)

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

def pf.le_refl(n: Nat) -> pf.LE(n, n):
  match n:
    case 0n:
      Unit{}
    case 1n+p:
      pf.le_refl(p)

def pf.le_down(-x: Nat, -y: Nat, -f: Nat, e: {x == 1n+y : Nat}, le: pf.LE(x, 1n+f)) -> pf.LE(y, f):
  %e : pf.LE(_, 1n+f)
  le

def pf.snd_cons(-n: O.Node, r: List<&2, O.Node> & List<&2, O.Node>) -> {Pair.snd(List<&2, O.Node>, List<&2, O.Node>, r) == Pair.snd(List<&2, O.Node>, List<&2, O.Node>, O.fit.cons(n, r)) : List<&2, O.Node>}:
  (ms, out) = r
  {==}

def pf.fst_cons(-n: O.Node, r: List<&2, O.Node> & List<&2, O.Node>) -> {n <> Pair.fst(List<&2, O.Node>, List<&2, O.Node>, r) == Pair.fst(List<&2, O.Node>, List<&2, O.Node>, O.fit.cons(n, r)) : List<&2, O.Node>}:
  (ms, out) = r
  {==}

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
  eq: {O.choose(m, t, budget, ph, info, v) == Some{a} : Maybe<&2, O.Node>}) -> pf.Cand(info, v, Some{a}):
  %eq : pf.Cand(info, v, _)
  pf.choose_sound(m, t, budget, ph, info, v)

def pf.reach.le(+info: O.Info, +v: List<&2, O.Node>, +a: O.Node, -f: Nat, le: pf.LE(List.length(&2, O.Node, v), 1n+f), cm: pf.Cand(info, v, Some{a}))
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
      %pf.snd_cons(O.Node.parent(a), O.fit.go(f, O.choose(m, t, budget, ph, info, O.merge(info, v, a)), m, t, budget, ph, info, O.merge(info, v, a))) : pf.Goal(ph, info, budget, _)
      pf.fit_reach(f, O.choose(m, t, budget, ph, info, O.merge(info, v, a)), m, t, budget, ph, info, O.merge(info, v, a), pf.reach.le(info, v, a, f, le, pf.reach.cand(m, t, budget, ph, info, v, a, eq)), {==})

def fit_reaches_budget(+m: O.Age, +t: List<&2, Bool>, +budget: Nat, +ph: Nat, +info: O.Info, +v: List<&2, O.Node>)
  -> Or({Nat.is_le(O.view_size(ph, info, O.fit.view(m, t, budget, ph, info, v)), budget) == True{} : Bool}, {S.can_merge(info, O.fit.view(m, t, budget, ph, info, v)) == False{} : Bool}):
  pf.fit_reach(List.length(&2, O.Node, v), O.choose(m, t, budget, ph, info, v), m, t, budget, ph, info, v, pf.le_refl(List.length(&2, O.Node, v)), {==})

# A fit merges into built parents
# -------------------------------

def pf.built_step(-info: O.Info, -v: List<&2, O.Node>, -a: O.Node, -rest: List<&2, O.Node>, cm: pf.Cand(info, v, Some{a}), br: S.Built(info, rest)) -> S.Built(info, O.Node.parent(a) <> rest):
  (hs, bs) = cm
  (bs, br)

def pf.fit_built(fuel: Nat, c: Maybe<&2, O.Node>, +m: O.Age, +t: List<&2, Bool>, +budget: Nat, +ph: Nat, +info: O.Info, +v: List<&2, O.Node>, cm: pf.Cand(info, v, c))
  -> S.Built(info, Pair.fst(List<&2, O.Node>, List<&2, O.Node>, O.fit.go(fuel, c, m, t, budget, ph, info, v))):
  match fuel c:
    case 0n _:
      Unit{}
    case 1n+f None{}:
      Unit{}
    case 1n++f Some{+a}:
      %pf.fst_cons(O.Node.parent(a), O.fit.go(f, O.choose(m, t, budget, ph, info, O.merge(info, v, a)), m, t, budget, ph, info, O.merge(info, v, a))) : S.Built(info, _)
      pf.built_step(info, v, a, Pair.fst(List<&2, O.Node>, List<&2, O.Node>, O.fit.go(f, O.choose(m, t, budget, ph, info, O.merge(info, v, a)), m, t, budget, ph, info, O.merge(info, v, a))), cm, pf.fit_built(f, O.choose(m, t, budget, ph, info, O.merge(info, v, a)), m, t, budget, ph, info, O.merge(info, v, a), pf.choose_sound(m, t, budget, ph, info, O.merge(info, v, a))))

def fit_merges_built(+m: O.Age, +t: List<&2, Bool>, +budget: Nat, +ph: Nat, +info: O.Info, +v: List<&2, O.Node>)
  -> S.Built(info, Pair.fst(List<&2, O.Node>, List<&2, O.Node>, O.fit(m, t, budget, ph, info, v))):
  pf.fit_built(List.length(&2, O.Node, v), O.choose(m, t, budget, ph, info, v), m, t, budget, ph, info, v, pf.choose_sound(m, t, budget, ph, info, v))

# Built nodes stay built
# ----------------------

def pf.trie_mono(tr: O.Trie, k: List<&2, Bool>, i: List<&2, Bool>, +sz: Nat, e: pf.IsSome(O.Trie.get(k, tr))) -> pf.IsSome(O.Trie.get(k, O.Trie.set(i, tr, sz))):
  match tr:
    case O.Tip{}:
      match k:
        case Nil{}:
          match e:
        case b <> kr:
          match b:
            case False{}:
              match e:
            case True{}:
              match e:
    case O.Bin{v, lo, hi}:
      match k i:
        case Nil{} Nil{}:
          Unit{}
        case Nil{} False{} <> ir:
          e
        case Nil{} True{} <> ir:
          e
        case False{} <> kr Nil{}:
          e
        case True{} <> kr Nil{}:
          e
        case False{} <> kr False{} <> ir:
          pf.trie_mono(lo, kr, ir, sz, e)
        case False{} <> kr True{} <> ir:
          e
        case True{} <> kr False{} <> ir:
          e
        case True{} <> kr True{} <> ir:
          pf.trie_mono(hi, kr, ir, sz, e)

def pf.lvls_mono(ts: List<&2, O.Trie>, lh: Nat, l: Nat, +k: List<&2, Bool>, +i: List<&2, Bool>, +sz: Nat, e: pf.IsSome(O.Lvls.get(lh, ts, k))) -> pf.IsSome(O.Lvls.get(lh, O.Lvls.set(l, ts, i, sz), k)):
  match ts:
    case Nil{}:
      match lh:
        case 0n:
          match e:
        case 1n+q:
          match e:
    case h <> t:
      match lh l:
        case 0n 0n:
          pf.trie_mono(h, k, i, sz, e)
        case 0n 1n+p:
          e
        case 1n+q 0n:
          e
        case 1n+q 1n+p:
          pf.lvls_mono(t, q, p, k, i, sz, e)

def pf.built_set(info: O.Info, n: O.Node, +sz: Nat, h: O.Node, e: {O.Info.built(info, h) == True{} : Bool}) -> {O.Info.built(O.Info.set(info, n, sz), h) == True{} : Bool}:
  match info:
    case O.All{a}:
      {==}
    case O.Lvls{+ts}:
      match n h:
        case O.Node{+l, +i} O.Node{+lh, +ih}:
          pf.from_some(O.Lvls.get(lh, O.Lvls.set(l, ts, i, sz), ih), pf.lvls_mono(ts, lh, l, ih, i, sz, pf.to_some(O.Lvls.get(lh, ts, ih), e)))

# Summarized survives
# -------------------

def pf.summ_h(p: Bool, +info: O.Info, +n: O.Node, +sz: Nat, +h: O.Node, e: {O.Bool.implies(p, O.Info.built(info, h)) == True{} : Bool}) -> {O.Bool.implies(p, O.Info.built(O.Info.set(info, n, sz), h)) == True{} : Bool}:
  match p:
    case False{}:
      {==}
    case True{}:
      pf.built_set(info, n, sz, h, e)

def pf.summ_set(v: List<&2, O.Node>, +info: O.Info, +n: O.Node, +sz: Nat, s: S.Summarized(info, v)) -> S.Summarized(O.Info.set(info, n, sz), v):
  match v:
    case Nil{}:
      Unit{}
    case +h <> +t:
      (eh, st) = s
      (pf.summ_h(O.Nat.is_pos(O.Node.lvl(h)), info, n, sz, h, eh), pf.summ_set(t, info, n, sz, st))

def pf.summ_app(v: List<&2, O.Node>, +info: O.Info, +t: List<&2, Bool>, s: S.Summarized(info, v)) -> S.Summarized(info, List.append(&2, O.Node, v, [O.Node.leaf(t)])):
  match v:
    case Nil{}:
      ({==}, Unit{})
    case +h <> +r:
      (eh, sr) = s
      (eh, pf.summ_app(r, info, t, sr))

def pf.summ_dup.fin(-info: O.Info, -h: O.Node, -t: List<&2, O.Node>, +eh: {O.Bool.implies(O.Nat.is_pos(O.Node.lvl(h)), O.Info.built(info, h)) == True{} : Bool}, p: (S.Summarized(info, t) & S.Summarized(info, t)))
  -> (S.Summarized(info, h <> t) & S.Summarized(info, h <> t)):
  (x, y) = p
  ((eh, x), (eh, y))

def pf.summ_dup(v: List<&2, O.Node>, +info: O.Info, s: S.Summarized(info, v)) -> (S.Summarized(info, v) & S.Summarized(info, v)):
  match v:
    case Nil{}:
      (Unit{}, Unit{})
    case +h <> +t:
      (eh, st) = s
      pf.summ_dup.fin(info, h, t, eh, pf.summ_dup(t, info, st))

def pf.msumm.pick(h: Bool, +info: O.Info, +a: O.Node, +x: O.Node, +y: O.Node, +more: List<&2, O.Node>,
  e: {h == Bool.and(O.Node.eq(x, a), O.mergeable(info, x, y)) : Bool},
  hx: {O.Bool.implies(O.Nat.is_pos(O.Node.lvl(x)), O.Info.built(info, x)) == True{} : Bool},
  sr: S.Summarized(info, y <> more), ih: S.Summarized(info, y <> more) -> S.Summarized(info, O.merge(info, y <> more, a)))
  -> S.Summarized(info, O.merge.pick(h, x, y, more, O.merge(info, y <> more, a))):
  match h:
    case True{}:
      (ey, sm) = sr
      (pf.implies_true(O.Nat.is_pos(O.Node.lvl(O.Node.parent(x))), O.Info.built(info, O.Node.parent(x)), pf.merge_built(info, x, y, pf.and_r(O.Node.eq(x, a), O.mergeable(info, x, y), Equal.sym(Bool, True{}, Bool.and(O.Node.eq(x, a), O.mergeable(info, x, y)), e)))), sm)
    case False{}:
      (hx, ih(sr))

def pf.msumm.here(+info: O.Info, +a: O.Node, +x: O.Node, rest: List<&2, O.Node>,
  hx: {O.Bool.implies(O.Nat.is_pos(O.Node.lvl(x)), O.Info.built(info, x)) == True{} : Bool},
  sr: S.Summarized(info, rest), ih: S.Summarized(info, rest) -> S.Summarized(info, O.merge(info, rest, a)))
  -> S.Summarized(info, O.merge.here(info, a, x, rest, O.merge(info, rest, a))):
  match rest:
    case Nil{}:
      (hx, Unit{})
    case +y <> +more:
      pf.msumm.pick(Bool.and(O.Node.eq(x, a), O.mergeable(info, x, y)), info, a, x, y, more, {==}, hx, sr, ih)

def pf.msumm.cons(+info: O.Info, +a: O.Node, +x: O.Node, +rest: List<&2, O.Node>, s: S.Summarized(info, x <> rest),
  ih: S.Summarized(info, rest) -> S.Summarized(info, O.merge(info, rest, a)))
  -> S.Summarized(info, O.merge(info, x <> rest, a)):
  (hx, sr) = s
  pf.msumm.here(info, a, x, rest, hx, sr, ih)

def pf.merge_summ(v: List<&2, O.Node>, +info: O.Info, +a: O.Node) -> S.Summarized(info, v) -> S.Summarized(info, O.merge(info, v, a)):
  match v:
    case Nil{}:
      s => Unit{}
    case +x <> +rest:
      s => pf.msumm.cons(info, a, x, rest, s, pf.merge_summ(rest, info, a))

def pf.fsumm.go(fuel: Nat, c: Maybe<&2, O.Node>, +m: O.Age, +t: List<&2, Bool>, +budget: Nat, +ph: Nat, +info: O.Info, +v: List<&2, O.Node>, s: S.Summarized(info, v))
  -> S.Summarized(info, Pair.snd(List<&2, O.Node>, List<&2, O.Node>, O.fit.go(fuel, c, m, t, budget, ph, info, v))):
  match fuel c:
    case 0n _:
      s
    case 1n+f None{}:
      s
    case 1n++f Some{+a}:
      %pf.snd_cons(O.Node.parent(a), O.fit.go(f, O.choose(m, t, budget, ph, info, O.merge(info, v, a)), m, t, budget, ph, info, O.merge(info, v, a))) : S.Summarized(info, _)
      pf.fsumm.go(f, O.choose(m, t, budget, ph, info, O.merge(info, v, a)), m, t, budget, ph, info, O.merge(info, v, a), pf.merge_summ(v, info, a)(s))

def pf.fit_summ(+m: O.Age, +t: List<&2, Bool>, +budget: Nat, +ph: Nat, +info: O.Info, +v: List<&2, O.Node>, s: S.Summarized(info, v))
  -> S.Summarized(info, O.fit.view(m, t, budget, ph, info, v)):
  pf.fsumm.go(List.length(&2, O.Node, v), O.choose(m, t, budget, ph, info, v), m, t, budget, ph, info, v, s)

def pf.fcsumm.if(over: Bool, +cfg: O.Cfg, +t: List<&2, Bool>, +info: O.Info, +cv: List<&2, O.Node>, s: S.Summarized(info, cv)) -> S.Summarized(info, O.fitc.if(over, cfg, t, info, cv)):
  match over:
    case False{}:
      s
    case True{}:
      pf.fit_summ(O.Last{}, t, O.Cfg.cfloor(cfg), O.Cfg.ph(cfg), info, cv, s)

def pf.fitc_summ(+cfg: O.Cfg, +t: List<&2, Bool>, +info: O.Info, +cv: List<&2, O.Node>, s: S.Summarized(info, cv)) -> S.Summarized(info, O.fitc(cfg, t, info, cv)):
  pf.fcsumm.if(Nat.is_gt(O.view_size(O.Cfg.ph(cfg), info, cv), O.Cfg.cceil(cfg)), cfg, t, info, cv, s)

# The history
# -----------

def pf.Inv(+s: O.St) -> Type:
  (S.Summarized(O.St.info(s), O.St.view(s)) & S.Summarized(O.St.info(s), O.St.cview(s)))

def pf.mcv(merged: List<&2, O.Node>, +cfg: O.Cfg, +t: List<&2, Bool>, +info: O.Info, +view: List<&2, O.Node>, +cv: List<&2, O.Node>, sv: S.Summarized(info, view), sc: S.Summarized(info, cv))
  -> S.Summarized(info, O.msg.cview(merged, cfg, t, info, view, cv)):
  match merged:
    case Nil{}:
      pf.fitc_summ(cfg, t, info, cv, sc)
    case h <> rest:
      pf.fit_summ(O.Last{}, t, O.Cfg.cfloor(cfg), O.Cfg.ph(cfg), info, view, sv)

def pf.batch.fin(+merged: List<&2, O.Node>, +view: List<&2, O.Node>, +cfg: O.Cfg, +t: List<&2, Bool>, +info: O.Info, +cv: List<&2, O.Node>, +ready: List<&2, O.Node>, +busy: List<&2, O.Node>,
  d: (S.Summarized(info, view) & S.Summarized(info, view)), sc: S.Summarized(info, cv))
  -> pf.Inv(Pair.fst(O.St, List<&2, O.Node>, O.msg.after(merged, view, cfg, t, info, cv, ready, busy))):
  (s1, s2) = d
  (s1, pf.mcv(merged, cfg, t, info, view, cv, s2, sc))

def pf.batch_inv(r: List<&2, O.Node> & List<&2, O.Node>, +cfg: O.Cfg, +t: List<&2, Bool>, +info: O.Info, +cv: List<&2, O.Node>, +ready: List<&2, O.Node>, +busy: List<&2, O.Node>)
  -> S.Summarized(info, Pair.snd(List<&2, O.Node>, List<&2, O.Node>, r)) -> S.Summarized(info, cv) -> pf.Inv(Pair.fst(O.St, List<&2, O.Node>, O.msg.batch(r, cfg, t, info, cv, ready, busy))):
  (merged, view0) = r
  +view = view0
  sv => sc => pf.batch.fin(merged, view, cfg, t, info, cv, ready, busy, pf.summ_dup(view, info, sv), sc)

def pf.msg_go_inv(grow: Bool, +cfg: O.Cfg, +t: List<&2, Bool>, +info: O.Info, +gv: List<&2, O.Node>, +gcv: List<&2, O.Node>, +ready: List<&2, O.Node>, +busy: List<&2, O.Node>,
  hv: S.Summarized(info, gv), hc: S.Summarized(info, gcv))
  -> pf.Inv(Pair.fst(O.St, List<&2, O.Node>, O.msg.go(grow, cfg, t, info, gv, gcv, ready, busy))):
  match grow:
    case False{}:
      (hv, pf.fitc_summ(cfg, t, info, gcv, hc))
    case True{}:
      pf.batch_inv(O.fit(O.Last{}, t, O.Cfg.floor(cfg), O.Cfg.ph(cfg), info, gv), cfg, t, info, gcv, ready, busy)(pf.fit_summ(O.Last{}, t, O.Cfg.floor(cfg), O.Cfg.ph(cfg), info, gv, hv))(hc)

def pf.step_msg(+cfg: O.Cfg, +t: List<&2, Bool>, +info: O.Info, +view: List<&2, O.Node>, +shrink: Bool, +cview: List<&2, O.Node>, +ready: List<&2, O.Node>, +busy: List<&2, O.Node>,
  i: pf.Inv(O.St{t, info, view, shrink, cview, ready, busy}))
  -> pf.Inv(Pair.fst(O.St, List<&2, O.Node>, O.msg(cfg, O.St{t, info, view, shrink, cview, ready, busy}))):
  (hv, hc) = i
  pf.msg_go_inv(O.St.batch(cfg, O.St{t, info, view, shrink, cview, ready, busy}), cfg, O.Bits.inc(t), info, List.append(&2, O.Node, view, [O.Node.leaf(t)]), List.append(&2, O.Node, cview, [O.Node.leaf(t)]), ready, busy, pf.summ_app(view, info, t, hv), pf.summ_app(cview, info, t, hc))

def pf.step_build(+cfg: O.Cfg, +t: List<&2, Bool>, +info: O.Info, +view: List<&2, O.Node>, +shrink: Bool, +cview: List<&2, O.Node>, +ready: List<&2, O.Node>, +busy: List<&2, O.Node>, +n: O.Node, +size: Nat,
  i: pf.Inv(O.St{t, info, view, shrink, cview, ready, busy}))
  -> pf.Inv(O.build(cfg, O.St{t, info, view, shrink, cview, ready, busy}, n, size)):
  (hv, hc) = i
  (pf.summ_set(view, info, n, size, hv), pf.fitc_summ(cfg, t, O.Info.set(info, n, size), cview, pf.summ_set(cview, info, n, size, hc)))

def pf.step_inv(+cfg: O.Cfg, s: O.St, e: O.Ev) -> pf.Inv(s) -> pf.Inv(Pair.fst(O.St, List<&2, O.Node>, O.step(cfg, s, e))):
  match s e:
    case O.St{+t, +info, +view, +shrink, +cview, +ready, +busy} O.Msg{}:
      i => pf.step_msg(cfg, t, info, view, shrink, cview, ready, busy, i)
    case O.St{+t, +info, +view, +shrink, +cview, +ready, +busy} O.Build{+n, +size}:
      i => pf.step_build(cfg, t, info, view, shrink, cview, ready, busy, n, size, i)
    case O.St{+t, +info, +view, +shrink, +cview, +ready, +busy} O.Start{n}:
      i => i
    case O.St{+t, +info, +view, +shrink, +cview, +ready, +busy} O.Free{n}:
      i => i

def pf.run_inv(evs: List<&2, O.Ev>, +cfg: O.Cfg, +s: O.St, i: pf.Inv(s)) -> pf.Inv(O.run.go(evs, cfg, s)):
  match evs:
    case Nil{}:
      i
    case +e <> rest:
      pf.run_inv(rest, cfg, Pair.fst(O.St, List<&2, O.Node>, O.step(cfg, s, e)), pf.step_inv(cfg, s, e)(i))

def pf.run_summ(+cfg: O.Cfg, +evs: List<&2, O.Ev>) -> pf.Inv(O.run(cfg, evs)):
  pf.run_inv(evs, cfg, O.St.empty(), (Unit{}, Unit{}))

def view_summarized(+cfg: O.Cfg, +evs: List<&2, O.Ev>) -> S.Summarized(O.St.info(O.run(cfg, evs)), S.view.of(cfg, evs)):
  Pair.fst(S.Summarized(O.St.info(O.run(cfg, evs)), S.view.of(cfg, evs)), S.Summarized(O.St.info(O.run(cfg, evs)), S.cview.of(cfg, evs)), pf.run_summ(cfg, evs))

def cview_summarized(+cfg: O.Cfg, +evs: List<&2, O.Ev>) -> S.Summarized(O.St.info(O.run(cfg, evs)), S.cview.of(cfg, evs)):
  Pair.snd(S.Summarized(O.St.info(O.run(cfg, evs)), S.view.of(cfg, evs)), S.Summarized(O.St.info(O.run(cfg, evs)), S.cview.of(cfg, evs)), pf.run_summ(cfg, evs))

# A compaction's view
# -------------------

def pf.ctx_pre.keep(k: Bool, +h: O.Node, -rec: List<&2, O.Node>, -rest: List<&2, O.Node>, ih: S.Prefix(rec, rest)) -> S.Prefix(O.ctx.keep(k, h, rec), h <> rest):
  match k:
    case False{}:
      Unit{}
    case True{}:
      ({==}, ih)

def pf.ctx_pre(v: List<&2, O.Node>, +info: O.Info, +bound: List<&2, Bool>) -> S.Prefix(O.ctx.go(v, info, bound), v):
  match v:
    case Nil{}:
      Unit{}
    case +h <> +rest:
      pf.ctx_pre.keep(O.ctx.ok(info, bound, h), h, O.ctx.go(rest, info, bound), rest, pf.ctx_pre(rest, info, bound))

def pf.ctx_bef.keep(k: Bool, +info: O.Info, +bound: List<&2, Bool>, +h: O.Node, -rec: List<&2, O.Node>, +e: {k == O.ctx.ok(info, bound, h) : Bool}, ih: S.Before(info, bound, rec))
  -> S.Before(info, bound, O.ctx.keep(k, h, rec)):
  match k:
    case False{}:
      Unit{}
    case True{}:
      (pf.and_l(O.Bits.le(O.Node.end_bits(h), bound), O.Info.built(info, h), Equal.sym(Bool, True{}, O.ctx.ok(info, bound, h), e)), (pf.and_r(O.Bits.le(O.Node.end_bits(h), bound), O.Info.built(info, h), Equal.sym(Bool, True{}, O.ctx.ok(info, bound, h), e)), ih))

def pf.ctx_bef(v: List<&2, O.Node>, +info: O.Info, +bound: List<&2, Bool>) -> S.Before(info, bound, O.ctx.go(v, info, bound)):
  match v:
    case Nil{}:
      Unit{}
    case +h <> +rest:
      pf.ctx_bef.keep(O.ctx.ok(info, bound, h), info, bound, h, O.ctx.go(rest, info, bound), {==}, pf.ctx_bef(rest, info, bound))

def context_ends_at_node(+s: O.St, +n: O.Node) -> S.Before(O.St.info(s), O.ctx.bound(n), O.ctx(s, n)):
  pf.ctx_bef(O.St.cview(s), O.St.info(s), O.ctx.bound(n))

def context_is_prefix(+s: O.St, +n: O.Node) -> S.Prefix(O.ctx(s, n), O.St.cview(s)):
  pf.ctx_pre(O.St.cview(s), O.St.info(s), O.ctx.bound(n))
