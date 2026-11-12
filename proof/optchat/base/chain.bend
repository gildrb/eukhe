# eukhe: lemmas the proofs of area optchat share: a fit is a chain of
# merges of the most due pair (S.Chain)
#
# The scan OFit.best.go keeps the first line of the most due mergeable
# pair so far, replacing it only by a strictly more due one. ch.scan
# carries, from the end of the view back, what its answer a is: either
# the pair it already held (no pair of the rest more due than a), or a
# pair of the rest at which S.At holds (every mergeable pair before it
# strictly less due, none after it more due) and which is more due than
# the pair held before (ch.Over). The order facts it needs are
# LD.du.md_tr (a > c >= x gives a > x) and LD.du.md_same (a pair of a's
# level and index value is not more due than a's). OFit.merge then
# replaces exactly that pair (the first pair from a node equal to a whose
# parent is built: an earlier one would be as due). A fit with no answer
# stops (ch.stop); else it merges a's pair over budget and goes on from a
# view one line shorter (ch.at_len), so the length is fuel enough
# (ch.go).

import Base
import ../../../bend/optchat/bits.bend as OBits
import ../../../bend/optchat/node.bend as ONode
import ../../../bend/optchat/info.bend as OInfo
import ../../../bend/optchat/fit.bend as OFit
import ../../../bend/optchat/state.bend as OState
import ../../../bend/optchat/step.bend as OStep
import ../../../spec/memory/optchat.bend as S
import ../../base/nat.bend as LNat
import ./step.bend as LA
import ./queries.bend as LQ
import ./batch.bend as LB
import ./due.bend as LD

# Logic
# -----

def ch.get(m: Maybe<&2, ONode.Node>, d: ONode.Node) -> ONode.Node:
  match m:
    case None{}:
      d
    case Some{x}:
      x

def ch.some_inj(+a: ONode.Node, +b: ONode.Node, h: {Some{a} == Some{b} : Maybe<&2, ONode.Node>}) -> {a == b : ONode.Node}:
  Equal.cong(Maybe<&2, ONode.Node>, ONode.Node, q => ch.get(q, a), Some{a}, Some{b}, h)

def ch.isn(m: Maybe<&2, ONode.Node>) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{x}:
      False{}

def ch.none_some(-G: Type, -a: ONode.Node, h: {None{} == Some{a} : Maybe<&2, ONode.Node>}) -> G:
  LA.cover.absurd(G, Equal.cong(Maybe<&2, ONode.Node>, Bool, q => ch.isn(q), Some{a}, None{}, Equal.sym(Maybe<&2, ONode.Node>, None{}, Some{a}, h)))

def ch.some_none(-G: Type, -a: ONode.Node, h: {Some{a} == None{} : Maybe<&2, ONode.Node>}) -> G:
  LA.cover.absurd(G, Equal.cong(Maybe<&2, ONode.Node>, Bool, q => ch.isn(q), Some{a}, None{}, h))

def ch.snd(-A: Type, -B: Type, p: A & B) -> B:
  (a, b) = p
  b

def ch.and_f(a: Bool) -> {Bool.and(a, False{}) == False{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

def ch.imp_t(a: Bool) -> {OBits.Bool.implies(a, True{}) == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

# a implies b when b holds
def ch.imp_by(+a: Bool, -b: Bool, h: {b == True{} : Bool}) -> {OBits.Bool.implies(a, b) == True{} : Bool}:
  %Equal.sym(Bool, b, True{}, h) : {OBits.Bool.implies(a, _) == True{} : Bool}
  ch.imp_t(a)

def ch.same_refl(a: ONode.Node) -> {S.same(a, a) == True{} : Bool}:
  match a:
    case ONode.Node{+l, +i}:
      %Equal.sym(Bool, Nat.is_eq(l, l), True{}, LNat.child.pc.eq_refl(l)) : {Bool.and(_, Nat.is_eq(OBits.Bits.val(i), OBits.Bits.val(i))) == True{} : Bool}
      LNat.child.pc.eq_refl(OBits.Bits.val(i))

def ch.eq_refl(+a: ONode.Node) -> {ONode.Node.eq(a, a) == True{} : Bool}:
  %Equal.sym(Bool, ONode.Node.eq(a, a), S.same(a, a), LQ.oq.eq(a, a)) : {_ == True{} : Bool}
  ch.same_refl(a)

# the code's pair test, as the spec's
def ch.pair_f(+info: OInfo.Info, +x: ONode.Node, +y: ONode.Node, e: {OFit.mergeable(info, x, y) == False{} : Bool}) -> {S.mergeable(info, x, y) == False{} : Bool}:
  %LB.ob.merg(info, x, y) : {_ == False{} : Bool}
  e

def ch.pair_t(+info: OInfo.Info, +x: ONode.Node, +y: ONode.Node, e: {OFit.mergeable(info, x, y) == True{} : Bool}) -> {S.mergeable(info, x, y) == True{} : Bool}:
  %LB.ob.merg(info, x, y) : {_ == True{} : Bool}
  e

def ch.md(+m: OFit.Age, +t: List<&2, Bool>, +a: ONode.Node, +b: ONode.Node, -v: Bool, e: {OFit.more_due(m, t, a, b) == v : Bool}) -> {S.more_due(m, t, a, b) == v : Bool}:
  %LB.ob.md(a, b, m, t) : {_ == v : Bool}
  e

# a pair more due than a's does not start at a node equal to a
def ch.ne_at(b: Bool, +m: OFit.Age, +t: List<&2, Bool>, +a: ONode.Node, +x: ONode.Node, eb: {ONode.Node.eq(x, a) == b : Bool}, h: {S.more_due(m, t, a, x) == True{} : Bool}) -> {ONode.Node.eq(x, a) == False{} : Bool}:
  match b:
    case False{}:
      eb
    case True{}:
      +sx = Equal.trans(Bool, S.same(x, a), ONode.Node.eq(x, a), True{}, Equal.sym(Bool, ONode.Node.eq(x, a), S.same(x, a), LQ.oq.eq(x, a)), eb)
      LA.cover.absurd({ONode.Node.eq(x, a) == False{} : Bool}, Equal.trans(Bool, False{}, S.more_due(m, t, a, x), True{}, Equal.sym(Bool, S.more_due(m, t, a, x), False{}, LD.du.md_same(m, t, a, x, sx)), h))

def ch.ne(+m: OFit.Age, +t: List<&2, Bool>, +a: ONode.Node, +x: ONode.Node, h: {S.more_due(m, t, a, x) == True{} : Bool}) -> {ONode.Node.eq(x, a) == False{} : Bool}:
  ch.ne_at(ONode.Node.eq(x, a), m, t, a, x, {==}, h)

# Merge, at a pair
# ----------------

def ch.hit_off(+info: OInfo.Info, +a: ONode.Node, +x: ONode.Node, +y: ONode.Node, e: {OFit.mergeable(info, x, y) == False{} : Bool}) -> {Bool.and(ONode.Node.eq(x, a), OFit.mergeable(info, x, y)) == False{} : Bool}:
  %Equal.sym(Bool, OFit.mergeable(info, x, y), False{}, e) : {Bool.and(ONode.Node.eq(x, a), _) == False{} : Bool}
  ch.and_f(ONode.Node.eq(x, a))

def ch.hit_ne(+info: OInfo.Info, +a: ONode.Node, +x: ONode.Node, +y: ONode.Node, e: {ONode.Node.eq(x, a) == False{} : Bool}) -> {Bool.and(ONode.Node.eq(x, a), OFit.mergeable(info, x, y)) == False{} : Bool}:
  %Equal.sym(Bool, ONode.Node.eq(x, a), False{}, e) : {Bool.and(_, OFit.mergeable(info, x, y)) == False{} : Bool}
  {==}

def ch.hit_on(+info: OInfo.Info, +a: ONode.Node, +x: ONode.Node, +y: ONode.Node, xa: {x == a : ONode.Node}, e: {OFit.mergeable(info, x, y) == True{} : Bool}) -> {Bool.and(ONode.Node.eq(x, a), OFit.mergeable(info, x, y)) == True{} : Bool}:
  %xa : {Bool.and(ONode.Node.eq(x, _), OFit.mergeable(info, x, y)) == True{} : Bool}
  %Equal.sym(Bool, ONode.Node.eq(x, x), True{}, ch.eq_refl(x)) : {Bool.and(_, OFit.mergeable(info, x, y)) == True{} : Bool}
  e

# x is not a's pair: merge keeps x and goes on
def ch.at_keep(hit: Bool, eh: {hit == False{} : Bool}, +m: OFit.Age, +t: List<&2, Bool>, +info: OInfo.Info, +a: ONode.Node, +x: ONode.Node, +y: ONode.Node, +more: List<&2, ONode.Node>,
  imp: {OBits.Bool.implies(S.mergeable(info, x, y), S.more_due(m, t, a, x)) == True{} : Bool}, at: S.At(m, t, info, a, y <> more, OFit.merge(info, y <> more, a)))
  -> S.At(m, t, info, a, x <> y <> more, OFit.merge.pick(hit, x, y, more, OFit.merge(info, y <> more, a))):
  match hit:
    case True{}:
      LA.cover.absurd(S.At(m, t, info, a, x <> y <> more, ONode.Node.parent(x) <> more), Equal.sym(Bool, True{}, False{}, eh))
    case False{}:
      Inr{({==}, (imp, at))}

# x is a, and merges with y
def ch.at_hit(hit: Bool, eh: {hit == True{} : Bool}, +m: OFit.Age, +t: List<&2, Bool>, +info: OInfo.Info, +a: ONode.Node, +x: ONode.Node, +y: ONode.Node, +more: List<&2, ONode.Node>,
  xa: {x == a : ONode.Node}, mg: {S.mergeable(info, x, y) == True{} : Bool}, nm: S.NoneMore(m, t, info, a, y <> more))
  -> S.At(m, t, info, a, x <> y <> more, OFit.merge.pick(hit, x, y, more, OFit.merge(info, y <> more, a))):
  match hit:
    case False{}:
      LA.cover.absurd(S.At(m, t, info, a, x <> y <> more, x <> OFit.merge(info, y <> more, a)), eh)
    case True{}:
      Inl{(xa, (mg, (LB.ob.parent(x), ({==}, nm))))}

# The scan
# --------

# the pair held before is less due than a
def ch.Over(+m: OFit.Age, +t: List<&2, Bool>, cur: Maybe<&2, ONode.Node>, +a: ONode.Node) -> Type:
  match cur:
    case None{}:
      Unit
    case Some{c}:
      {S.more_due(m, t, a, c) == True{} : Bool}

# what the scan of v from the held pair cur answers when it answers a
def ch.Res(+m: OFit.Age, +t: List<&2, Bool>, +info: OInfo.Info, +cur: Maybe<&2, ONode.Node>, +a: ONode.Node, +v: List<&2, ONode.Node>) -> Type:
  Or(({cur == Some{a} : Maybe<&2, ONode.Node>} & S.NoneMore(m, t, info, a, v)), (S.At(m, t, info, a, v, OFit.merge(info, v, a)) & ch.Over(m, t, cur, a)))

# the old pair c is not a's: so c is a, or a is more due than c
def ch.ov_eq(+m: OFit.Age, +t: List<&2, Bool>, +x: ONode.Node, -a: ONode.Node, +c: ONode.Node, xa: {x == a : ONode.Node}, h: {S.more_due(m, t, x, c) == True{} : Bool}) -> {S.more_due(m, t, a, c) == True{} : Bool}:
  %xa : {S.more_due(m, t, _, c) == True{} : Bool}
  h

# x's pair may not merge: no test on it holds
def ch.imp_off(+info: OInfo.Info, +x: ONode.Node, +y: ONode.Node, -z: Bool, sf: {S.mergeable(info, x, y) == False{} : Bool}) -> {OBits.Bool.implies(S.mergeable(info, x, y), z) == True{} : Bool}:
  %Equal.sym(Bool, S.mergeable(info, x, y), False{}, sf) : {OBits.Bool.implies(_, z) == True{} : Bool}
  {==}

# x's pair is not more due than c, which is a
def ch.imp_not(+m: OFit.Age, +t: List<&2, Bool>, +info: OInfo.Info, +x: ONode.Node, +y: ONode.Node, +c: ONode.Node, -a: ONode.Node, ca: {c == a : ONode.Node}, smf: {S.more_due(m, t, x, c) == False{} : Bool}) -> {OBits.Bool.implies(S.mergeable(info, x, y), Bool.not(S.more_due(m, t, x, a))) == True{} : Bool}:
  %ca : {OBits.Bool.implies(S.mergeable(info, x, y), Bool.not(S.more_due(m, t, x, _))) == True{} : Bool}
  %Equal.sym(Bool, S.more_due(m, t, x, c), False{}, smf) : {OBits.Bool.implies(S.mergeable(info, x, y), Bool.not(_)) == True{} : Bool}
  ch.imp_t(S.mergeable(info, x, y))

# a is more due than x's pair: merge keeps x
def ch.over_x(+m: OFit.Age, +t: List<&2, Bool>, +info: OInfo.Info, +x: ONode.Node, +y: ONode.Node, +more: List<&2, ONode.Node>, +cur: Maybe<&2, ONode.Node>, +a: ONode.Node,
  +ax: {S.more_due(m, t, a, x) == True{} : Bool}, ov: {S.more_due(m, t, a, x) == True{} : Bool} -> ch.Over(m, t, cur, a), at: S.At(m, t, info, a, y <> more, OFit.merge(info, y <> more, a))) -> ch.Res(m, t, info, cur, a, x <> y <> more):
  Inr{(ch.at_keep(Bool.and(ONode.Node.eq(x, a), OFit.mergeable(info, x, y)), ch.hit_ne(info, a, x, y, ch.ne(m, t, a, x, ax)), m, t, info, a, x, y, more, ch.imp_by(S.mergeable(info, x, y), S.more_due(m, t, a, x), ax), at), ov(ax))}

# a is more due than the held c, which is at least as due as x's pair
def ch.over_c(+m: OFit.Age, +t: List<&2, Bool>, +info: OInfo.Info, +x: ONode.Node, +y: ONode.Node, +more: List<&2, ONode.Node>, +c: ONode.Node, +a: ONode.Node,
  smf: {S.more_due(m, t, x, c) == False{} : Bool}, +ac: {S.more_due(m, t, a, c) == True{} : Bool}, at: S.At(m, t, info, a, y <> more, OFit.merge(info, y <> more, a))) -> ch.Res(m, t, info, Some{c}, a, x <> y <> more):
  ch.over_x(m, t, info, x, y, more, Some{c}, a, LD.du.md_tr(m, t, a, c, x, ac, smf), h => ac, at)

# the scan took x's pair (x, y) as the most due so far
def ch.took(+m: OFit.Age, +t: List<&2, Bool>, +info: OInfo.Info, +x: ONode.Node, +y: ONode.Node, +more: List<&2, ONode.Node>, +cur: Maybe<&2, ONode.Node>, +a: ONode.Node,
  +eok: {OFit.mergeable(info, x, y) == True{} : Bool},
  ov_eq: {x == a : ONode.Node} -> ch.Over(m, t, cur, a),
  ov_gt: {S.more_due(m, t, a, x) == True{} : Bool} -> ch.Over(m, t, cur, a),
  ih: ch.Res(m, t, info, Some{x}, a, y <> more)) -> ch.Res(m, t, info, cur, a, x <> y <> more):
  match ih:
    case Inl{p}:
      (eq, nm) = p
      +xa = ch.some_inj(x, a, eq)
      Inr{(ch.at_hit(Bool.and(ONode.Node.eq(x, a), OFit.mergeable(info, x, y)), ch.hit_on(info, a, x, y, xa, eok), m, t, info, a, x, y, more, xa, ch.pair_t(info, x, y, eok), nm), ov_eq(xa))}
    case Inr{p}:
      (at, oc) = p
      ch.over_x(m, t, info, x, y, more, cur, a, oc, ov_gt, at)

# the held c is a: x's pair is not more due than a
def ch.kept_eq(+m: OFit.Age, +t: List<&2, Bool>, +info: OInfo.Info, +x: ONode.Node, +y: ONode.Node, +more: List<&2, ONode.Node>, +c: ONode.Node, +a: ONode.Node,
  smf: {S.more_due(m, t, x, c) == False{} : Bool}, +eq: {Some{c} == Some{a} : Maybe<&2, ONode.Node>}, nm: S.NoneMore(m, t, info, a, y <> more)) -> ch.Res(m, t, info, Some{c}, a, x <> y <> more):
  Inl{(eq, (ch.imp_not(m, t, info, x, y, c, a, ch.some_inj(c, a, eq), smf), nm))}

# the held pair c stays: x's pair is not more due
def ch.kept(+m: OFit.Age, +t: List<&2, Bool>, +info: OInfo.Info, +x: ONode.Node, +y: ONode.Node, +more: List<&2, ONode.Node>, +c: ONode.Node, +a: ONode.Node,
  smf: {S.more_due(m, t, x, c) == False{} : Bool},
  ih: ch.Res(m, t, info, Some{c}, a, y <> more)) -> ch.Res(m, t, info, Some{c}, a, x <> y <> more):
  match ih:
    case Inl{p}:
      (eq, nm) = p
      ch.kept_eq(m, t, info, x, y, more, c, a, smf, eq, nm)
    case Inr{p}:
      (at, oc) = p
      ch.over_c(m, t, info, x, y, more, c, a, smf, oc, at)

# x's pair against the held c
def ch.vs(mx: Bool, +m: OFit.Age, +t: List<&2, Bool>, +info: OInfo.Info, +x: ONode.Node, +y: ONode.Node, +more: List<&2, ONode.Node>, +c: ONode.Node, +a: ONode.Node,
  emx: {OFit.more_due(m, t, x, c) == mx : Bool}, eok: {OFit.mergeable(info, x, y) == True{} : Bool},
  ih: ch.Res(m, t, info, Some{OFit.best.vs(mx, x, c)}, a, y <> more)) -> ch.Res(m, t, info, Some{c}, a, x <> y <> more):
  match mx:
    case True{}:
      +sxc = ch.md(m, t, x, c, True{}, emx)
      ch.took(m, t, info, x, y, more, Some{c}, a, eok, xa => ch.ov_eq(m, t, x, a, c, xa, sxc), h => LD.du.md_tr2(m, t, a, x, c, h, sxc), ih)
    case False{}:
      ch.kept(m, t, info, x, y, more, c, a, ch.md(m, t, x, c, False{}, emx), ih)

# x's pair against the held pair, if any
def ch.take(cur: Maybe<&2, ONode.Node>, +m: OFit.Age, +t: List<&2, Bool>, +info: OInfo.Info, +x: ONode.Node, +y: ONode.Node, +more: List<&2, ONode.Node>, +a: ONode.Node,
  eok: {OFit.mergeable(info, x, y) == True{} : Bool},
  ih: ch.Res(m, t, info, OFit.best.take(m, t, x, cur), a, y <> more)) -> ch.Res(m, t, info, cur, a, x <> y <> more):
  match cur:
    case None{}:
      ch.took(m, t, info, x, y, more, None{}, a, eok, xa => Unit{}, h => Unit{}, ih)
    case Some{+c}:
      ch.vs(OFit.more_due(m, t, x, c), m, t, info, x, y, more, c, a, {==}, eok, ih)

def ch.step2(ok: Bool, +m: OFit.Age, +t: List<&2, Bool>, +info: OInfo.Info, +x: ONode.Node, +y: ONode.Node, +more: List<&2, ONode.Node>, +cur: Maybe<&2, ONode.Node>, +a: ONode.Node,
  +eok: {OFit.mergeable(info, x, y) == ok : Bool},
  ih: ch.Res(m, t, info, OFit.best.pick(ok, m, t, x, cur), a, y <> more)) -> ch.Res(m, t, info, cur, a, x <> y <> more):
  match ok:
    case False{}:
      match ih:
        case Inl{p}:
          (eq, nm) = p
          Inl{(eq, (ch.imp_off(info, x, y, Bool.not(S.more_due(m, t, x, a)), ch.pair_f(info, x, y, eok)), nm))}
        case Inr{p}:
          (at, oc) = p
          Inr{(ch.at_keep(Bool.and(ONode.Node.eq(x, a), OFit.mergeable(info, x, y)), ch.hit_off(info, a, x, y, eok), m, t, info, a, x, y, more, ch.imp_off(info, x, y, S.more_due(m, t, a, x), ch.pair_f(info, x, y, eok)), at), oc)}
    case True{}:
      ch.take(cur, m, t, info, x, y, more, a, eok, ih)

def ch.step(+m: OFit.Age, +t: List<&2, Bool>, +info: OInfo.Info, +x: ONode.Node, rest: List<&2, ONode.Node>, +cur: Maybe<&2, ONode.Node>, +a: ONode.Node,
  ih: ch.Res(m, t, info, OFit.best.pair(m, t, info, x, List.head(&2, ONode.Node, rest), cur), a, rest)) -> ch.Res(m, t, info, cur, a, x <> rest):
  match rest:
    case Nil{}:
      match ih:
        case Inl{p}:
          (eq, nm) = p
          Inl{(eq, ({==}, Unit{}))}
        case Inr{p}:
          (at, oc) = p
          match at:
    case +y <> +more:
      ch.step2(OFit.mergeable(info, x, y), m, t, info, x, y, more, cur, a, {==}, ih)

def ch.scan(+m: OFit.Age, +t: List<&2, Bool>, +info: OInfo.Info, v: List<&2, ONode.Node>, +cur: Maybe<&2, ONode.Node>, +a: ONode.Node, e: {OFit.best.go(m, t, info, v, cur) == Some{a} : Maybe<&2, ONode.Node>}) -> ch.Res(m, t, info, cur, a, v):
  match v:
    case Nil{}:
      Inl{(e, Unit{})}
    case +x <> +rest:
      ch.step(m, t, info, x, rest, cur, a, ch.scan(m, t, info, rest, OFit.best.pair(m, t, info, x, List.head(&2, ONode.Node, rest), cur), a, e))

def ch.best.of(+m: OFit.Age, +t: List<&2, Bool>, +info: OInfo.Info, +v: List<&2, ONode.Node>, +a: ONode.Node, r: ch.Res(m, t, info, None{}, a, v)) -> S.At(m, t, info, a, v, OFit.merge(info, v, a)):
  match r:
    case Inl{p}:
      (eq, nm) = p
      ch.none_some(S.At(m, t, info, a, v, OFit.merge(info, v, a)), a, eq)
    case Inr{p}:
      (at, oc) = p
      at

# the best pair's answer a: merging a's pair is a merge of the most due pair
def ch.best(+m: OFit.Age, +t: List<&2, Bool>, +info: OInfo.Info, +v: List<&2, ONode.Node>, +a: ONode.Node, e: {OFit.best(m, t, info, v) == Some{a} : Maybe<&2, ONode.Node>}) -> S.At(m, t, info, a, v, OFit.merge(info, v, a)):
  ch.best.of(m, t, info, v, a, ch.scan(m, t, info, v, None{}, a, e))

# No pair
# -------

def ch.none_pick(ok: Bool, +m: OFit.Age, +t: List<&2, Bool>, +info: OInfo.Info, +x: ONode.Node, +y: ONode.Node, +more: List<&2, ONode.Node>, cur: Maybe<&2, ONode.Node>,
  eok: {OFit.mergeable(info, x, y) == ok : Bool},
  ih: {OFit.best.pick(ok, m, t, x, cur) == None{} : Maybe<&2, ONode.Node>} & {S.mergeable_any(info, y <> more) == False{} : Bool})
  -> {cur == None{} : Maybe<&2, ONode.Node>} & {Bool.or(S.mergeable(info, x, y), S.mergeable_any(info, y <> more)) == False{} : Bool}:
  match ok:
    case False{}:
      (c0, ma) = ih
      +sf = ch.pair_f(info, x, y, eok)
      %Equal.sym(Bool, S.mergeable(info, x, y), False{}, sf) : {cur == None{} : Maybe<&2, ONode.Node>} & {Bool.or(_, S.mergeable_any(info, y <> more)) == False{} : Bool}
      (c0, ma)
    case True{}:
      match cur:
        case None{}:
          (c0, ma) = ih
          ch.some_none({None{} == None{} : Maybe<&2, ONode.Node>} & {Bool.or(S.mergeable(info, x, y), S.mergeable_any(info, y <> more)) == False{} : Bool}, x, c0)
        case Some{c}:
          (c0, ma) = ih
          ch.some_none({Some{c} == None{} : Maybe<&2, ONode.Node>} & {Bool.or(S.mergeable(info, x, y), S.mergeable_any(info, y <> more)) == False{} : Bool}, OFit.best.vs(OFit.more_due(m, t, x, c), x, c), c0)

def ch.none_step(+m: OFit.Age, +t: List<&2, Bool>, +info: OInfo.Info, +x: ONode.Node, rest: List<&2, ONode.Node>, +cur: Maybe<&2, ONode.Node>,
  ih: {OFit.best.pair(m, t, info, x, List.head(&2, ONode.Node, rest), cur) == None{} : Maybe<&2, ONode.Node>} & {S.mergeable_any(info, rest) == False{} : Bool})
  -> {cur == None{} : Maybe<&2, ONode.Node>} & {S.mergeable_any(info, x <> rest) == False{} : Bool}:
  match rest:
    case Nil{}:
      (c0, ma) = ih
      (c0, {==})
    case +y <> +more:
      ch.none_pick(OFit.mergeable(info, x, y), m, t, info, x, y, more, cur, {==}, ih)

# a scan that answers nothing found no pair that may merge
def ch.none(+m: OFit.Age, +t: List<&2, Bool>, +info: OInfo.Info, v: List<&2, ONode.Node>, +cur: Maybe<&2, ONode.Node>, e: {OFit.best.go(m, t, info, v, cur) == None{} : Maybe<&2, ONode.Node>}) -> {cur == None{} : Maybe<&2, ONode.Node>} & {S.mergeable_any(info, v) == False{} : Bool}:
  match v:
    case Nil{}:
      (e, {==})
    case +x <> +rest:
      ch.none_step(m, t, info, x, rest, cur, ch.none(m, t, info, rest, OFit.best.pair(m, t, info, x, List.head(&2, ONode.Node, rest), cur), e))

# The fit
# -------

def ch.stop_if(ov: Bool, +m: OFit.Age, +t: List<&2, Bool>, +budget: Nat, +ph: Nat, +info: OInfo.Info, +v: List<&2, ONode.Node>,
  eov: {OFit.over(ph, info, v, budget) == ov : Bool}, ec: {OFit.choose.if(ov, m, t, info, v) == None{} : Maybe<&2, ONode.Node>}) -> S.Stop(info, budget, ph, v):
  match ov:
    case False{}:
      +gf = Equal.trans(Bool, Nat.is_gt(S.vsize(ph, info, v), budget), OFit.over(ph, info, v, budget), False{}, Equal.sym(Bool, OFit.over(ph, info, v, budget), Nat.is_gt(S.vsize(ph, info, v), budget), LB.ob.over(ph, info, v, budget)), eov)
      Inl{LD.du.cgl(Nat.cmp(S.vsize(ph, info, v), budget), gf)}
    case True{}:
      Inr{ch.snd({None{} == None{} : Maybe<&2, ONode.Node>}, {S.mergeable_any(info, v) == False{} : Bool}, ch.none(m, t, info, v, None{}, ec))}

# a fit with no next merge may stop
def ch.stop(+m: OFit.Age, +t: List<&2, Bool>, +budget: Nat, +ph: Nat, +info: OInfo.Info, +v: List<&2, ONode.Node>, ec: {OFit.choose(m, t, budget, ph, info, v) == None{} : Maybe<&2, ONode.Node>}) -> S.Stop(info, budget, ph, v):
  ch.stop_if(OFit.over(ph, info, v, budget), m, t, budget, ph, info, v, {==}, ec)

def ch.stop0(+info: OInfo.Info, +budget: Nat, +ph: Nat, v: List<&2, ONode.Node>, len: {Nat.is_le(List.length(&2, ONode.Node, v), 0n) == True{} : Bool}) -> S.Stop(info, budget, ph, v):
  match v:
    case Nil{}:
      Inr{{==}}
    case x <> r:
      LA.cover.absurd(S.Stop(info, budget, ph, x <> r), len)

def ch.at_if(ov: Bool, +m: OFit.Age, +t: List<&2, Bool>, +budget: Nat, +ph: Nat, +info: OInfo.Info, +v: List<&2, ONode.Node>, +a: ONode.Node,
  eov: {OFit.over(ph, info, v, budget) == ov : Bool}, ec: {OFit.choose.if(ov, m, t, info, v) == Some{a} : Maybe<&2, ONode.Node>})
  -> {Nat.is_gt(S.vsize(ph, info, v), budget) == True{} : Bool} & S.At(m, t, info, a, v, OFit.merge(info, v, a)):
  match ov:
    case False{}:
      ch.none_some({Nat.is_gt(S.vsize(ph, info, v), budget) == True{} : Bool} & S.At(m, t, info, a, v, OFit.merge(info, v, a)), a, ec)
    case True{}:
      (Equal.trans(Bool, Nat.is_gt(S.vsize(ph, info, v), budget), OFit.over(ph, info, v, budget), True{}, Equal.sym(Bool, OFit.over(ph, info, v, budget), Nat.is_gt(S.vsize(ph, info, v), budget), LB.ob.over(ph, info, v, budget)), eov), ch.best(m, t, info, v, a, ec))

def ch.at_len.here(+m: OFit.Age, +t: List<&2, Bool>, +info: OInfo.Info, +a: ONode.Node, +x: ONode.Node, vr: List<&2, ONode.Node>, +z: ONode.Node, +wr: List<&2, ONode.Node>, h: S.At.here(m, t, info, a, x, vr, z, wr)) -> {List.length(&2, ONode.Node, x <> vr) == 1n+List.length(&2, ONode.Node, z <> wr) : Nat}:
  match vr:
    case Nil{}:
      match h:
    case +y <> +more:
      (xa, r1) = h
      (mg, r2) = r1
      (zp, r3) = r2
      (wm, nm) = r3
      %wm : {2n+List.length(&2, ONode.Node, _) == 2n+List.length(&2, ONode.Node, wr) : Nat}
      {==}

# a merge drops one line
def ch.at_len(+m: OFit.Age, +t: List<&2, Bool>, +info: OInfo.Info, +a: ONode.Node, v: List<&2, ONode.Node>, w: List<&2, ONode.Node>, at: S.At(m, t, info, a, v, w)) -> {List.length(&2, ONode.Node, v) == 1n+List.length(&2, ONode.Node, w) : Nat}:
  match v w:
    case Nil{} _:
      match at:
    case x <> vr Nil{}:
      match at:
    case +x <> +vr +z <> +wr:
      match at:
        case Inl{h}:
          ch.at_len.here(m, t, info, a, x, vr, z, wr, h)
        case Inr{p}:
          (xz, rest) = p
          (imp, at2) = rest
          Equal.cong(Nat, Nat, q => 1n+q, List.length(&2, ONode.Node, vr), 1n+List.length(&2, ONode.Node, wr), ch.at_len(m, t, info, a, vr, wr, at2))

def ch.cons(r: List<&2, ONode.Node> & List<&2, ONode.Node>, +m: OFit.Age, +t: List<&2, Bool>, +info: OInfo.Info, +budget: Nat, +ph: Nat, +v: List<&2, ONode.Node>, +a: ONode.Node, +w: List<&2, ONode.Node>,
  gt: {Nat.is_gt(S.vsize(ph, info, v), budget) == True{} : Bool}, at: S.At(m, t, info, a, v, w), ih: S.Chain(m, t, info, budget, ph, w, Pair.fst(List<&2, ONode.Node>, List<&2, ONode.Node>, r), Pair.snd(List<&2, ONode.Node>, List<&2, ONode.Node>, r)))
  -> S.Chain(m, t, info, budget, ph, v, Pair.fst(List<&2, ONode.Node>, List<&2, ONode.Node>, OFit.fit.cons(ONode.Node.parent(a), r)), Pair.snd(List<&2, ONode.Node>, List<&2, ONode.Node>, OFit.fit.cons(ONode.Node.parent(a), r))):
  (ms, out) = r
  (gt, (w, (a, ((Equal.sym(ONode.Node, ONode.Node.parent(a), S.parent(a), LB.ob.parent(a)), at), ih))))

def ch.len_of(+m: OFit.Age, +t: List<&2, Bool>, +budget: Nat, +ph: Nat, +info: OInfo.Info, +v: List<&2, ONode.Node>, +a: ONode.Node, ga: {Nat.is_gt(S.vsize(ph, info, v), budget) == True{} : Bool} & S.At(m, t, info, a, v, OFit.merge(info, v, a))) -> {List.length(&2, ONode.Node, v) == 1n+List.length(&2, ONode.Node, OFit.merge(info, v, a)) : Nat}:
  (gt, at) = ga
  ch.at_len(m, t, info, a, v, OFit.merge(info, v, a), at)

def ch.cons2(r: List<&2, ONode.Node> & List<&2, ONode.Node>, +m: OFit.Age, +t: List<&2, Bool>, +info: OInfo.Info, +budget: Nat, +ph: Nat, +v: List<&2, ONode.Node>, +a: ONode.Node, +w: List<&2, ONode.Node>,
  ga: {Nat.is_gt(S.vsize(ph, info, v), budget) == True{} : Bool} & S.At(m, t, info, a, v, w), ih: S.Chain(m, t, info, budget, ph, w, Pair.fst(List<&2, ONode.Node>, List<&2, ONode.Node>, r), Pair.snd(List<&2, ONode.Node>, List<&2, ONode.Node>, r)))
  -> S.Chain(m, t, info, budget, ph, v, Pair.fst(List<&2, ONode.Node>, List<&2, ONode.Node>, OFit.fit.cons(ONode.Node.parent(a), r)), Pair.snd(List<&2, ONode.Node>, List<&2, ONode.Node>, OFit.fit.cons(ONode.Node.parent(a), r))):
  (gt, at) = ga
  ch.cons(r, m, t, info, budget, ph, v, a, w, gt, at, ih)

def ch.len_next(+g: Nat, -v: List<&2, ONode.Node>, -w: List<&2, ONode.Node>, e: {List.length(&2, ONode.Node, v) == 1n+List.length(&2, ONode.Node, w) : Nat}, len: {Nat.is_le(List.length(&2, ONode.Node, v), 1n+g) == True{} : Bool}) -> {Nat.is_le(List.length(&2, ONode.Node, w), g) == True{} : Bool}:
  %e : {Nat.is_le(_, 1n+g) == True{} : Bool}
  len

def ch.go(f: Nat, c: Maybe<&2, ONode.Node>, +m: OFit.Age, +t: List<&2, Bool>, +budget: Nat, +ph: Nat, +info: OInfo.Info, +v: List<&2, ONode.Node>,
  +ec: {OFit.choose(m, t, budget, ph, info, v) == c : Maybe<&2, ONode.Node>}, len: {Nat.is_le(List.length(&2, ONode.Node, v), f) == True{} : Bool})
  -> S.Chain(m, t, info, budget, ph, v, Pair.fst(List<&2, ONode.Node>, List<&2, ONode.Node>, OFit.fit.go(f, c, m, t, budget, ph, info, v)), Pair.snd(List<&2, ONode.Node>, List<&2, ONode.Node>, OFit.fit.go(f, c, m, t, budget, ph, info, v))):
  match f c:
    case 0n _:
      ({==}, ch.stop0(info, budget, ph, v, len))
    case 1n+g None{}:
      ({==}, ch.stop(m, t, budget, ph, info, v, ec))
    case 1n++g Some{+a}:
      +w = OFit.merge(info, v, a)
      +ov = OFit.over(ph, info, v, budget)
      ch.cons2(OFit.fit.go(g, OFit.choose(m, t, budget, ph, info, w), m, t, budget, ph, info, w), m, t, info, budget, ph, v, a, w, ch.at_if(ov, m, t, budget, ph, info, v, a, {==}, ec), ch.go(g, OFit.choose(m, t, budget, ph, info, w), m, t, budget, ph, info, w, {==}, ch.len_next(g, v, w, ch.len_of(m, t, budget, ph, info, v, a, ch.at_if(ov, m, t, budget, ph, info, v, a, {==}, ec)), len)))

# every fit is a chain of merges of the most due pair
def ch.fit(+m: OFit.Age, +t: List<&2, Bool>, +budget: Nat, +ph: Nat, +info: OInfo.Info, +v: List<&2, ONode.Node>) -> S.Chain(m, t, info, budget, ph, v, Pair.fst(List<&2, ONode.Node>, List<&2, ONode.Node>, OFit.fit(m, t, budget, ph, info, v)), Pair.snd(List<&2, ONode.Node>, List<&2, ONode.Node>, OFit.fit(m, t, budget, ph, info, v))):
  ch.go(List.length(&2, ONode.Node, v), OFit.choose(m, t, budget, ph, info, v), m, t, budget, ph, info, v, {==}, LNat.child.pc.le_refl(List.length(&2, ONode.Node, v)))

# so the fitted view is Fitted
def ch.fitted(+m: OFit.Age, +t: List<&2, Bool>, +budget: Nat, +ph: Nat, +info: OInfo.Info, +v: List<&2, ONode.Node>) -> S.Fitted(m, t, info, budget, ph, v, OFit.fit.view(m, t, budget, ph, info, v)):
  (Pair.fst(List<&2, ONode.Node>, List<&2, ONode.Node>, OFit.fit(m, t, budget, ph, info, v)), ch.fit(m, t, budget, ph, info, v))

# The compaction sawtooth
# -----------------------

def ch.saw_if(ov: Bool, +cfg: OState.Cfg, +t: List<&2, Bool>, +info: OInfo.Info, +cv: List<&2, ONode.Node>) -> S.Saw.if(ov, cfg, t, info, cv, OStep.fitc.if(ov, cfg, t, info, cv)):
  match ov:
    case False{}:
      {==}
    case True{}:
      ch.fitted(OFit.Last{}, t, OState.Cfg.cfloor(cfg), OState.Cfg.ph(cfg), info, cv)

# the compaction view's step is its sawtooth
def ch.saw(+cfg: OState.Cfg, +t: List<&2, Bool>, +info: OInfo.Info, +cv: List<&2, ONode.Node>) -> S.Saw(cfg, t, info, cv, OStep.fitc(cfg, t, info, cv)):
  %LB.ob.over(OState.Cfg.ph(cfg), info, cv, OState.Cfg.cceil(cfg)) : S.Saw.if(_, cfg, t, info, cv, OStep.fitc(cfg, t, info, cv))
  ch.saw_if(OFit.over(OState.Cfg.ph(cfg), info, cv, OState.Cfg.cceil(cfg)), cfg, t, info, cv)
