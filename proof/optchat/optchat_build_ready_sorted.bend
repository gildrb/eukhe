# eukhe: the proof of LAW optchat_build_ready_sorted
# The order by level, then index value (S.before) is transitive (bt.trans)
# and total on nodes not named alike (bt.total). A strictly ordered list
# stays so when a node is removed (ONode.Nodes.del: a skipped node's
# successor is still after its predecessor, bt.weaken) and when a node is
# inserted by ONode.Nodes.ins (in front of the first node it comes before,
# not at all when named alike, bt.ins); a build removes n and may insert
# its parent.

import Base
import ../../bend/optchat/bits.bend as OBits
import ../../bend/optchat/node.bend as ONode
import ../../bend/optchat/info.bend as OInfo
import ../../bend/optchat/state.bend as OState
import ../../bend/optchat/step.bend as OStep
import ../../spec/memory/optchat.bend as S
import ../../laws/optchat/queries.bend as OptchatQueries
import ../base/nat.bend as LNat
import ./base/step.bend as LA
import ./base/queries.bend as LQ
import ./base/batch.bend as LB

# Bool
# ----

def bt.or_l(+x: Bool, -y: Bool, h: {x == True{} : Bool}) -> {Bool.or(x, y) == True{} : Bool}:
  %Equal.sym(Bool, x, True{}, h) : {Bool.or(_, y) == True{} : Bool}
  {==}

def bt.or_r(x: Bool, -y: Bool, h: {y == True{} : Bool}) -> {Bool.or(x, y) == True{} : Bool}:
  match x:
    case True{}:
      {==}
    case False{}:
      h

def bt.and_t(+x: Bool, +y: Bool, hx: {x == True{} : Bool}, hy: {y == True{} : Bool}) -> {Bool.and(x, y) == True{} : Bool}:
  %Equal.sym(Bool, x, True{}, hx) : {Bool.and(_, y) == True{} : Bool}
  hy

def bt.split(x: Bool, -y: Bool, h: {Bool.or(x, y) == True{} : Bool}) -> Or({x == True{} : Bool}, {y == True{} : Bool}):
  match x:
    case True{}:
      Inl{{==}}
    case False{}:
      Inr{h}

def bt.nor_l(x: Bool, -y: Bool, h: {Bool.or(x, y) == False{} : Bool}) -> {x == False{} : Bool}:
  match x:
    case True{}:
      LA.cover.absurd({True{} == False{} : Bool}, Equal.sym(Bool, True{}, False{}, h))
    case False{}:
      {==}

def bt.nor_r(x: Bool, -y: Bool, h: {Bool.or(x, y) == False{} : Bool}) -> {y == False{} : Bool}:
  match x:
    case True{}:
      LA.cover.absurd({y == False{} : Bool}, Equal.sym(Bool, True{}, False{}, h))
    case False{}:
      h

# and(True, y) is y
def bt.and_on(x: Bool, -y: Bool, -z: Bool, hx: {x == True{} : Bool}, h: {Bool.and(x, y) == z : Bool}) -> {y == z : Bool}:
  match x:
    case True{}:
      h
    case False{}:
      LA.cover.absurd({y == z : Bool}, hx)

# Nat
# ---

def bt.lt_trans(+a: Nat, +b: Nat, +c: Nat, h1: {Nat.is_lt(a, b) == True{} : Bool}, h2: {Nat.is_lt(b, c) == True{} : Bool}) -> {Nat.is_lt(a, c) == True{} : Bool}:
  LNat.pc.le_lt_trans(a, b, c, LNat.pc.lt_to_le(a, b, h1), h2)

# not a < b and not a == b: b < a
def bt.tri(a: Nat, b: Nat, h1: {Nat.is_lt(a, b) == False{} : Bool}, h2: {Nat.is_eq(a, b) == False{} : Bool}) -> {Nat.is_lt(b, a) == True{} : Bool}:
  match a b:
    case 0n 0n:
      LA.cover.absurd({False{} == True{} : Bool}, Equal.sym(Bool, True{}, False{}, h2))
    case 0n 1n+q:
      LA.cover.absurd({Nat.is_lt(1n+q, 0n) == True{} : Bool}, Equal.sym(Bool, True{}, False{}, h1))
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      bt.tri(p, q, h1, h2)

# The order
# ---------

def bt.tr1(+l1: Nat, +v1: Nat, +l2: Nat, +v2: Nat, +l3: Nat, +v3: Nat,
  o1: Or({Nat.is_lt(l1, l2) == True{} : Bool}, {Bool.and(Nat.is_eq(l1, l2), Nat.is_lt(v1, v2)) == True{} : Bool}),
  o2: Or({Nat.is_lt(l2, l3) == True{} : Bool}, {Bool.and(Nat.is_eq(l2, l3), Nat.is_lt(v2, v3)) == True{} : Bool}))
  -> {Bool.or(Nat.is_lt(l1, l3), Bool.and(Nat.is_eq(l1, l3), Nat.is_lt(v1, v3))) == True{} : Bool}:
  match o1 o2:
    case Inl{a} Inl{b}:
      bt.or_l(Nat.is_lt(l1, l3), Bool.and(Nat.is_eq(l1, l3), Nat.is_lt(v1, v3)), bt.lt_trans(l1, l2, l3, a, b))
    case Inl{a} Inr{+b}:
      +e23 = LA.cover.eq_of_is_eq(l2, l3, LA.cover.and_l(Nat.is_eq(l2, l3), Nat.is_lt(v2, v3), b))
      %e23 : {Bool.or(Nat.is_lt(l1, _), Bool.and(Nat.is_eq(l1, _), Nat.is_lt(v1, v3))) == True{} : Bool}
      bt.or_l(Nat.is_lt(l1, l2), Bool.and(Nat.is_eq(l1, l2), Nat.is_lt(v1, v3)), a)
    case Inr{+a} Inl{b}:
      +e12 = LA.cover.eq_of_is_eq(l1, l2, LA.cover.and_l(Nat.is_eq(l1, l2), Nat.is_lt(v1, v2), a))
      %Equal.sym(Nat, l1, l2, e12) : {Bool.or(Nat.is_lt(_, l3), Bool.and(Nat.is_eq(_, l3), Nat.is_lt(v1, v3))) == True{} : Bool}
      bt.or_l(Nat.is_lt(l2, l3), Bool.and(Nat.is_eq(l2, l3), Nat.is_lt(v1, v3)), b)
    case Inr{+a} Inr{+b}:
      +e12 = LA.cover.eq_of_is_eq(l1, l2, LA.cover.and_l(Nat.is_eq(l1, l2), Nat.is_lt(v1, v2), a))
      +lv = bt.lt_trans(v1, v2, v3, LA.cover.and_r(Nat.is_eq(l1, l2), Nat.is_lt(v1, v2), a), LA.cover.and_r(Nat.is_eq(l2, l3), Nat.is_lt(v2, v3), b))
      %Equal.sym(Nat, l1, l2, e12) : {Bool.or(Nat.is_lt(_, l3), Bool.and(Nat.is_eq(_, l3), Nat.is_lt(v1, v3))) == True{} : Bool}
      bt.or_r(Nat.is_lt(l2, l3), Bool.and(Nat.is_eq(l2, l3), Nat.is_lt(v1, v3)), bt.and_t(Nat.is_eq(l2, l3), Nat.is_lt(v1, v3), LA.cover.and_l(Nat.is_eq(l2, l3), Nat.is_lt(v2, v3), b), lv))

def bt.trans(a: ONode.Node, b: ONode.Node, c: ONode.Node, h1: {S.before(a, b) == True{} : Bool}, h2: {S.before(b, c) == True{} : Bool}) -> {S.before(a, c) == True{} : Bool}:
  match a b c:
    case ONode.Node{+la, ia} ONode.Node{+lb, ib} ONode.Node{+lc, ic}:
      +va = OBits.Bits.val(ia)
      +vb = OBits.Bits.val(ib)
      +vc = OBits.Bits.val(ic)
      bt.tr1(la, va, lb, vb, lc, vc, bt.split(Nat.is_lt(la, lb), Bool.and(Nat.is_eq(la, lb), Nat.is_lt(va, vb)), h1), bt.split(Nat.is_lt(lb, lc), Bool.and(Nat.is_eq(lb, lc), Nat.is_lt(vb, vc)), h2))

def bt.tot_l(q: Bool, +lx: Nat, +vx: Nat, +lh: Nat, +vh: Nat, +eq: {Nat.is_eq(lx, lh) == q : Bool},
  lt: {Nat.is_lt(lx, lh) == False{} : Bool}, lv: {Bool.and(Nat.is_eq(lx, lh), Nat.is_lt(vx, vh)) == False{} : Bool}, sm: {Bool.and(Nat.is_eq(lx, lh), Nat.is_eq(vx, vh)) == False{} : Bool})
  -> {Bool.or(Nat.is_lt(lh, lx), Bool.and(Nat.is_eq(lh, lx), Nat.is_lt(vh, vx))) == True{} : Bool}:
  match q:
    case False{}:
      bt.or_l(Nat.is_lt(lh, lx), Bool.and(Nat.is_eq(lh, lx), Nat.is_lt(vh, vx)), bt.tri(lx, lh, lt, eq))
    case True{}:
      +e = LA.cover.eq_of_is_eq(lx, lh, eq)
      +vlt = bt.and_on(Nat.is_eq(lx, lh), Nat.is_lt(vx, vh), False{}, eq, lv)
      +veq = bt.and_on(Nat.is_eq(lx, lh), Nat.is_eq(vx, vh), False{}, eq, sm)
      %Equal.sym(Nat, lx, lh, e) : {Bool.or(Nat.is_lt(lh, _), Bool.and(Nat.is_eq(lh, _), Nat.is_lt(vh, vx))) == True{} : Bool}
      bt.or_r(Nat.is_lt(lh, lh), Bool.and(Nat.is_eq(lh, lh), Nat.is_lt(vh, vx)), bt.and_t(Nat.is_eq(lh, lh), Nat.is_lt(vh, vx), LNat.child.pc.eq_refl(lh), bt.tri(vx, vh, vlt, veq)))

# two nodes not named alike, the first not before the second: the second
# is before the first
def bt.total(x: ONode.Node, h: ONode.Node, nb: {S.before(x, h) == False{} : Bool}, ns: {S.same(x, h) == False{} : Bool}) -> {S.before(h, x) == True{} : Bool}:
  match x h:
    case ONode.Node{+lx, ix} ONode.Node{+lh, ih}:
      +vx = OBits.Bits.val(ix)
      +vh = OBits.Bits.val(ih)
      +nb2 = nb
      bt.tot_l(Nat.is_eq(lx, lh), lx, vx, lh, vh, {==}, bt.nor_l(Nat.is_lt(lx, lh), Bool.and(Nat.is_eq(lx, lh), Nat.is_lt(vx, vh)), nb2), bt.nor_r(Nat.is_lt(lx, lh), Bool.and(Nat.is_eq(lx, lh), Nat.is_lt(vx, vh)), nb2), ns)

# Sorted lists
# ------------

def bt.weaken(t: List<&2, ONode.Node>, +p: ONode.Node, +h: ONode.Node, pb: {S.before(p, h) == True{} : Bool}, s: {S.Sorted.go(t, h) == True{} : Bool}) -> {S.Sorted.go(t, p) == True{} : Bool}:
  match t:
    case Nil{}:
      {==}
    case +h2 <> +t2:
      +s2 = s
      bt.and_t(S.before(p, h2), S.Sorted.go(t2, h2), bt.trans(p, h, h2, pb, LA.cover.and_l(S.before(h, h2), S.Sorted.go(t2, h2), s2)), LA.cover.and_r(S.before(h, h2), S.Sorted.go(t2, h2), s2))

def bt.tail(t: List<&2, ONode.Node>, +h: ONode.Node, s: {S.Sorted.go(t, h) == True{} : Bool}) -> {S.Sorted(t) == True{} : Bool}:
  match t:
    case Nil{}:
      {==}
    case +h2 <> +t2:
      LA.cover.and_r(S.before(h, h2), S.Sorted.go(t2, h2), s)

def bt.dk(k: Bool, +h: ONode.Node, +p: ONode.Node, +dt: List<&2, ONode.Node>, b: {S.before(p, h) == True{} : Bool}, ihh: {S.Sorted.go(dt, h) == True{} : Bool}, ihp: {S.Sorted.go(dt, p) == True{} : Bool}) -> {S.Sorted.go(ONode.Nodes.keep(k, h, dt), p) == True{} : Bool}:
  match k:
    case True{}:
      bt.and_t(S.before(p, h), S.Sorted.go(dt, h), b, ihh)
    case False{}:
      ihp

def bt.del_go(xs: List<&2, ONode.Node>, +n: ONode.Node, +p: ONode.Node, s: {S.Sorted.go(xs, p) == True{} : Bool}) -> {S.Sorted.go(ONode.Nodes.del(xs, n), p) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +h <> +t:
      +s2 = s
      +b = LA.cover.and_l(S.before(p, h), S.Sorted.go(t, h), s2)
      +r = LA.cover.and_r(S.before(p, h), S.Sorted.go(t, h), s2)
      bt.dk(Bool.not(ONode.Node.eq(h, n)), h, p, ONode.Nodes.del(t, n), b, bt.del_go(t, n, h, r), bt.del_go(t, n, p, bt.weaken(t, p, h, b, r)))

def bt.dk2(k: Bool, +h: ONode.Node, -dt: List<&2, ONode.Node>, a: {S.Sorted.go(dt, h) == True{} : Bool}, b: {S.Sorted(dt) == True{} : Bool}) -> {S.Sorted(ONode.Nodes.keep(k, h, dt)) == True{} : Bool}:
  match k:
    case True{}:
      a
    case False{}:
      b

# removing a node keeps a list sorted
def bt.del(xs: List<&2, ONode.Node>, +n: ONode.Node, s: {S.Sorted(xs) == True{} : Bool}) -> {S.Sorted(ONode.Nodes.del(xs, n)) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +h <> +t:
      +s2 = s
      bt.dk2(Bool.not(ONode.Node.eq(h, n)), h, ONode.Nodes.del(t, n), bt.del_go(t, n, h, s2), bt.del(t, n, bt.tail(t, h, s2)))

# the code's order and naming, as the spec's
def bt.lt(+x: ONode.Node, +h: ONode.Node, -b: Bool, e: {ONode.Node.lt(x, h) == b : Bool}) -> {S.before(x, h) == b : Bool}:
  %LB.ob.before(x, h) : {_ == b : Bool}
  e

def bt.eq(+x: ONode.Node, +h: ONode.Node, -b: Bool, e: {ONode.Node.eq(x, h) == b : Bool}) -> {S.same(x, h) == b : Bool}:
  %LQ.oq.eq(x, h) : {_ == b : Bool}
  e

def bt.ia(here: Bool, sm: Bool, +x: ONode.Node, +h: ONode.Node, +t: List<&2, ONode.Node>, +p: ONode.Node,
  +eh: {ONode.Node.lt(x, h) == here : Bool}, esm: {ONode.Node.eq(x, h) == sm : Bool},
  b: {S.before(p, h) == True{} : Bool}, +r: {S.Sorted.go(t, h) == True{} : Bool}, px: {S.before(p, x) == True{} : Bool},
  ih: {S.before(h, x) == True{} : Bool} -> {S.Sorted.go(ONode.Nodes.ins(t, x), h) == True{} : Bool})
  -> {S.Sorted.go(ONode.Nodes.ins.at(here, sm, x, h, t, ONode.Nodes.ins(t, x)), p) == True{} : Bool}:
  match here sm:
    case True{} _:
      bt.and_t(S.before(p, x), Bool.and(S.before(x, h), S.Sorted.go(t, h)), px, bt.and_t(S.before(x, h), S.Sorted.go(t, h), bt.lt(x, h, True{}, eh), r))
    case False{} True{}:
      bt.and_t(S.before(p, h), S.Sorted.go(t, h), b, r)
    case False{} False{}:
      bt.and_t(S.before(p, h), S.Sorted.go(ONode.Nodes.ins(t, x), h), b, ih(bt.total(x, h, bt.lt(x, h, False{}, eh), bt.eq(x, h, False{}, esm))))

def bt.ins_go(xs: List<&2, ONode.Node>, +x: ONode.Node, +p: ONode.Node, s: {S.Sorted.go(xs, p) == True{} : Bool}, px: {S.before(p, x) == True{} : Bool}) -> {S.Sorted.go(ONode.Nodes.ins(xs, x), p) == True{} : Bool}:
  match xs:
    case Nil{}:
      bt.and_t(S.before(p, x), True{}, px, {==})
    case +h <> +t:
      +s2 = s
      +r = LA.cover.and_r(S.before(p, h), S.Sorted.go(t, h), s2)
      bt.ia(ONode.Node.lt(x, h), ONode.Node.eq(x, h), x, h, t, p, {==}, {==}, LA.cover.and_l(S.before(p, h), S.Sorted.go(t, h), s2), r, px, e => bt.ins_go(t, x, h, r, e))

def bt.ia2(here: Bool, sm: Bool, +x: ONode.Node, +h: ONode.Node, +t: List<&2, ONode.Node>,
  +eh: {ONode.Node.lt(x, h) == here : Bool}, esm: {ONode.Node.eq(x, h) == sm : Bool}, +s: {S.Sorted.go(t, h) == True{} : Bool})
  -> {S.Sorted(ONode.Nodes.ins.at(here, sm, x, h, t, ONode.Nodes.ins(t, x))) == True{} : Bool}:
  match here sm:
    case True{} _:
      bt.and_t(S.before(x, h), S.Sorted.go(t, h), bt.lt(x, h, True{}, eh), s)
    case False{} True{}:
      s
    case False{} False{}:
      bt.ins_go(t, x, h, s, bt.total(x, h, bt.lt(x, h, False{}, eh), bt.eq(x, h, False{}, esm)))

# inserting a node keeps a list sorted
def bt.ins(xs: List<&2, ONode.Node>, +x: ONode.Node, s: {S.Sorted(xs) == True{} : Bool}) -> {S.Sorted(ONode.Nodes.ins(xs, x)) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +h <> +t:
      bt.ia2(ONode.Node.lt(x, h), ONode.Node.eq(x, h), x, h, t, {==}, {==}, s)

def bt.note(g: Bool, +pn: ONode.Node, +ready: List<&2, ONode.Node>, +n: ONode.Node, s: {S.Sorted(ready) == True{} : Bool}) -> {S.Sorted(OStep.ready.if(g, pn, ONode.Nodes.del(ready, n))) == True{} : Bool}:
  match g:
    case False{}:
      bt.del(ready, n, s)
    case True{}:
      bt.ins(ONode.Nodes.del(ready, n), pn, bt.del(ready, n, s))

def OptchatQueries.optchat_build_ready_sorted(cfg, s, n, size, sorted):
  match s:
    case OState.St{t, +info, view, shrink, cview, +ready, busy}:
      +info2 = OInfo.Info.set(info, n, size)
      bt.note(Bool.and(OInfo.Info.built(info2, ONode.Node.sibling(n)), Bool.not(OInfo.Info.built(info2, ONode.Node.parent(n)))), ONode.Node.parent(n), ready, n, sorted)
