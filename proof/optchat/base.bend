# eukhe: lemmas the proofs of area optchat share

import Base
import ../../bend/optchat/bits.bend as OBits
import ../../bend/optchat/fit.bend as OFit
import ../../bend/optchat/info.bend as OInfo
import ../../bend/optchat/node.bend as ONode
import ../../bend/optchat/state.bend as OState
import ../../bend/optchat/step.bend as OStep
import ../../bend/spec.bend as S
import ../base/bool.bend as LBool
import ../base/logic/bool.bend as LLogicBool
import ../base/logic/logic.bend as LLogicLogic
import ../base/optchat.bend as LOptchat

# ---- cover ----

# proof_cover: the coverage laws of LAWS.bend (view_covers, cview_covers,
# message_appends, message_merges_nothing, merge_is_one_pair,
# merge_covers). A merge replaces a sibling pair by its parent, which
# covers the same messages; a fit is a chain of merges; a message appends
# the line of message T at T; so every event keeps both views tiling 0..T.

# Logic
# -----

# a type picked by a Bool: a rewrite through it refutes False == True
def cover.BD(b: Bool, t: Type, f: Type) -> Type:
  match b:
    case True{}:
      t
    case False{}:
      f

def cover.absurd(-A: Type, e: {False{} == True{} : Bool}) -> A:
  %e : cover.BD(_, A, Unit)
  Unit{}

def cover.and_l(a: Bool, -b: Bool, e: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      cover.absurd({False{} == True{} : Bool}, e)

def cover.and_r(a: Bool, -b: Bool, e: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      e
    case False{}:
      cover.absurd({b == True{} : Bool}, e)

def cover.eq_of_is_eq(a: Nat, b: Nat, e: {Nat.is_eq(a, b) == True{} : Bool}) -> {a == b : Nat}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      cover.absurd({0n == 1n+q : Nat}, e)
    case 1n+p 0n:
      cover.absurd({1n+p == 0n : Nat}, e)
    case 1n+p 1n+q:
      %cover.eq_of_is_eq(p, q, e) : {1n+p == 1n+_ : Nat}
      {==}

# Numbers
# -------

def cover.add_succ(a: Nat, -b: Nat) -> {1n+Nat.add(a, b) == Nat.add(a, 1n+b) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      %cover.add_succ(p, b) : {2n+Nat.add(p, b) == 1n+_ : Nat}
      {==}

def cover.add_one(n: Nat) -> {1n+n == Nat.add(n, 1n) : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      %cover.add_one(p) : {2n+p == 1n+_ : Nat}
      {==}

def cover.add_self(+p: Nat) -> {Nat.add(p, p) == Nat.double(p) : Nat}:
  match p:
    case 0n:
      {==}
    case 1n+q:
      %cover.add_succ(q, q) : {1n+_ == 2n+Nat.double(q) : Nat}
      %cover.add_self(q) : {2n+Nat.add(q, q) == 2n+_ : Nat}
      {==}

def cover.add_double(s: Nat, +p: Nat) -> {Nat.add(Nat.add(s, p), p) == Nat.add(s, Nat.double(p)) : Nat}:
  match s:
    case 0n:
      cover.add_self(p)
    case 1n+q:
      %cover.add_double(q, p) : {1n+Nat.add(Nat.add(q, p), p) == 1n+_ : Nat}
      {==}

# Bits
# ----

def cover.val_inc(b: List<&2, Bool>) -> {1n+OBits.Bits.val(b) == OBits.Bits.val(OBits.Bits.inc(b)) : Nat}:
  match b:
    case Nil{}:
      {==}
    case False{} <> r:
      {==}
    case True{} <> r:
      %cover.val_inc(r) : {2n+Nat.double(OBits.Bits.val(r)) == Nat.double(_) : Nat}
      {==}

# a node with low bit 0 starts where its parent does
def cover.val_up(i: List<&2, Bool>, lowf: {Bool.not(OBits.Bits.low(i)) == True{} : Bool}) -> {OBits.Bits.val(i) == Nat.double(OBits.Bits.val(OBits.Bits.up(i))) : Nat}:
  match i:
    case Nil{}:
      {==}
    case False{} <> r:
      {==}
    case True{} <> r:
      cover.absurd({OBits.Bits.val(True{} <> r) == Nat.double(OBits.Bits.val(r)) : Nat}, lowf)

# message t's line ends at t + 1
def cover.leaf_end(+t: List<&2, Bool>) -> {Nat.add(OBits.Bits.val(t), ONode.Node.count(ONode.Node.leaf(t))) == OBits.Bits.val(OBits.Bits.inc(t)) : Nat}:
  Equal.trans(Nat, Nat.add(OBits.Bits.val(t), 1n), 1n+OBits.Bits.val(t), OBits.Bits.val(OBits.Bits.inc(t)), Equal.sym(Nat, 1n+OBits.Bits.val(t), Nat.add(OBits.Bits.val(t), 1n), cover.add_one(OBits.Bits.val(t))), cover.val_inc(t))

# A merge
# -------

def cover.start_par(+la: Nat, +ia: List<&2, Bool>, -s: Nat, lowf: {Bool.not(OBits.Bits.low(ia)) == True{} : Bool}, st: {OBits.shl(la, OBits.Bits.val(ia)) == s : Nat}) -> {OBits.shl(1n+la, OBits.Bits.val(OBits.Bits.up(ia))) == s : Nat}:
  %cover.val_up(ia, lowf) : {OBits.shl(la, _) == s : Nat}
  st

def cover.sum(s: Nat, +la: Nat, -lb: Nat, leq: {la == lb : Nat}) -> {Nat.add(Nat.add(s, OBits.pow2(la)), OBits.pow2(lb)) == Nat.add(s, Nat.double(OBits.pow2(la))) : Nat}:
  %leq : {Nat.add(Nat.add(s, OBits.pow2(la)), OBits.pow2(_)) == Nat.add(s, Nat.double(OBits.pow2(la))) : Nat}
  cover.add_double(s, OBits.pow2(la))

def cover.tail(+la: Nat, -lb: Nat, +s: Nat, -more: List<&2, ONode.Node>, -e: Nat, leq: {la == lb : Nat}, tt: S.Tiles(Nat.add(Nat.add(s, OBits.pow2(la)), OBits.pow2(lb)), more, e)) -> S.Tiles(Nat.add(s, OBits.pow2(1n+la)), more, e):
  %cover.sum(s, la, lb, leq) : S.Tiles(_, more, e)
  tt

# sibling lines x, y tile like their parent
def cover.pair(+x: ONode.Node, +y: ONode.Node, +s: Nat, -more: List<&2, ONode.Node>, -e: Nat, +sib: {ONode.Node.sib(x, y) == True{} : Bool}, tiles: S.Tiles(s, x <> y <> more, e)) -> S.Tiles(s, ONode.Node.parent(x) <> more, e):
  match x y:
    case ONode.Node{+la, +ia} ONode.Node{+lb, +ib}:
      (st, sty, tt) = tiles
      +rest = Bool.and(Bool.not(OBits.Bits.low(ia)), Bool.and(OBits.Bits.low(ib), OBits.Bits.eq(OBits.Bits.up(ia), OBits.Bits.up(ib))))
      lowf = cover.and_l(Bool.not(OBits.Bits.low(ia)), Bool.and(OBits.Bits.low(ib), OBits.Bits.eq(OBits.Bits.up(ia), OBits.Bits.up(ib))), cover.and_r(Nat.is_eq(la, lb), rest, sib))
      leq = cover.eq_of_is_eq(la, lb, cover.and_l(Nat.is_eq(la, lb), rest, sib))
      (cover.start_par(la, ia, s, lowf, st), cover.tail(la, lb, s, more, e, leq, tt))

def cover.here(vr: List<&2, ONode.Node>, +x: ONode.Node, -z: ONode.Node, -wr: List<&2, ONode.Node>, +info: OInfo.Info, +s: Nat, -e: Nat, tiles: S.Tiles(s, x <> vr, e), h: S.Here(info, x, vr, z, wr)) -> S.Tiles(s, z <> wr, e):
  match vr:
    case Nil{}:
      match h:
    case +y <> more:
      (mg, zp, wm) = h
      %Equal.sym(ONode.Node, z, ONode.Node.parent(x), zp) : S.Tiles(s, _ <> wr, e)
      %Equal.sym(List<&2, ONode.Node>, wr, more, wm) : S.Tiles(s, ONode.Node.parent(x) <> _, e)
      cover.pair(x, y, s, more, e, cover.and_l(ONode.Node.sib(x, y), OInfo.Info.built(info, ONode.Node.parent(x)), mg), tiles)

def cover.merged(+v: List<&2, ONode.Node>, +w: List<&2, ONode.Node>, +info: OInfo.Info, +s: Nat, +e: Nat, tiles: S.Tiles(s, v, e), mg: S.Merged(info, v, w)) -> S.Tiles(s, w, e):
  match v w:
    case Nil{} _:
      match mg:
    case +x <> +vr Nil{}:
      match mg:
    case +x <> +vr +z <> +wr:
      (st, tt) = tiles
      match mg:
        case Inl{h}:
          cover.here(vr, x, z, wr, info, s, e, (st, tt), h)
        case Inr{p}:
          (xz, m) = p
          %xz : S.Tiles(s, _ <> wr, e)
          (st, cover.merged(vr, wr, info, Nat.add(s, ONode.Node.count(x)), e, tt, m))

# merge_is_one_pair
# -----------------

def cover.keep(+info: OInfo.Info, +x: ONode.Node, -vr: List<&2, ONode.Node>, -rec: List<&2, ONode.Node>, ih: Or({rec == vr : List<&2, ONode.Node>}, S.Merged(info, vr, rec))) -> Or({x <> rec == x <> vr : List<&2, ONode.Node>}, S.Merged(info, x <> vr, x <> rec)):
  match ih:
    case Inl{eq}:
      Inl{Equal.cong(List<&2, ONode.Node>, List<&2, ONode.Node>, k => x <> k, rec, vr, eq)}
    case Inr{m}:
      Inr{Inr{({==}, m)}}

def cover.pick(+info: OInfo.Info, +a: ONode.Node, +x: ONode.Node, +y: ONode.Node, +more: List<&2, ONode.Node>, hit: Bool, he: {hit == Bool.and(ONode.Node.eq(x, a), OFit.mergeable(info, x, y)) : Bool}, ih: Or({OFit.merge(info, y <> more, a) == y <> more : List<&2, ONode.Node>}, S.Merged(info, y <> more, OFit.merge(info, y <> more, a)))) -> Or({OFit.merge.pick(hit, x, y, more, OFit.merge(info, y <> more, a)) == x <> y <> more : List<&2, ONode.Node>}, S.Merged(info, x <> y <> more, OFit.merge.pick(hit, x, y, more, OFit.merge(info, y <> more, a)))):
  match hit:
    case True{}:
      Inr{Inl{(cover.and_r(ONode.Node.eq(x, a), OFit.mergeable(info, x, y), Equal.sym(Bool, True{}, Bool.and(ONode.Node.eq(x, a), OFit.mergeable(info, x, y)), he)), {==}, {==})}}
    case False{}:
      cover.keep(info, x, y <> more, OFit.merge(info, y <> more, a), ih)

def cover.one(+info: OInfo.Info, +a: ONode.Node, +x: ONode.Node, rest: List<&2, ONode.Node>, ih: Or({OFit.merge(info, rest, a) == rest : List<&2, ONode.Node>}, S.Merged(info, rest, OFit.merge(info, rest, a)))) -> Or({OFit.merge.here(info, a, x, rest, OFit.merge(info, rest, a)) == x <> rest : List<&2, ONode.Node>}, S.Merged(info, x <> rest, OFit.merge.here(info, a, x, rest, OFit.merge(info, rest, a)))):
  match rest:
    case Nil{}:
      Inl{{==}}
    case +y <> +more:
      cover.pick(info, a, x, y, more, Bool.and(ONode.Node.eq(x, a), OFit.mergeable(info, x, y)), {==}, ih)

def merge_is_one_pair(+info: OInfo.Info, +v: List<&2, ONode.Node>, +a: ONode.Node) -> Or({OFit.merge(info, v, a) == v : List<&2, ONode.Node>}, S.Merged(info, v, OFit.merge(info, v, a))):
  match v:
    case Nil{}:
      Inl{{==}}
    case +x <> +rest:
      cover.one(info, a, x, rest, merge_is_one_pair(info, rest, a))

# A fit
# -----

def cover.tiles_of(+info: OInfo.Info, +s: Nat, +v: List<&2, ONode.Node>, +w: List<&2, ONode.Node>, +e: Nat, tiles: S.Tiles(s, v, e), o: Or({w == v : List<&2, ONode.Node>}, S.Merged(info, v, w))) -> S.Tiles(s, w, e):
  match o:
    case Inl{eq}:
      %Equal.sym(List<&2, ONode.Node>, w, v, eq) : S.Tiles(s, _, e)
      tiles
    case Inr{m}:
      cover.merged(v, w, info, s, e, tiles, m)

def cover.merge_tiles(+info: OInfo.Info, +s: Nat, +v: List<&2, ONode.Node>, +a: ONode.Node, +e: Nat, tiles: S.Tiles(s, v, e)) -> S.Tiles(s, OFit.merge(info, v, a), e):
  cover.tiles_of(info, s, v, OFit.merge(info, v, a), e, tiles, merge_is_one_pair(info, v, a))

def cover.cons_snd(-n: ONode.Node, r: List<&2, ONode.Node> & List<&2, ONode.Node>) -> {Pair.snd(List<&2, ONode.Node>, List<&2, ONode.Node>, r) == Pair.snd(List<&2, ONode.Node>, List<&2, ONode.Node>, OFit.fit.cons(n, r)) : List<&2, ONode.Node>}:
  (ms, out) = r
  {==}

def cover.fit_go(fuel: Nat, c: Maybe<&2, ONode.Node>, +m: OFit.Age, +t: List<&2, Bool>, +budget: Nat, +ph: Nat, +info: OInfo.Info, +v: List<&2, ONode.Node>, +s: Nat, +e: Nat, tiles: S.Tiles(s, v, e)) -> S.Tiles(s, Pair.snd(List<&2, ONode.Node>, List<&2, ONode.Node>, OFit.fit.go(fuel, c, m, t, budget, ph, info, v)), e):
  match fuel c:
    case 0n _:
      tiles
    case 1n+f None{}:
      tiles
    case 1n++f Some{+a}:
      +w = OFit.merge(info, v, a)
      %cover.cons_snd(ONode.Node.parent(a), OFit.fit.go(f, OFit.choose(m, t, budget, ph, info, w), m, t, budget, ph, info, w)) : S.Tiles(s, _, e)
      cover.fit_go(f, OFit.choose(m, t, budget, ph, info, w), m, t, budget, ph, info, w, s, e, cover.merge_tiles(info, s, v, a, e, tiles))

def cover.fit_view(+m: OFit.Age, +t: List<&2, Bool>, +budget: Nat, +ph: Nat, +info: OInfo.Info, +v: List<&2, ONode.Node>, +s: Nat, +e: Nat, tiles: S.Tiles(s, v, e)) -> S.Tiles(s, OFit.fit.view(m, t, budget, ph, info, v), e):
  cover.fit_go(List.length(&2, ONode.Node, v), OFit.choose(m, t, budget, ph, info, v), m, t, budget, ph, info, v, s, e, tiles)

def cover.fitc_if(over: Bool, +cfg: OState.Cfg, +t: List<&2, Bool>, +info: OInfo.Info, +cv: List<&2, ONode.Node>, +s: Nat, +e: Nat, tiles: S.Tiles(s, cv, e)) -> S.Tiles(s, OStep.fitc.if(over, cfg, t, info, cv), e):
  match over:
    case False{}:
      tiles
    case True{}:
      cover.fit_view(OFit.Last{}, t, OState.Cfg.cfloor(cfg), OState.Cfg.ph(cfg), info, cv, s, e, tiles)

def cover.fitc(+cfg: OState.Cfg, +t: List<&2, Bool>, +info: OInfo.Info, +cv: List<&2, ONode.Node>, +s: Nat, +e: Nat, tiles: S.Tiles(s, cv, e)) -> S.Tiles(s, OStep.fitc(cfg, t, info, cv), e):
  cover.fitc_if(Nat.is_gt(OFit.view_size(OState.Cfg.ph(cfg), info, cv), OState.Cfg.cceil(cfg)), cfg, t, info, cv, s, e, tiles)

# The chat
# --------

# both views tile the messages 0..T
def cover.Inv(+s: OState.St) -> Type:
  S.Tiles(0n, OState.St.view(s), OBits.Bits.val(OState.St.t(s))) & S.Tiles(0n, OState.St.cview(s), OBits.Bits.val(OState.St.t(s)))

def cover.inv_view(-s: OState.St, inv: cover.Inv(s)) -> S.Tiles(0n, OState.St.view(s), OBits.Bits.val(OState.St.t(s))):
  (a, b) = inv
  a

# message t's line goes after a view of 0..t
def cover.app(+v: List<&2, ONode.Node>, +s: Nat, -e: Nat, +x: ONode.Node, -E: Nat, tiles: S.Tiles(s, v, e), st: {ONode.Node.start(x) == e : Nat}, ce: {Nat.add(e, ONode.Node.count(x)) == E : Nat}) -> S.Tiles(s, List.append(&2, ONode.Node, v, [x]), E):
  match v:
    case Nil{}:
      %Equal.sym(Nat, s, e, tiles) : S.Tiles(_, [x], E)
      (st, ce)
    case +h <> tl:
      (sh, tt) = tiles
      (sh, cover.app(tl, Nat.add(s, ONode.Node.count(h)), e, x, E, tt, st, ce))

def cover.grow(+v: List<&2, ONode.Node>, +t: List<&2, Bool>, tiles: S.Tiles(0n, v, OBits.Bits.val(t))) -> S.Tiles(0n, List.append(&2, ONode.Node, v, [ONode.Node.leaf(t)]), OBits.Bits.val(OBits.Bits.inc(t))):
  cover.app(v, 0n, OBits.Bits.val(t), ONode.Node.leaf(t), OBits.Bits.val(OBits.Bits.inc(t)), tiles, {==}, cover.leaf_end(t))

def cover.msg_cview(merged: List<&2, ONode.Node>, +cfg: OState.Cfg, +t: List<&2, Bool>, +info: OInfo.Info, +view: List<&2, ONode.Node>, +cv: List<&2, ONode.Node>, tv: S.Tiles(0n, view, OBits.Bits.val(t)), tc: S.Tiles(0n, cv, OBits.Bits.val(t))) -> S.Tiles(0n, OStep.msg.cview(merged, cfg, t, info, view, cv), OBits.Bits.val(t)):
  match merged:
    case Nil{}:
      cover.fitc(cfg, t, info, cv, 0n, OBits.Bits.val(t), tc)
    case h <> rest:
      cover.fit_view(OFit.Last{}, t, OState.Cfg.cfloor(cfg), OState.Cfg.ph(cfg), info, view, 0n, OBits.Bits.val(t), tv)

def cover.dup.cons(-h: ONode.Node, -s: Nat, -t: List<&2, ONode.Node>, -e: Nat, sh: {ONode.Node.start(h) == s : Nat}, p: S.Tiles(Nat.add(s, ONode.Node.count(h)), t, e) & S.Tiles(Nat.add(s, ONode.Node.count(h)), t, e)) -> S.Tiles(s, h <> t, e) & S.Tiles(s, h <> t, e):
  (a, b) = p
  %sh : ({ONode.Node.start(h) == _ : Nat} & S.Tiles(Nat.add(s, ONode.Node.count(h)), t, e)) & ({ONode.Node.start(h) == _ : Nat} & S.Tiles(Nat.add(s, ONode.Node.count(h)), t, e))
  (({==}, a), ({==}, b))

# a tiling, twice (Tiles is a Type, so it is not copied by +)
def cover.dup(+v: List<&2, ONode.Node>, +s: Nat, -e: Nat, tiles: S.Tiles(s, v, e)) -> S.Tiles(s, v, e) & S.Tiles(s, v, e):
  match v:
    case Nil{}:
      %tiles : {s == _ : Nat} & {s == _ : Nat}
      ({==}, {==})
    case +h <> tl:
      (sh, tt) = tiles
      cover.dup.cons(h, s, tl, e, sh, cover.dup(tl, Nat.add(s, ONode.Node.count(h)), e, tt))

def cover.batch.go(+merged: List<&2, ONode.Node>, +view: List<&2, ONode.Node>, +cfg: OState.Cfg, +t: List<&2, Bool>, +info: OInfo.Info, +cv: List<&2, ONode.Node>, tvs: S.Tiles(0n, view, OBits.Bits.val(t)) & S.Tiles(0n, view, OBits.Bits.val(t)), tc: S.Tiles(0n, cv, OBits.Bits.val(t))) -> S.Tiles(0n, view, OBits.Bits.val(t)) & S.Tiles(0n, OStep.msg.cview(merged, cfg, t, info, view, cv), OBits.Bits.val(t)):
  (tv, tv2) = tvs
  (tv, cover.msg_cview(merged, cfg, t, info, view, cv, tv2, tc))

def cover.batch(r: List<&2, ONode.Node> & List<&2, ONode.Node>, +cfg: OState.Cfg, +t: List<&2, Bool>, +info: OInfo.Info, +cv: List<&2, ONode.Node>, -ready: List<&2, ONode.Node>, -busy: List<&2, ONode.Node>, tv: S.Tiles(0n, Pair.snd(List<&2, ONode.Node>, List<&2, ONode.Node>, r), OBits.Bits.val(t)), tc: S.Tiles(0n, cv, OBits.Bits.val(t))) -> cover.Inv(Pair.fst(OState.St, List<&2, ONode.Node>, OStep.msg.batch(r, cfg, t, info, cv, ready, busy))):
  (merged, view0) = r
  +view = view0
  cover.batch.go(merged, view, cfg, t, info, cv, cover.dup(view, 0n, OBits.Bits.val(t), tv), tc)

def cover.msg_go(grow: Bool, +cfg: OState.Cfg, +t: List<&2, Bool>, +info: OInfo.Info, +view: List<&2, ONode.Node>, +cv: List<&2, ONode.Node>, -ready: List<&2, ONode.Node>, -busy: List<&2, ONode.Node>, tv: S.Tiles(0n, view, OBits.Bits.val(t)), tc: S.Tiles(0n, cv, OBits.Bits.val(t))) -> cover.Inv(Pair.fst(OState.St, List<&2, ONode.Node>, OStep.msg.go(grow, cfg, t, info, view, cv, ready, busy))):
  match grow:
    case False{}:
      (tv, cover.fitc(cfg, t, info, cv, 0n, OBits.Bits.val(t), tc))
    case True{}:
      cover.batch(OFit.fit(OFit.Last{}, t, OState.Cfg.floor(cfg), OState.Cfg.ph(cfg), info, view), cfg, t, info, cv, ready, busy, cover.fit_view(OFit.Last{}, t, OState.Cfg.floor(cfg), OState.Cfg.ph(cfg), info, view, 0n, OBits.Bits.val(t), tv), tc)

def cover.step(+cfg: OState.Cfg, +s: OState.St, +ev: OState.Ev, inv: cover.Inv(s)) -> cover.Inv(Pair.fst(OState.St, List<&2, ONode.Node>, OStep.step(cfg, s, ev))):
  match s ev:
    case OState.St{+t, +info, +view, shrink, +cview, +ready, +busy} OState.Msg{}:
      (tv, tc) = inv
      cover.msg_go(OStep.St.batch(cfg, OState.St{t, info, view, shrink, cview, ready, busy}), cfg, OBits.Bits.inc(t), info, List.append(&2, ONode.Node, view, [ONode.Node.leaf(t)]), List.append(&2, ONode.Node, cview, [ONode.Node.leaf(t)]), ready, busy, cover.grow(view, t, tv), cover.grow(cview, t, tc))
    case OState.St{+t, +info, +view, shrink, +cview, ready, busy} OState.Build{+n, +size}:
      (tv, tc) = inv
      (tv, cover.fitc(cfg, t, OInfo.Info.set(info, n, size), cview, 0n, OBits.Bits.val(t), tc))
    case OState.St{t, info, view, shrink, cview, ready, busy} OState.Start{n}:
      inv
    case OState.St{t, info, view, shrink, cview, ready, busy} OState.Free{n}:
      inv

def cover.run(evs: List<&2, OState.Ev>, +cfg: OState.Cfg, +s: OState.St, inv: cover.Inv(s)) -> cover.Inv(OStep.run.go(evs, cfg, s)):
  match evs:
    case Nil{}:
      inv
    case +e <> rest:
      cover.run(rest, cfg, Pair.fst(OState.St, List<&2, ONode.Node>, OStep.step(cfg, s, e)), cover.step(cfg, s, e, inv))

def cover.all(+cfg: OState.Cfg, +evs: List<&2, OState.Ev>) -> cover.Inv(OStep.run(cfg, evs)):
  cover.run(evs, cfg, OState.St.empty(), ({==}, {==}))

# The laws
# --------

def view_covers(+cfg: OState.Cfg, +evs: List<&2, OState.Ev>) -> S.Tiles(0n, S.view.of(cfg, evs), S.total.of(cfg, evs)):
  cover.inv_view(OStep.run(cfg, evs), cover.all(cfg, evs))

def pf.IsSome(m: Maybe<&2, Nat>) -> Type:
  match m:
    case None{}:
      Empty
    case Some{x}:
      Unit

def pf.to_some(m: Maybe<&2, Nat>, e: {Maybe.is_some(&2, Nat, m) == True{} : Bool}) -> pf.IsSome(m):
  match m:
    case None{}:
      LLogicLogic.pf.absurd_ft(Empty, e)
    case Some{x}:
      Unit{}

def pf.from_some(m: Maybe<&2, Nat>, s: pf.IsSome(m)) -> {Maybe.is_some(&2, Nat, m) == True{} : Bool}:
  match m:
    case None{}:
      match s:
    case Some{x}:
      {==}

def pf.implies_true(p: Bool, -b: Bool, e: {b == True{} : Bool}) -> {OBits.Bool.implies(p, b) == True{} : Bool}:
  match p:
    case False{}:
      {==}
    case True{}:
      e

# Has: a heads an adjacent pair of v that merge.here takes
# --------------------------------------------------------

def pf.Has.at(+info: OInfo.Info, +a: ONode.Node, +x: ONode.Node, rest: List<&2, ONode.Node>, rec: Bool) -> Bool:
  match rest:
    case Nil{}:
      rec
    case +y <> more:
      Bool.or(Bool.and(ONode.Node.eq(x, a), OFit.mergeable(info, x, y)), rec)

def pf.Has(+info: OInfo.Info, v: List<&2, ONode.Node>, +a: ONode.Node) -> Bool:
  match v:
    case Nil{}:
      False{}
    case +x <> +rest:
      pf.Has.at(info, a, x, rest, pf.Has(info, rest, a))

def pf.has_at(+info: OInfo.Info, +a: ONode.Node, +x: ONode.Node, rest: List<&2, ONode.Node>, -rec: Bool, e: {rec == True{} : Bool}) -> {pf.Has.at(info, a, x, rest, rec) == True{} : Bool}:
  match rest:
    case Nil{}:
      e
    case +y <> more:
      LBool.pf.or_r(Bool.and(ONode.Node.eq(x, a), OFit.mergeable(info, x, y)), rec, e)

# v with p's lines before it, p reversed
def pf.rapp(p: List<&2, ONode.Node>, v: List<&2, ONode.Node>) -> List<&2, ONode.Node>:
  match p:
    case Nil{}:
      v
    case h <> t:
      pf.rapp(t, h <> v)

def pf.has_rapp(p: List<&2, ONode.Node>, +info: OInfo.Info, +a: ONode.Node, +v: List<&2, ONode.Node>, e: {pf.Has(info, v, a) == True{} : Bool}) -> {pf.Has(info, pf.rapp(p, v), a) == True{} : Bool}:
  match p:
    case Nil{}:
      e
    case +h <> t:
      pf.has_rapp(t, info, a, h <> v, pf.has_at(info, a, h, v, pf.Has(info, v, a), e))

# Best is sound
# -------------
# Cand(info, v, r): the candidate r, if any, heads a pair of v that
# merges, and its parent is built

def pf.Cand(+info: OInfo.Info, +v: List<&2, ONode.Node>, r: Maybe<&2, ONode.Node>) -> Type:
  match r:
    case None{}:
      Unit
    case Some{+a}:
      ({pf.Has(info, v, a) == True{} : Bool} & {OInfo.Info.built(info, ONode.Node.parent(a)) == True{} : Bool})

def pf.merge_built(+info: OInfo.Info, +a: ONode.Node, +y: ONode.Node, e: {OFit.mergeable(info, a, y) == True{} : Bool}) -> {OInfo.Info.built(info, ONode.Node.parent(a)) == True{} : Bool}:
  LLogicBool.pf.and_r(ONode.Node.sib(a, y), OInfo.Info.built(info, ONode.Node.parent(a)), e)

def pf.here_has(+info: OInfo.Info, +a: ONode.Node, +y: ONode.Node, +more: List<&2, ONode.Node>, e: {True{} == OFit.mergeable(info, a, y) : Bool}) -> {pf.Has(info, a <> y <> more, a) == True{} : Bool}:
  %LOptchat.pf.node_eq_refl(a) : {Bool.or(Bool.and(_, OFit.mergeable(info, a, y)), pf.Has(info, y <> more, a)) == True{} : Bool}
  %e : {Bool.or(Bool.and(True{}, _), pf.Has(info, y <> more, a)) == True{} : Bool}
  {==}

def pf.bvs(more: Bool, +info: OInfo.Info, +w: List<&2, ONode.Node>, +a: ONode.Node, +c: ONode.Node, cw: pf.Cand(info, w, Some{c}),
  hw: {pf.Has(info, w, a) == True{} : Bool}, bw: {OInfo.Info.built(info, ONode.Node.parent(a)) == True{} : Bool})
  -> pf.Cand(info, w, Some{OFit.best.vs(more, a, c)}):
  match more:
    case True{}:
      (hw, bw)
    case False{}:
      cw

def pf.btake(cur: Maybe<&2, ONode.Node>, +m: OFit.Age, +t: List<&2, Bool>, +info: OInfo.Info, +w: List<&2, ONode.Node>, +a: ONode.Node, cw: pf.Cand(info, w, cur),
  hw: {pf.Has(info, w, a) == True{} : Bool}, bw: {OInfo.Info.built(info, ONode.Node.parent(a)) == True{} : Bool})
  -> pf.Cand(info, w, OFit.best.take(m, t, a, cur)):
  match cur:
    case None{}:
      (hw, bw)
    case Some{+c}:
      pf.bvs(OFit.more_due(m, t, a, c), info, w, a, c, cw, hw, bw)

def pf.bpick(ok: Bool, +m: OFit.Age, +t: List<&2, Bool>, +info: OInfo.Info, +pre: List<&2, ONode.Node>, +a: ONode.Node, +y: ONode.Node, +more: List<&2, ONode.Node>,
  +e: {ok == OFit.mergeable(info, a, y) : Bool}, cur: Maybe<&2, ONode.Node>, cw: pf.Cand(info, pf.rapp(pre, a <> y <> more), cur))
  -> pf.Cand(info, pf.rapp(pre, a <> y <> more), OFit.best.pick(ok, m, t, a, cur)):
  match ok:
    case False{}:
      cw
    case True{}:
      pf.btake(cur, m, t, info, pf.rapp(pre, a <> y <> more), a, cw, pf.has_rapp(pre, info, a, a <> y <> more, pf.here_has(info, a, y, more, e)), pf.merge_built(info, a, y, Equal.sym(Bool, True{}, OFit.mergeable(info, a, y), e)))

def pf.bpair(rest: List<&2, ONode.Node>, +m: OFit.Age, +t: List<&2, Bool>, +info: OInfo.Info, +pre: List<&2, ONode.Node>, +a: ONode.Node, cur: Maybe<&2, ONode.Node>, cw: pf.Cand(info, pf.rapp(pre, a <> rest), cur))
  -> pf.Cand(info, pf.rapp(pre, a <> rest), OFit.best.pair(m, t, info, a, List.head(&2, ONode.Node, rest), cur)):
  match rest:
    case Nil{}:
      cw
    case +y <> +more:
      pf.bpick(OFit.mergeable(info, a, y), m, t, info, pre, a, y, more, {==}, cur, cw)

def pf.best_sound(v: List<&2, ONode.Node>, +m: OFit.Age, +t: List<&2, Bool>, +info: OInfo.Info, +pre: List<&2, ONode.Node>, +cur: Maybe<&2, ONode.Node>, cw: pf.Cand(info, pf.rapp(pre, v), cur))
  -> pf.Cand(info, pf.rapp(pre, v), OFit.best.go(m, t, info, v, cur)):
  match v:
    case Nil{}:
      cw
    case +a <> +rest:
      pf.best_sound(rest, m, t, info, a <> pre, OFit.best.pair(m, t, info, a, List.head(&2, ONode.Node, rest), cur), pf.bpair(rest, m, t, info, pre, a, cur, cw))

def pf.csound.if(over: Bool, +m: OFit.Age, +t: List<&2, Bool>, +info: OInfo.Info, +v: List<&2, ONode.Node>) -> pf.Cand(info, v, OFit.choose.if(over, m, t, info, v)):
  match over:
    case False{}:
      Unit{}
    case True{}:
      pf.best_sound(v, m, t, info, Nil{}, None{}, Unit{})

def pf.choose_sound(+m: OFit.Age, +t: List<&2, Bool>, +budget: Nat, +ph: Nat, +info: OInfo.Info, +v: List<&2, ONode.Node>) -> pf.Cand(info, v, OFit.choose(m, t, budget, ph, info, v)):
  pf.csound.if(Nat.is_gt(OFit.view_size(ph, info, v), budget), m, t, info, v)

def pf.snd_cons(-n: ONode.Node, r: List<&2, ONode.Node> & List<&2, ONode.Node>) -> {Pair.snd(List<&2, ONode.Node>, List<&2, ONode.Node>, r) == Pair.snd(List<&2, ONode.Node>, List<&2, ONode.Node>, OFit.fit.cons(n, r)) : List<&2, ONode.Node>}:
  (ms, out) = r
  {==}

# Built nodes stay built
# ----------------------

def pf.trie_mono(tr: OInfo.Trie, k: List<&2, Bool>, i: List<&2, Bool>, +sz: Nat, e: pf.IsSome(OInfo.Trie.get(k, tr))) -> pf.IsSome(OInfo.Trie.get(k, OInfo.Trie.set(i, tr, sz))):
  match tr:
    case OInfo.Tip{}:
      match k:
        case Nil{}:
          match e:
        case b <> kr:
          match b:
            case False{}:
              match e:
            case True{}:
              match e:
    case OInfo.Bin{v, lo, hi}:
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

def pf.lvls_mono(ts: List<&2, OInfo.Trie>, lh: Nat, l: Nat, +k: List<&2, Bool>, +i: List<&2, Bool>, +sz: Nat, e: pf.IsSome(OInfo.Lvls.get(lh, ts, k))) -> pf.IsSome(OInfo.Lvls.get(lh, OInfo.Lvls.set(l, ts, i, sz), k)):
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

def pf.built_set(info: OInfo.Info, n: ONode.Node, +sz: Nat, h: ONode.Node, e: {OInfo.Info.built(info, h) == True{} : Bool}) -> {OInfo.Info.built(OInfo.Info.set(info, n, sz), h) == True{} : Bool}:
  match info:
    case OInfo.All{a}:
      {==}
    case OInfo.Lvls{+ts}:
      match n h:
        case ONode.Node{+l, +i} ONode.Node{+lh, +ih}:
          pf.from_some(OInfo.Lvls.get(lh, OInfo.Lvls.set(l, ts, i, sz), ih), pf.lvls_mono(ts, lh, l, ih, i, sz, pf.to_some(OInfo.Lvls.get(lh, ts, ih), e)))

# Summarized survives
# -------------------

def pf.summ_h(p: Bool, +info: OInfo.Info, +n: ONode.Node, +sz: Nat, +h: ONode.Node, e: {OBits.Bool.implies(p, OInfo.Info.built(info, h)) == True{} : Bool}) -> {OBits.Bool.implies(p, OInfo.Info.built(OInfo.Info.set(info, n, sz), h)) == True{} : Bool}:
  match p:
    case False{}:
      {==}
    case True{}:
      pf.built_set(info, n, sz, h, e)

def pf.summ_set(v: List<&2, ONode.Node>, +info: OInfo.Info, +n: ONode.Node, +sz: Nat, s: S.Summarized(info, v)) -> S.Summarized(OInfo.Info.set(info, n, sz), v):
  match v:
    case Nil{}:
      Unit{}
    case +h <> +t:
      (eh, st) = s
      (pf.summ_h(OBits.Nat.is_pos(ONode.Node.lvl(h)), info, n, sz, h, eh), pf.summ_set(t, info, n, sz, st))

def pf.summ_app(v: List<&2, ONode.Node>, +info: OInfo.Info, +t: List<&2, Bool>, s: S.Summarized(info, v)) -> S.Summarized(info, List.append(&2, ONode.Node, v, [ONode.Node.leaf(t)])):
  match v:
    case Nil{}:
      ({==}, Unit{})
    case +h <> +r:
      (eh, sr) = s
      (eh, pf.summ_app(r, info, t, sr))

def pf.summ_dup.fin(-info: OInfo.Info, -h: ONode.Node, -t: List<&2, ONode.Node>, +eh: {OBits.Bool.implies(OBits.Nat.is_pos(ONode.Node.lvl(h)), OInfo.Info.built(info, h)) == True{} : Bool}, p: (S.Summarized(info, t) & S.Summarized(info, t)))
  -> (S.Summarized(info, h <> t) & S.Summarized(info, h <> t)):
  (x, y) = p
  ((eh, x), (eh, y))

def pf.summ_dup(v: List<&2, ONode.Node>, +info: OInfo.Info, s: S.Summarized(info, v)) -> (S.Summarized(info, v) & S.Summarized(info, v)):
  match v:
    case Nil{}:
      (Unit{}, Unit{})
    case +h <> +t:
      (eh, st) = s
      pf.summ_dup.fin(info, h, t, eh, pf.summ_dup(t, info, st))

def pf.msumm.pick(h: Bool, +info: OInfo.Info, +a: ONode.Node, +x: ONode.Node, +y: ONode.Node, +more: List<&2, ONode.Node>,
  e: {h == Bool.and(ONode.Node.eq(x, a), OFit.mergeable(info, x, y)) : Bool},
  hx: {OBits.Bool.implies(OBits.Nat.is_pos(ONode.Node.lvl(x)), OInfo.Info.built(info, x)) == True{} : Bool},
  sr: S.Summarized(info, y <> more), ih: S.Summarized(info, y <> more) -> S.Summarized(info, OFit.merge(info, y <> more, a)))
  -> S.Summarized(info, OFit.merge.pick(h, x, y, more, OFit.merge(info, y <> more, a))):
  match h:
    case True{}:
      (ey, sm) = sr
      (pf.implies_true(OBits.Nat.is_pos(ONode.Node.lvl(ONode.Node.parent(x))), OInfo.Info.built(info, ONode.Node.parent(x)), pf.merge_built(info, x, y, LLogicBool.pf.and_r(ONode.Node.eq(x, a), OFit.mergeable(info, x, y), Equal.sym(Bool, True{}, Bool.and(ONode.Node.eq(x, a), OFit.mergeable(info, x, y)), e)))), sm)
    case False{}:
      (hx, ih(sr))

def pf.msumm.here(+info: OInfo.Info, +a: ONode.Node, +x: ONode.Node, rest: List<&2, ONode.Node>,
  hx: {OBits.Bool.implies(OBits.Nat.is_pos(ONode.Node.lvl(x)), OInfo.Info.built(info, x)) == True{} : Bool},
  sr: S.Summarized(info, rest), ih: S.Summarized(info, rest) -> S.Summarized(info, OFit.merge(info, rest, a)))
  -> S.Summarized(info, OFit.merge.here(info, a, x, rest, OFit.merge(info, rest, a))):
  match rest:
    case Nil{}:
      (hx, Unit{})
    case +y <> +more:
      pf.msumm.pick(Bool.and(ONode.Node.eq(x, a), OFit.mergeable(info, x, y)), info, a, x, y, more, {==}, hx, sr, ih)

def pf.msumm.cons(+info: OInfo.Info, +a: ONode.Node, +x: ONode.Node, +rest: List<&2, ONode.Node>, s: S.Summarized(info, x <> rest),
  ih: S.Summarized(info, rest) -> S.Summarized(info, OFit.merge(info, rest, a)))
  -> S.Summarized(info, OFit.merge(info, x <> rest, a)):
  (hx, sr) = s
  pf.msumm.here(info, a, x, rest, hx, sr, ih)

def pf.merge_summ(v: List<&2, ONode.Node>, +info: OInfo.Info, +a: ONode.Node) -> S.Summarized(info, v) -> S.Summarized(info, OFit.merge(info, v, a)):
  match v:
    case Nil{}:
      s => Unit{}
    case +x <> +rest:
      s => pf.msumm.cons(info, a, x, rest, s, pf.merge_summ(rest, info, a))

def pf.fsumm.go(fuel: Nat, c: Maybe<&2, ONode.Node>, +m: OFit.Age, +t: List<&2, Bool>, +budget: Nat, +ph: Nat, +info: OInfo.Info, +v: List<&2, ONode.Node>, s: S.Summarized(info, v))
  -> S.Summarized(info, Pair.snd(List<&2, ONode.Node>, List<&2, ONode.Node>, OFit.fit.go(fuel, c, m, t, budget, ph, info, v))):
  match fuel c:
    case 0n _:
      s
    case 1n+f None{}:
      s
    case 1n++f Some{+a}:
      %pf.snd_cons(ONode.Node.parent(a), OFit.fit.go(f, OFit.choose(m, t, budget, ph, info, OFit.merge(info, v, a)), m, t, budget, ph, info, OFit.merge(info, v, a))) : S.Summarized(info, _)
      pf.fsumm.go(f, OFit.choose(m, t, budget, ph, info, OFit.merge(info, v, a)), m, t, budget, ph, info, OFit.merge(info, v, a), pf.merge_summ(v, info, a)(s))

def pf.fit_summ(+m: OFit.Age, +t: List<&2, Bool>, +budget: Nat, +ph: Nat, +info: OInfo.Info, +v: List<&2, ONode.Node>, s: S.Summarized(info, v))
  -> S.Summarized(info, OFit.fit.view(m, t, budget, ph, info, v)):
  pf.fsumm.go(List.length(&2, ONode.Node, v), OFit.choose(m, t, budget, ph, info, v), m, t, budget, ph, info, v, s)

def pf.fcsumm.if(over: Bool, +cfg: OState.Cfg, +t: List<&2, Bool>, +info: OInfo.Info, +cv: List<&2, ONode.Node>, s: S.Summarized(info, cv)) -> S.Summarized(info, OStep.fitc.if(over, cfg, t, info, cv)):
  match over:
    case False{}:
      s
    case True{}:
      pf.fit_summ(OFit.Last{}, t, OState.Cfg.cfloor(cfg), OState.Cfg.ph(cfg), info, cv, s)

def pf.fitc_summ(+cfg: OState.Cfg, +t: List<&2, Bool>, +info: OInfo.Info, +cv: List<&2, ONode.Node>, s: S.Summarized(info, cv)) -> S.Summarized(info, OStep.fitc(cfg, t, info, cv)):
  pf.fcsumm.if(Nat.is_gt(OFit.view_size(OState.Cfg.ph(cfg), info, cv), OState.Cfg.cceil(cfg)), cfg, t, info, cv, s)

# The history
# -----------

def fit.pf.Inv(+s: OState.St) -> Type:
  (S.Summarized(OState.St.info(s), OState.St.view(s)) & S.Summarized(OState.St.info(s), OState.St.cview(s)))

def pf.mcv(merged: List<&2, ONode.Node>, +cfg: OState.Cfg, +t: List<&2, Bool>, +info: OInfo.Info, +view: List<&2, ONode.Node>, +cv: List<&2, ONode.Node>, sv: S.Summarized(info, view), sc: S.Summarized(info, cv))
  -> S.Summarized(info, OStep.msg.cview(merged, cfg, t, info, view, cv)):
  match merged:
    case Nil{}:
      pf.fitc_summ(cfg, t, info, cv, sc)
    case h <> rest:
      pf.fit_summ(OFit.Last{}, t, OState.Cfg.cfloor(cfg), OState.Cfg.ph(cfg), info, view, sv)

def pf.batch.fin(+merged: List<&2, ONode.Node>, +view: List<&2, ONode.Node>, +cfg: OState.Cfg, +t: List<&2, Bool>, +info: OInfo.Info, +cv: List<&2, ONode.Node>, +ready: List<&2, ONode.Node>, +busy: List<&2, ONode.Node>,
  d: (S.Summarized(info, view) & S.Summarized(info, view)), sc: S.Summarized(info, cv))
  -> fit.pf.Inv(Pair.fst(OState.St, List<&2, ONode.Node>, OStep.msg.after(merged, view, cfg, t, info, cv, ready, busy))):
  (s1, s2) = d
  (s1, pf.mcv(merged, cfg, t, info, view, cv, s2, sc))

def pf.batch_inv(r: List<&2, ONode.Node> & List<&2, ONode.Node>, +cfg: OState.Cfg, +t: List<&2, Bool>, +info: OInfo.Info, +cv: List<&2, ONode.Node>, +ready: List<&2, ONode.Node>, +busy: List<&2, ONode.Node>)
  -> S.Summarized(info, Pair.snd(List<&2, ONode.Node>, List<&2, ONode.Node>, r)) -> S.Summarized(info, cv) -> fit.pf.Inv(Pair.fst(OState.St, List<&2, ONode.Node>, OStep.msg.batch(r, cfg, t, info, cv, ready, busy))):
  (merged, view0) = r
  +view = view0
  sv => sc => pf.batch.fin(merged, view, cfg, t, info, cv, ready, busy, pf.summ_dup(view, info, sv), sc)

def pf.msg_go_inv(grow: Bool, +cfg: OState.Cfg, +t: List<&2, Bool>, +info: OInfo.Info, +gv: List<&2, ONode.Node>, +gcv: List<&2, ONode.Node>, +ready: List<&2, ONode.Node>, +busy: List<&2, ONode.Node>,
  hv: S.Summarized(info, gv), hc: S.Summarized(info, gcv))
  -> fit.pf.Inv(Pair.fst(OState.St, List<&2, ONode.Node>, OStep.msg.go(grow, cfg, t, info, gv, gcv, ready, busy))):
  match grow:
    case False{}:
      (hv, pf.fitc_summ(cfg, t, info, gcv, hc))
    case True{}:
      pf.batch_inv(OFit.fit(OFit.Last{}, t, OState.Cfg.floor(cfg), OState.Cfg.ph(cfg), info, gv), cfg, t, info, gcv, ready, busy)(pf.fit_summ(OFit.Last{}, t, OState.Cfg.floor(cfg), OState.Cfg.ph(cfg), info, gv, hv))(hc)

def pf.step_msg(+cfg: OState.Cfg, +t: List<&2, Bool>, +info: OInfo.Info, +view: List<&2, ONode.Node>, +shrink: Bool, +cview: List<&2, ONode.Node>, +ready: List<&2, ONode.Node>, +busy: List<&2, ONode.Node>,
  i: fit.pf.Inv(OState.St{t, info, view, shrink, cview, ready, busy}))
  -> fit.pf.Inv(Pair.fst(OState.St, List<&2, ONode.Node>, OStep.msg(cfg, OState.St{t, info, view, shrink, cview, ready, busy}))):
  (hv, hc) = i
  pf.msg_go_inv(OStep.St.batch(cfg, OState.St{t, info, view, shrink, cview, ready, busy}), cfg, OBits.Bits.inc(t), info, List.append(&2, ONode.Node, view, [ONode.Node.leaf(t)]), List.append(&2, ONode.Node, cview, [ONode.Node.leaf(t)]), ready, busy, pf.summ_app(view, info, t, hv), pf.summ_app(cview, info, t, hc))

def pf.step_build(+cfg: OState.Cfg, +t: List<&2, Bool>, +info: OInfo.Info, +view: List<&2, ONode.Node>, +shrink: Bool, +cview: List<&2, ONode.Node>, +ready: List<&2, ONode.Node>, +busy: List<&2, ONode.Node>, +n: ONode.Node, +size: Nat,
  i: fit.pf.Inv(OState.St{t, info, view, shrink, cview, ready, busy}))
  -> fit.pf.Inv(OStep.build(cfg, OState.St{t, info, view, shrink, cview, ready, busy}, n, size)):
  (hv, hc) = i
  (pf.summ_set(view, info, n, size, hv), pf.fitc_summ(cfg, t, OInfo.Info.set(info, n, size), cview, pf.summ_set(cview, info, n, size, hc)))

def pf.step_inv(+cfg: OState.Cfg, s: OState.St, e: OState.Ev) -> fit.pf.Inv(s) -> fit.pf.Inv(Pair.fst(OState.St, List<&2, ONode.Node>, OStep.step(cfg, s, e))):
  match s e:
    case OState.St{+t, +info, +view, +shrink, +cview, +ready, +busy} OState.Msg{}:
      i => pf.step_msg(cfg, t, info, view, shrink, cview, ready, busy, i)
    case OState.St{+t, +info, +view, +shrink, +cview, +ready, +busy} OState.Build{+n, +size}:
      i => pf.step_build(cfg, t, info, view, shrink, cview, ready, busy, n, size, i)
    case OState.St{+t, +info, +view, +shrink, +cview, +ready, +busy} OState.Start{n}:
      i => i
    case OState.St{+t, +info, +view, +shrink, +cview, +ready, +busy} OState.Free{n}:
      i => i

def pf.run_inv(evs: List<&2, OState.Ev>, +cfg: OState.Cfg, +s: OState.St, i: fit.pf.Inv(s)) -> fit.pf.Inv(OStep.run.go(evs, cfg, s)):
  match evs:
    case Nil{}:
      i
    case +e <> rest:
      pf.run_inv(rest, cfg, Pair.fst(OState.St, List<&2, ONode.Node>, OStep.step(cfg, s, e)), pf.step_inv(cfg, s, e)(i))

def pf.run_summ(+cfg: OState.Cfg, +evs: List<&2, OState.Ev>) -> fit.pf.Inv(OStep.run(cfg, evs)):
  pf.run_inv(evs, cfg, OState.St.empty(), (Unit{}, Unit{}))

def pa.cmp0_dbl(n: Nat) -> {Nat.cmp(0n, Nat.double(n)) == Nat.cmp(0n, n) : Cmp}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      {==}

def pa.cmp_dbl0(n: Nat) -> {Nat.cmp(Nat.double(n), 0n) == Nat.cmp(n, 0n) : Cmp}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      {==}

def pa.cmp_nil(ys: List<&2, Bool>) -> {OBits.Cmp.of_zero(OBits.Bits.is_zero(ys), LT{}) == Nat.cmp(0n, OBits.Bits.val(ys)) : Cmp}:
  match ys:
    case Nil{}:
      {==}
    case h <> +t:
      match h:
        case True{}:
          {==}
        case False{}:
          Equal.trans(Cmp, OBits.Cmp.of_zero(OBits.Bits.is_zero(t), LT{}), Nat.cmp(0n, OBits.Bits.val(t)), Nat.cmp(0n, Nat.double(OBits.Bits.val(t))), pa.cmp_nil(t), Equal.sym(Cmp, Nat.cmp(0n, Nat.double(OBits.Bits.val(t))), Nat.cmp(0n, OBits.Bits.val(t)), pa.cmp0_dbl(OBits.Bits.val(t))))

def pa.cmp_nil_r(xs: List<&2, Bool>) -> {OBits.Cmp.of_zero(OBits.Bits.is_zero(xs), GT{}) == Nat.cmp(OBits.Bits.val(xs), 0n) : Cmp}:
  match xs:
    case Nil{}:
      {==}
    case h <> +t:
      match h:
        case True{}:
          {==}
        case False{}:
          Equal.trans(Cmp, OBits.Cmp.of_zero(OBits.Bits.is_zero(t), GT{}), Nat.cmp(OBits.Bits.val(t), 0n), Nat.cmp(Nat.double(OBits.Bits.val(t)), 0n), pa.cmp_nil_r(t), Equal.sym(Cmp, Nat.cmp(Nat.double(OBits.Bits.val(t)), 0n), Nat.cmp(OBits.Bits.val(t), 0n), pa.cmp_dbl0(OBits.Bits.val(t))))

# comparing two numbers by their higher bits, then the lowest
def pa.cmp_bit(A: Nat, B: Nat, x: Bool, y: Bool) -> {OBits.Cmp.then(Nat.cmp(A, B), Bool.cmp(x, y)) == Nat.cmp(OBits.bit(x, Nat.double(A)), OBits.bit(y, Nat.double(B))) : Cmp}:
  match A B:
    case 0n 0n:
      match x y:
        case False{} False{}:
          {==}
        case False{} True{}:
          {==}
        case True{} False{}:
          {==}
        case True{} True{}:
          {==}
    case 0n 1n+q:
      match x y:
        case False{} False{}:
          {==}
        case False{} True{}:
          {==}
        case True{} False{}:
          {==}
        case True{} True{}:
          {==}
    case 1n+p 0n:
      match x y:
        case False{} False{}:
          {==}
        case False{} True{}:
          {==}
        case True{} False{}:
          {==}
        case True{} True{}:
          {==}
    case 1n+p 1n+q:
      match x y:
        case False{} False{}:
          pa.cmp_bit(p, q, False{}, False{})
        case False{} True{}:
          pa.cmp_bit(p, q, False{}, True{})
        case True{} False{}:
          pa.cmp_bit(p, q, True{}, False{})
        case True{} True{}:
          pa.cmp_bit(p, q, True{}, True{})

# bit lists compare as their values
def pa.cmp_val(xs: List<&2, Bool>, ys: List<&2, Bool>) -> {OBits.Bits.cmp(xs, ys) == Nat.cmp(OBits.Bits.val(xs), OBits.Bits.val(ys)) : Cmp}:
  match xs ys:
    case Nil{} ys:
      pa.cmp_nil(ys)
    case x <> xt Nil{}:
      pa.cmp_nil_r(x <> xt)
    case +x <> +xt +y <> +yt:
      Equal.trans(Cmp, OBits.Cmp.then(OBits.Bits.cmp(xt, yt), Bool.cmp(x, y)), OBits.Cmp.then(Nat.cmp(OBits.Bits.val(xt), OBits.Bits.val(yt)), Bool.cmp(x, y)), Nat.cmp(OBits.Bits.val(x <> xt), OBits.Bits.val(y <> yt)), Equal.cong(Cmp, Cmp, z => OBits.Cmp.then(z, Bool.cmp(x, y)), OBits.Bits.cmp(xt, yt), Nat.cmp(OBits.Bits.val(xt), OBits.Bits.val(yt)), pa.cmp_val(xt, yt)), pa.cmp_bit(OBits.Bits.val(xt), OBits.Bits.val(yt), x, y))
