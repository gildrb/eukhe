# eukhe: lemmas the proofs of area optchat share

import Base
import ../../bend/optchat.bend as O
import ../../bend/spec.bend as S
import ../../LAWS.bend as Laws
import ../base.bend as L

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

def cover.val_inc(b: List<&2, Bool>) -> {1n+O.Bits.val(b) == O.Bits.val(O.Bits.inc(b)) : Nat}:
  match b:
    case Nil{}:
      {==}
    case False{} <> r:
      {==}
    case True{} <> r:
      %cover.val_inc(r) : {2n+Nat.double(O.Bits.val(r)) == Nat.double(_) : Nat}
      {==}

# a node with low bit 0 starts where its parent does
def cover.val_up(i: List<&2, Bool>, lowf: {Bool.not(O.Bits.low(i)) == True{} : Bool}) -> {O.Bits.val(i) == Nat.double(O.Bits.val(O.Bits.up(i))) : Nat}:
  match i:
    case Nil{}:
      {==}
    case False{} <> r:
      {==}
    case True{} <> r:
      cover.absurd({O.Bits.val(True{} <> r) == Nat.double(O.Bits.val(r)) : Nat}, lowf)

# message t's line ends at t + 1
def cover.leaf_end(+t: List<&2, Bool>) -> {Nat.add(O.Bits.val(t), O.Node.count(O.Node.leaf(t))) == O.Bits.val(O.Bits.inc(t)) : Nat}:
  Equal.trans(Nat, Nat.add(O.Bits.val(t), 1n), 1n+O.Bits.val(t), O.Bits.val(O.Bits.inc(t)), Equal.sym(Nat, 1n+O.Bits.val(t), Nat.add(O.Bits.val(t), 1n), cover.add_one(O.Bits.val(t))), cover.val_inc(t))

# A merge
# -------

def cover.start_par(+la: Nat, +ia: List<&2, Bool>, -s: Nat, lowf: {Bool.not(O.Bits.low(ia)) == True{} : Bool}, st: {O.shl(la, O.Bits.val(ia)) == s : Nat}) -> {O.shl(1n+la, O.Bits.val(O.Bits.up(ia))) == s : Nat}:
  %cover.val_up(ia, lowf) : {O.shl(la, _) == s : Nat}
  st

def cover.sum(s: Nat, +la: Nat, -lb: Nat, leq: {la == lb : Nat}) -> {Nat.add(Nat.add(s, O.pow2(la)), O.pow2(lb)) == Nat.add(s, Nat.double(O.pow2(la))) : Nat}:
  %leq : {Nat.add(Nat.add(s, O.pow2(la)), O.pow2(_)) == Nat.add(s, Nat.double(O.pow2(la))) : Nat}
  cover.add_double(s, O.pow2(la))

def cover.tail(+la: Nat, -lb: Nat, +s: Nat, -more: List<&2, O.Node>, -e: Nat, leq: {la == lb : Nat}, tt: S.Tiles(Nat.add(Nat.add(s, O.pow2(la)), O.pow2(lb)), more, e)) -> S.Tiles(Nat.add(s, O.pow2(1n+la)), more, e):
  %cover.sum(s, la, lb, leq) : S.Tiles(_, more, e)
  tt

# sibling lines x, y tile like their parent
def cover.pair(+x: O.Node, +y: O.Node, +s: Nat, -more: List<&2, O.Node>, -e: Nat, +sib: {O.Node.sib(x, y) == True{} : Bool}, tiles: S.Tiles(s, x <> y <> more, e)) -> S.Tiles(s, O.Node.parent(x) <> more, e):
  match x y:
    case O.Node{+la, +ia} O.Node{+lb, +ib}:
      (st, sty, tt) = tiles
      +rest = Bool.and(Bool.not(O.Bits.low(ia)), Bool.and(O.Bits.low(ib), O.Bits.eq(O.Bits.up(ia), O.Bits.up(ib))))
      lowf = cover.and_l(Bool.not(O.Bits.low(ia)), Bool.and(O.Bits.low(ib), O.Bits.eq(O.Bits.up(ia), O.Bits.up(ib))), cover.and_r(Nat.is_eq(la, lb), rest, sib))
      leq = cover.eq_of_is_eq(la, lb, cover.and_l(Nat.is_eq(la, lb), rest, sib))
      (cover.start_par(la, ia, s, lowf, st), cover.tail(la, lb, s, more, e, leq, tt))

def cover.here(vr: List<&2, O.Node>, +x: O.Node, -z: O.Node, -wr: List<&2, O.Node>, +info: O.Info, +s: Nat, -e: Nat, tiles: S.Tiles(s, x <> vr, e), h: S.Here(info, x, vr, z, wr)) -> S.Tiles(s, z <> wr, e):
  match vr:
    case Nil{}:
      match h:
    case +y <> more:
      (mg, zp, wm) = h
      %Equal.sym(O.Node, z, O.Node.parent(x), zp) : S.Tiles(s, _ <> wr, e)
      %Equal.sym(List<&2, O.Node>, wr, more, wm) : S.Tiles(s, O.Node.parent(x) <> _, e)
      cover.pair(x, y, s, more, e, cover.and_l(O.Node.sib(x, y), O.Info.built(info, O.Node.parent(x)), mg), tiles)

def cover.merged(+v: List<&2, O.Node>, +w: List<&2, O.Node>, +info: O.Info, +s: Nat, +e: Nat, tiles: S.Tiles(s, v, e), mg: S.Merged(info, v, w)) -> S.Tiles(s, w, e):
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
          (st, cover.merged(vr, wr, info, Nat.add(s, O.Node.count(x)), e, tt, m))

# merge_is_one_pair
# -----------------

def cover.keep(+info: O.Info, +x: O.Node, -vr: List<&2, O.Node>, -rec: List<&2, O.Node>, ih: Or({rec == vr : List<&2, O.Node>}, S.Merged(info, vr, rec))) -> Or({x <> rec == x <> vr : List<&2, O.Node>}, S.Merged(info, x <> vr, x <> rec)):
  match ih:
    case Inl{eq}:
      Inl{Equal.cong(List<&2, O.Node>, List<&2, O.Node>, k => x <> k, rec, vr, eq)}
    case Inr{m}:
      Inr{Inr{({==}, m)}}

def cover.pick(+info: O.Info, +a: O.Node, +x: O.Node, +y: O.Node, +more: List<&2, O.Node>, hit: Bool, he: {hit == Bool.and(O.Node.eq(x, a), O.mergeable(info, x, y)) : Bool}, ih: Or({O.merge(info, y <> more, a) == y <> more : List<&2, O.Node>}, S.Merged(info, y <> more, O.merge(info, y <> more, a)))) -> Or({O.merge.pick(hit, x, y, more, O.merge(info, y <> more, a)) == x <> y <> more : List<&2, O.Node>}, S.Merged(info, x <> y <> more, O.merge.pick(hit, x, y, more, O.merge(info, y <> more, a)))):
  match hit:
    case True{}:
      Inr{Inl{(cover.and_r(O.Node.eq(x, a), O.mergeable(info, x, y), Equal.sym(Bool, True{}, Bool.and(O.Node.eq(x, a), O.mergeable(info, x, y)), he)), {==}, {==})}}
    case False{}:
      cover.keep(info, x, y <> more, O.merge(info, y <> more, a), ih)

def cover.one(+info: O.Info, +a: O.Node, +x: O.Node, rest: List<&2, O.Node>, ih: Or({O.merge(info, rest, a) == rest : List<&2, O.Node>}, S.Merged(info, rest, O.merge(info, rest, a)))) -> Or({O.merge.here(info, a, x, rest, O.merge(info, rest, a)) == x <> rest : List<&2, O.Node>}, S.Merged(info, x <> rest, O.merge.here(info, a, x, rest, O.merge(info, rest, a)))):
  match rest:
    case Nil{}:
      Inl{{==}}
    case +y <> +more:
      cover.pick(info, a, x, y, more, Bool.and(O.Node.eq(x, a), O.mergeable(info, x, y)), {==}, ih)

def merge_is_one_pair(+info: O.Info, +v: List<&2, O.Node>, +a: O.Node) -> Or({O.merge(info, v, a) == v : List<&2, O.Node>}, S.Merged(info, v, O.merge(info, v, a))):
  match v:
    case Nil{}:
      Inl{{==}}
    case +x <> +rest:
      cover.one(info, a, x, rest, merge_is_one_pair(info, rest, a))

# A fit
# -----

def cover.tiles_of(+info: O.Info, +s: Nat, +v: List<&2, O.Node>, +w: List<&2, O.Node>, +e: Nat, tiles: S.Tiles(s, v, e), o: Or({w == v : List<&2, O.Node>}, S.Merged(info, v, w))) -> S.Tiles(s, w, e):
  match o:
    case Inl{eq}:
      %Equal.sym(List<&2, O.Node>, w, v, eq) : S.Tiles(s, _, e)
      tiles
    case Inr{m}:
      cover.merged(v, w, info, s, e, tiles, m)

def cover.merge_tiles(+info: O.Info, +s: Nat, +v: List<&2, O.Node>, +a: O.Node, +e: Nat, tiles: S.Tiles(s, v, e)) -> S.Tiles(s, O.merge(info, v, a), e):
  cover.tiles_of(info, s, v, O.merge(info, v, a), e, tiles, merge_is_one_pair(info, v, a))

def cover.cons_snd(-n: O.Node, r: List<&2, O.Node> & List<&2, O.Node>) -> {Pair.snd(List<&2, O.Node>, List<&2, O.Node>, r) == Pair.snd(List<&2, O.Node>, List<&2, O.Node>, O.fit.cons(n, r)) : List<&2, O.Node>}:
  (ms, out) = r
  {==}

def cover.fit_go(fuel: Nat, c: Maybe<&2, O.Node>, +m: O.Age, +t: List<&2, Bool>, +budget: Nat, +ph: Nat, +info: O.Info, +v: List<&2, O.Node>, +s: Nat, +e: Nat, tiles: S.Tiles(s, v, e)) -> S.Tiles(s, Pair.snd(List<&2, O.Node>, List<&2, O.Node>, O.fit.go(fuel, c, m, t, budget, ph, info, v)), e):
  match fuel c:
    case 0n _:
      tiles
    case 1n+f None{}:
      tiles
    case 1n++f Some{+a}:
      +w = O.merge(info, v, a)
      %cover.cons_snd(O.Node.parent(a), O.fit.go(f, O.choose(m, t, budget, ph, info, w), m, t, budget, ph, info, w)) : S.Tiles(s, _, e)
      cover.fit_go(f, O.choose(m, t, budget, ph, info, w), m, t, budget, ph, info, w, s, e, cover.merge_tiles(info, s, v, a, e, tiles))

def cover.fit_view(+m: O.Age, +t: List<&2, Bool>, +budget: Nat, +ph: Nat, +info: O.Info, +v: List<&2, O.Node>, +s: Nat, +e: Nat, tiles: S.Tiles(s, v, e)) -> S.Tiles(s, O.fit.view(m, t, budget, ph, info, v), e):
  cover.fit_go(List.length(&2, O.Node, v), O.choose(m, t, budget, ph, info, v), m, t, budget, ph, info, v, s, e, tiles)

def cover.fitc_if(over: Bool, +cfg: O.Cfg, +t: List<&2, Bool>, +info: O.Info, +cv: List<&2, O.Node>, +s: Nat, +e: Nat, tiles: S.Tiles(s, cv, e)) -> S.Tiles(s, O.fitc.if(over, cfg, t, info, cv), e):
  match over:
    case False{}:
      tiles
    case True{}:
      cover.fit_view(O.Last{}, t, O.Cfg.cfloor(cfg), O.Cfg.ph(cfg), info, cv, s, e, tiles)

def cover.fitc(+cfg: O.Cfg, +t: List<&2, Bool>, +info: O.Info, +cv: List<&2, O.Node>, +s: Nat, +e: Nat, tiles: S.Tiles(s, cv, e)) -> S.Tiles(s, O.fitc(cfg, t, info, cv), e):
  cover.fitc_if(Nat.is_gt(O.view_size(O.Cfg.ph(cfg), info, cv), O.Cfg.cceil(cfg)), cfg, t, info, cv, s, e, tiles)

# The chat
# --------

# both views tile the messages 0..T
def cover.Inv(+s: O.St) -> Type:
  S.Tiles(0n, O.St.view(s), O.Bits.val(O.St.t(s))) & S.Tiles(0n, O.St.cview(s), O.Bits.val(O.St.t(s)))

def cover.inv_view(-s: O.St, inv: cover.Inv(s)) -> S.Tiles(0n, O.St.view(s), O.Bits.val(O.St.t(s))):
  (a, b) = inv
  a

# message t's line goes after a view of 0..t
def cover.app(+v: List<&2, O.Node>, +s: Nat, -e: Nat, +x: O.Node, -E: Nat, tiles: S.Tiles(s, v, e), st: {O.Node.start(x) == e : Nat}, ce: {Nat.add(e, O.Node.count(x)) == E : Nat}) -> S.Tiles(s, List.append(&2, O.Node, v, [x]), E):
  match v:
    case Nil{}:
      %Equal.sym(Nat, s, e, tiles) : S.Tiles(_, [x], E)
      (st, ce)
    case +h <> tl:
      (sh, tt) = tiles
      (sh, cover.app(tl, Nat.add(s, O.Node.count(h)), e, x, E, tt, st, ce))

def cover.grow(+v: List<&2, O.Node>, +t: List<&2, Bool>, tiles: S.Tiles(0n, v, O.Bits.val(t))) -> S.Tiles(0n, List.append(&2, O.Node, v, [O.Node.leaf(t)]), O.Bits.val(O.Bits.inc(t))):
  cover.app(v, 0n, O.Bits.val(t), O.Node.leaf(t), O.Bits.val(O.Bits.inc(t)), tiles, {==}, cover.leaf_end(t))

def cover.msg_cview(merged: List<&2, O.Node>, +cfg: O.Cfg, +t: List<&2, Bool>, +info: O.Info, +view: List<&2, O.Node>, +cv: List<&2, O.Node>, tv: S.Tiles(0n, view, O.Bits.val(t)), tc: S.Tiles(0n, cv, O.Bits.val(t))) -> S.Tiles(0n, O.msg.cview(merged, cfg, t, info, view, cv), O.Bits.val(t)):
  match merged:
    case Nil{}:
      cover.fitc(cfg, t, info, cv, 0n, O.Bits.val(t), tc)
    case h <> rest:
      cover.fit_view(O.Last{}, t, O.Cfg.cfloor(cfg), O.Cfg.ph(cfg), info, view, 0n, O.Bits.val(t), tv)

def cover.dup.cons(-h: O.Node, -s: Nat, -t: List<&2, O.Node>, -e: Nat, sh: {O.Node.start(h) == s : Nat}, p: S.Tiles(Nat.add(s, O.Node.count(h)), t, e) & S.Tiles(Nat.add(s, O.Node.count(h)), t, e)) -> S.Tiles(s, h <> t, e) & S.Tiles(s, h <> t, e):
  (a, b) = p
  %sh : ({O.Node.start(h) == _ : Nat} & S.Tiles(Nat.add(s, O.Node.count(h)), t, e)) & ({O.Node.start(h) == _ : Nat} & S.Tiles(Nat.add(s, O.Node.count(h)), t, e))
  (({==}, a), ({==}, b))

# a tiling, twice (Tiles is a Type, so it is not copied by +)
def cover.dup(+v: List<&2, O.Node>, +s: Nat, -e: Nat, tiles: S.Tiles(s, v, e)) -> S.Tiles(s, v, e) & S.Tiles(s, v, e):
  match v:
    case Nil{}:
      %tiles : {s == _ : Nat} & {s == _ : Nat}
      ({==}, {==})
    case +h <> tl:
      (sh, tt) = tiles
      cover.dup.cons(h, s, tl, e, sh, cover.dup(tl, Nat.add(s, O.Node.count(h)), e, tt))

def cover.batch.go(+merged: List<&2, O.Node>, +view: List<&2, O.Node>, +cfg: O.Cfg, +t: List<&2, Bool>, +info: O.Info, +cv: List<&2, O.Node>, tvs: S.Tiles(0n, view, O.Bits.val(t)) & S.Tiles(0n, view, O.Bits.val(t)), tc: S.Tiles(0n, cv, O.Bits.val(t))) -> S.Tiles(0n, view, O.Bits.val(t)) & S.Tiles(0n, O.msg.cview(merged, cfg, t, info, view, cv), O.Bits.val(t)):
  (tv, tv2) = tvs
  (tv, cover.msg_cview(merged, cfg, t, info, view, cv, tv2, tc))

def cover.batch(r: List<&2, O.Node> & List<&2, O.Node>, +cfg: O.Cfg, +t: List<&2, Bool>, +info: O.Info, +cv: List<&2, O.Node>, -ready: List<&2, O.Node>, -busy: List<&2, O.Node>, tv: S.Tiles(0n, Pair.snd(List<&2, O.Node>, List<&2, O.Node>, r), O.Bits.val(t)), tc: S.Tiles(0n, cv, O.Bits.val(t))) -> cover.Inv(Pair.fst(O.St, List<&2, O.Node>, O.msg.batch(r, cfg, t, info, cv, ready, busy))):
  (merged, view0) = r
  +view = view0
  cover.batch.go(merged, view, cfg, t, info, cv, cover.dup(view, 0n, O.Bits.val(t), tv), tc)

def cover.msg_go(grow: Bool, +cfg: O.Cfg, +t: List<&2, Bool>, +info: O.Info, +view: List<&2, O.Node>, +cv: List<&2, O.Node>, -ready: List<&2, O.Node>, -busy: List<&2, O.Node>, tv: S.Tiles(0n, view, O.Bits.val(t)), tc: S.Tiles(0n, cv, O.Bits.val(t))) -> cover.Inv(Pair.fst(O.St, List<&2, O.Node>, O.msg.go(grow, cfg, t, info, view, cv, ready, busy))):
  match grow:
    case False{}:
      (tv, cover.fitc(cfg, t, info, cv, 0n, O.Bits.val(t), tc))
    case True{}:
      cover.batch(O.fit(O.Last{}, t, O.Cfg.floor(cfg), O.Cfg.ph(cfg), info, view), cfg, t, info, cv, ready, busy, cover.fit_view(O.Last{}, t, O.Cfg.floor(cfg), O.Cfg.ph(cfg), info, view, 0n, O.Bits.val(t), tv), tc)

def cover.step(+cfg: O.Cfg, +s: O.St, +ev: O.Ev, inv: cover.Inv(s)) -> cover.Inv(Pair.fst(O.St, List<&2, O.Node>, O.step(cfg, s, ev))):
  match s ev:
    case O.St{+t, +info, +view, shrink, +cview, +ready, +busy} O.Msg{}:
      (tv, tc) = inv
      cover.msg_go(O.St.batch(cfg, O.St{t, info, view, shrink, cview, ready, busy}), cfg, O.Bits.inc(t), info, List.append(&2, O.Node, view, [O.Node.leaf(t)]), List.append(&2, O.Node, cview, [O.Node.leaf(t)]), ready, busy, cover.grow(view, t, tv), cover.grow(cview, t, tc))
    case O.St{+t, +info, +view, shrink, +cview, ready, busy} O.Build{+n, +size}:
      (tv, tc) = inv
      (tv, cover.fitc(cfg, t, O.Info.set(info, n, size), cview, 0n, O.Bits.val(t), tc))
    case O.St{t, info, view, shrink, cview, ready, busy} O.Start{n}:
      inv
    case O.St{t, info, view, shrink, cview, ready, busy} O.Free{n}:
      inv

def cover.run(evs: List<&2, O.Ev>, +cfg: O.Cfg, +s: O.St, inv: cover.Inv(s)) -> cover.Inv(O.run.go(evs, cfg, s)):
  match evs:
    case Nil{}:
      inv
    case +e <> rest:
      cover.run(rest, cfg, Pair.fst(O.St, List<&2, O.Node>, O.step(cfg, s, e)), cover.step(cfg, s, e, inv))

def cover.all(+cfg: O.Cfg, +evs: List<&2, O.Ev>) -> cover.Inv(O.run(cfg, evs)):
  cover.run(evs, cfg, O.St.empty(), ({==}, {==}))

# The laws
# --------

def view_covers(+cfg: O.Cfg, +evs: List<&2, O.Ev>) -> S.Tiles(0n, S.view.of(cfg, evs), S.total.of(cfg, evs)):
  cover.inv_view(O.run(cfg, evs), cover.all(cfg, evs))

def pf.IsSome(m: Maybe<&2, Nat>) -> Type:
  match m:
    case None{}:
      Empty
    case Some{x}:
      Unit

def pf.to_some(m: Maybe<&2, Nat>, e: {Maybe.is_some(&2, Nat, m) == True{} : Bool}) -> pf.IsSome(m):
  match m:
    case None{}:
      L.pf.absurd_ft(Empty, e)
    case Some{x}:
      Unit{}

def pf.from_some(m: Maybe<&2, Nat>, s: pf.IsSome(m)) -> {Maybe.is_some(&2, Nat, m) == True{} : Bool}:
  match m:
    case None{}:
      match s:
    case Some{x}:
      {==}

def pf.implies_true(p: Bool, -b: Bool, e: {b == True{} : Bool}) -> {O.Bool.implies(p, b) == True{} : Bool}:
  match p:
    case False{}:
      {==}
    case True{}:
      e

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
      L.pf.or_r(Bool.and(O.Node.eq(x, a), O.mergeable(info, x, y)), rec, e)

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
  L.pf.and_r(O.Node.sib(a, y), O.Info.built(info, O.Node.parent(a)), e)

def pf.here_has(+info: O.Info, +a: O.Node, +y: O.Node, +more: List<&2, O.Node>, e: {True{} == O.mergeable(info, a, y) : Bool}) -> {pf.Has(info, a <> y <> more, a) == True{} : Bool}:
  %L.pf.node_eq_refl(a) : {Bool.or(Bool.and(_, O.mergeable(info, a, y)), pf.Has(info, y <> more, a)) == True{} : Bool}
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

def pf.snd_cons(-n: O.Node, r: List<&2, O.Node> & List<&2, O.Node>) -> {Pair.snd(List<&2, O.Node>, List<&2, O.Node>, r) == Pair.snd(List<&2, O.Node>, List<&2, O.Node>, O.fit.cons(n, r)) : List<&2, O.Node>}:
  (ms, out) = r
  {==}

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
      (pf.implies_true(O.Nat.is_pos(O.Node.lvl(O.Node.parent(x))), O.Info.built(info, O.Node.parent(x)), pf.merge_built(info, x, y, L.pf.and_r(O.Node.eq(x, a), O.mergeable(info, x, y), Equal.sym(Bool, True{}, Bool.and(O.Node.eq(x, a), O.mergeable(info, x, y)), e)))), sm)
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

def fit.pf.Inv(+s: O.St) -> Type:
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
  -> fit.pf.Inv(Pair.fst(O.St, List<&2, O.Node>, O.msg.after(merged, view, cfg, t, info, cv, ready, busy))):
  (s1, s2) = d
  (s1, pf.mcv(merged, cfg, t, info, view, cv, s2, sc))

def pf.batch_inv(r: List<&2, O.Node> & List<&2, O.Node>, +cfg: O.Cfg, +t: List<&2, Bool>, +info: O.Info, +cv: List<&2, O.Node>, +ready: List<&2, O.Node>, +busy: List<&2, O.Node>)
  -> S.Summarized(info, Pair.snd(List<&2, O.Node>, List<&2, O.Node>, r)) -> S.Summarized(info, cv) -> fit.pf.Inv(Pair.fst(O.St, List<&2, O.Node>, O.msg.batch(r, cfg, t, info, cv, ready, busy))):
  (merged, view0) = r
  +view = view0
  sv => sc => pf.batch.fin(merged, view, cfg, t, info, cv, ready, busy, pf.summ_dup(view, info, sv), sc)

def pf.msg_go_inv(grow: Bool, +cfg: O.Cfg, +t: List<&2, Bool>, +info: O.Info, +gv: List<&2, O.Node>, +gcv: List<&2, O.Node>, +ready: List<&2, O.Node>, +busy: List<&2, O.Node>,
  hv: S.Summarized(info, gv), hc: S.Summarized(info, gcv))
  -> fit.pf.Inv(Pair.fst(O.St, List<&2, O.Node>, O.msg.go(grow, cfg, t, info, gv, gcv, ready, busy))):
  match grow:
    case False{}:
      (hv, pf.fitc_summ(cfg, t, info, gcv, hc))
    case True{}:
      pf.batch_inv(O.fit(O.Last{}, t, O.Cfg.floor(cfg), O.Cfg.ph(cfg), info, gv), cfg, t, info, gcv, ready, busy)(pf.fit_summ(O.Last{}, t, O.Cfg.floor(cfg), O.Cfg.ph(cfg), info, gv, hv))(hc)

def pf.step_msg(+cfg: O.Cfg, +t: List<&2, Bool>, +info: O.Info, +view: List<&2, O.Node>, +shrink: Bool, +cview: List<&2, O.Node>, +ready: List<&2, O.Node>, +busy: List<&2, O.Node>,
  i: fit.pf.Inv(O.St{t, info, view, shrink, cview, ready, busy}))
  -> fit.pf.Inv(Pair.fst(O.St, List<&2, O.Node>, O.msg(cfg, O.St{t, info, view, shrink, cview, ready, busy}))):
  (hv, hc) = i
  pf.msg_go_inv(O.St.batch(cfg, O.St{t, info, view, shrink, cview, ready, busy}), cfg, O.Bits.inc(t), info, List.append(&2, O.Node, view, [O.Node.leaf(t)]), List.append(&2, O.Node, cview, [O.Node.leaf(t)]), ready, busy, pf.summ_app(view, info, t, hv), pf.summ_app(cview, info, t, hc))

def pf.step_build(+cfg: O.Cfg, +t: List<&2, Bool>, +info: O.Info, +view: List<&2, O.Node>, +shrink: Bool, +cview: List<&2, O.Node>, +ready: List<&2, O.Node>, +busy: List<&2, O.Node>, +n: O.Node, +size: Nat,
  i: fit.pf.Inv(O.St{t, info, view, shrink, cview, ready, busy}))
  -> fit.pf.Inv(O.build(cfg, O.St{t, info, view, shrink, cview, ready, busy}, n, size)):
  (hv, hc) = i
  (pf.summ_set(view, info, n, size, hv), pf.fitc_summ(cfg, t, O.Info.set(info, n, size), cview, pf.summ_set(cview, info, n, size, hc)))

def pf.step_inv(+cfg: O.Cfg, s: O.St, e: O.Ev) -> fit.pf.Inv(s) -> fit.pf.Inv(Pair.fst(O.St, List<&2, O.Node>, O.step(cfg, s, e))):
  match s e:
    case O.St{+t, +info, +view, +shrink, +cview, +ready, +busy} O.Msg{}:
      i => pf.step_msg(cfg, t, info, view, shrink, cview, ready, busy, i)
    case O.St{+t, +info, +view, +shrink, +cview, +ready, +busy} O.Build{+n, +size}:
      i => pf.step_build(cfg, t, info, view, shrink, cview, ready, busy, n, size, i)
    case O.St{+t, +info, +view, +shrink, +cview, +ready, +busy} O.Start{n}:
      i => i
    case O.St{+t, +info, +view, +shrink, +cview, +ready, +busy} O.Free{n}:
      i => i

def pf.run_inv(evs: List<&2, O.Ev>, +cfg: O.Cfg, +s: O.St, i: fit.pf.Inv(s)) -> fit.pf.Inv(O.run.go(evs, cfg, s)):
  match evs:
    case Nil{}:
      i
    case +e <> rest:
      pf.run_inv(rest, cfg, Pair.fst(O.St, List<&2, O.Node>, O.step(cfg, s, e)), pf.step_inv(cfg, s, e)(i))

def pf.run_summ(+cfg: O.Cfg, +evs: List<&2, O.Ev>) -> fit.pf.Inv(O.run(cfg, evs)):
  pf.run_inv(evs, cfg, O.St.empty(), (Unit{}, Unit{}))

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

def pa.cmp_nil(ys: List<&2, Bool>) -> {O.Cmp.of_zero(O.Bits.is_zero(ys), LT{}) == Nat.cmp(0n, O.Bits.val(ys)) : Cmp}:
  match ys:
    case Nil{}:
      {==}
    case h <> +t:
      match h:
        case True{}:
          {==}
        case False{}:
          Equal.trans(Cmp, O.Cmp.of_zero(O.Bits.is_zero(t), LT{}), Nat.cmp(0n, O.Bits.val(t)), Nat.cmp(0n, Nat.double(O.Bits.val(t))), pa.cmp_nil(t), Equal.sym(Cmp, Nat.cmp(0n, Nat.double(O.Bits.val(t))), Nat.cmp(0n, O.Bits.val(t)), pa.cmp0_dbl(O.Bits.val(t))))

def pa.cmp_nil_r(xs: List<&2, Bool>) -> {O.Cmp.of_zero(O.Bits.is_zero(xs), GT{}) == Nat.cmp(O.Bits.val(xs), 0n) : Cmp}:
  match xs:
    case Nil{}:
      {==}
    case h <> +t:
      match h:
        case True{}:
          {==}
        case False{}:
          Equal.trans(Cmp, O.Cmp.of_zero(O.Bits.is_zero(t), GT{}), Nat.cmp(O.Bits.val(t), 0n), Nat.cmp(Nat.double(O.Bits.val(t)), 0n), pa.cmp_nil_r(t), Equal.sym(Cmp, Nat.cmp(Nat.double(O.Bits.val(t)), 0n), Nat.cmp(O.Bits.val(t), 0n), pa.cmp_dbl0(O.Bits.val(t))))

# comparing two numbers by their higher bits, then the lowest
def pa.cmp_bit(A: Nat, B: Nat, x: Bool, y: Bool) -> {O.Cmp.then(Nat.cmp(A, B), Bool.cmp(x, y)) == Nat.cmp(O.bit(x, Nat.double(A)), O.bit(y, Nat.double(B))) : Cmp}:
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
def pa.cmp_val(xs: List<&2, Bool>, ys: List<&2, Bool>) -> {O.Bits.cmp(xs, ys) == Nat.cmp(O.Bits.val(xs), O.Bits.val(ys)) : Cmp}:
  match xs ys:
    case Nil{} ys:
      pa.cmp_nil(ys)
    case x <> xt Nil{}:
      pa.cmp_nil_r(x <> xt)
    case +x <> +xt +y <> +yt:
      Equal.trans(Cmp, O.Cmp.then(O.Bits.cmp(xt, yt), Bool.cmp(x, y)), O.Cmp.then(Nat.cmp(O.Bits.val(xt), O.Bits.val(yt)), Bool.cmp(x, y)), Nat.cmp(O.Bits.val(x <> xt), O.Bits.val(y <> yt)), Equal.cong(Cmp, Cmp, z => O.Cmp.then(z, Bool.cmp(x, y)), O.Bits.cmp(xt, yt), Nat.cmp(O.Bits.val(xt), O.Bits.val(yt)), pa.cmp_val(xt, yt)), pa.cmp_bit(O.Bits.val(xt), O.Bits.val(yt), x, y))
