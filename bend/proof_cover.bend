# proof_cover: the coverage laws of LAWS.bend (view_covers, cview_covers,
# message_appends, message_merges_nothing, merge_is_one_pair,
# merge_covers). A merge replaces a sibling pair by its parent, which
# covers the same messages; a fit is a chain of merges; a message appends
# the line of message T at T; so every event keeps both views tiling 0..T.

import Base
import ./optchat.bend as O
import ./spec.bend as S

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

def merge_covers(+info: O.Info, +s: Nat, +v: List<&2, O.Node>, +w: List<&2, O.Node>, +e: Nat, tiles: S.Tiles(s, v, e), merged: S.Merged(info, v, w)) -> S.Tiles(s, w, e):
  cover.merged(v, w, info, s, e, tiles, merged)

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

def cover.inv_cview(-s: O.St, inv: cover.Inv(s)) -> S.Tiles(0n, O.St.cview(s), O.Bits.val(O.St.t(s))):
  (a, b) = inv
  b

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

def cview_covers(+cfg: O.Cfg, +evs: List<&2, O.Ev>) -> S.Tiles(0n, S.cview.of(cfg, evs), S.total.of(cfg, evs)):
  cover.inv_cview(O.run(cfg, evs), cover.all(cfg, evs))

def message_appends(+cfg: O.Cfg, +s: O.St, quiet: {O.St.batch(cfg, s) == False{} : Bool}) -> {O.St.view(Pair.fst(O.St, List<&2, O.Node>, O.msg(cfg, s))) == List.append(&2, O.Node, O.St.view(s), [O.Node.leaf(O.St.t(s))]) : List<&2, O.Node>}:
  %Equal.sym(Bool, O.St.batch(cfg, s), False{}, quiet) : {O.St.view(Pair.fst(O.St, List<&2, O.Node>, O.msg.go(_, cfg, O.Bits.inc(O.St.t(s)), O.St.info(s), O.St.grown(s), List.append(&2, O.Node, O.St.cview(s), [O.Node.leaf(O.St.t(s))]), O.St.ready(s), O.St.busy(s)))) == List.append(&2, O.Node, O.St.view(s), [O.Node.leaf(O.St.t(s))]) : List<&2, O.Node>}
  {==}

def message_merges_nothing(+cfg: O.Cfg, +s: O.St, quiet: {O.St.batch(cfg, s) == False{} : Bool}) -> {Pair.snd(O.St, List<&2, O.Node>, O.msg(cfg, s)) == Nil{} : List<&2, O.Node>}:
  %Equal.sym(Bool, O.St.batch(cfg, s), False{}, quiet) : {Pair.snd(O.St, List<&2, O.Node>, O.msg.go(_, cfg, O.Bits.inc(O.St.t(s)), O.St.info(s), O.St.grown(s), List.append(&2, O.Node, O.St.cview(s), [O.Node.leaf(O.St.t(s))]), O.St.ready(s), O.St.busy(s))) == Nil{} : List<&2, O.Node>}
  {==}
