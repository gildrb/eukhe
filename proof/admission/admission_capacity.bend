# eukhe: the proof of LAW admission_capacity

import Base
import ../../bend/admission.bend as Ad
import ../../LAWS.bend as Laws
import ./base.bend as LA

def ad.add_one(n: Nat) -> {1n+n == Nat.add(n, 1n) : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      %ad.add_one(p) : {2n+p == 1n+_ : Nat}
      {==}

def ad.or_tl(x: Bool, -y: Bool, ex: {x == True{} : Bool}) -> {Bool.or(x, y) == True{} : Bool}:
  match x:
    case True{}:
      {==}
    case False{}:
      LA.ad.absurd({Bool.or(False{}, y) == True{} : Bool}, ex)

def ad.or_elim(w: Bool, -v: Bool, ih: {Bool.or(w, v) == True{} : Bool}, f: {v == True{} : Bool} -> {w == True{} : Bool}) -> {w == True{} : Bool}:
  match w:
    case True{}:
      {==}
    case False{}:
      f(ih)

def ad.pick_room(r: Bool, -wi: Nat, -hi: Nat, -wb: Nat, -c: Ad.Cls, e: {Ad.pick.go(r, wi, hi, wb) == Some{c} : Maybe<&2, Ad.Cls>}) -> {r == True{} : Bool}:
  match r:
    case True{}:
      {==}
    case False{}:
      %e : LA.ad.BD(Maybe.is_some(&2, Ad.Cls, _), {False{} == True{} : Bool}, Unit)
      Unit{}

def ad.within_room(l: Ad.Lim, -n: Nat, rm: {Ad.room(l, n) == True{} : Bool}) -> {Ad.within(l, 1n+n) == True{} : Bool}:
  match l:
    case Ad.Unl{}:
      {==}
    case Ad.Cap{p}:
      rm

def ad.within_of(l: Ad.Lim, +g: Nat, +m: Nat, lg: {Ad.le(g, 1n+m) == True{} : Bool}, rm: {Ad.room(l, m) == True{} : Bool}) -> {Ad.within(l, g) == True{} : Bool}:
  match l:
    case Ad.Unl{}:
      {==}
    case Ad.Cap{+p}:
      LA.ad.le_trans(g, 1n+m, 1n+p, lg, rm)

# a grant takes one more slot
def ad.held_mark(+t: List<&2, Ad.Tk>, c: Ad.Cls, +nz: {Ad.isz(Ad.cnt(Ad.Waiting{}, c, t)) == False{} : Bool}) -> {Ad.held(Ad.mark(c, t)) == 1n+Ad.held(t) : Nat}:
  match c:
    case Ad.Ia{}:
      +hi = Ad.cnt(Ad.Holding{}, Ad.Ia{}, t)
      +hb = Ad.cnt(Ad.Holding{}, Ad.Bg{}, t)
      +t2 = Ad.mark(Ad.Ia{}, t)
      %Equal.sym(Nat, Ad.cnt(Ad.Holding{}, Ad.Ia{}, t2), 1n+hi, LA.ad.cnt_mark(Ad.Holding{}, Ad.Ia{}, t, Ad.Ia{}, nz)) : {Nat.add(_, Ad.cnt(Ad.Holding{}, Ad.Bg{}, t2)) == 1n+Nat.add(hi, hb) : Nat}
      %Equal.sym(Nat, Ad.cnt(Ad.Holding{}, Ad.Bg{}, t2), hb, LA.ad.cnt_mark(Ad.Holding{}, Ad.Bg{}, t, Ad.Ia{}, nz)) : {Nat.add(1n+hi, _) == 1n+Nat.add(hi, hb) : Nat}
      {==}
    case Ad.Bg{}:
      +hi = Ad.cnt(Ad.Holding{}, Ad.Ia{}, t)
      +hb = Ad.cnt(Ad.Holding{}, Ad.Bg{}, t)
      +t2 = Ad.mark(Ad.Bg{}, t)
      %Equal.sym(Nat, Ad.cnt(Ad.Holding{}, Ad.Ia{}, t2), hi, LA.ad.cnt_mark(Ad.Holding{}, Ad.Ia{}, t, Ad.Bg{}, nz)) : {Nat.add(_, Ad.cnt(Ad.Holding{}, Ad.Bg{}, t2)) == 1n+Nat.add(hi, hb) : Nat}
      %Equal.sym(Nat, Ad.cnt(Ad.Holding{}, Ad.Bg{}, t2), 1n+hb, LA.ad.cnt_mark(Ad.Holding{}, Ad.Bg{}, t, Ad.Bg{}, nz)) : {Nat.add(hi, _) == 1n+Nat.add(hi, hb) : Nat}
      Equal.sym(Nat, 1n+Nat.add(hi, hb), Nat.add(hi, 1n+hb), LA.ad.add_succ(hi, hb))

def ad.nz_of(+l: Ad.Lim, +t: List<&2, Ad.Tk>, c: Ad.Cls, +ed: {Ad.pick(l, t) == Some{c} : Maybe<&2, Ad.Cls>}) -> {Ad.isz(Ad.cnt(Ad.Waiting{}, c, t)) == False{} : Bool}:
  match c:
    case Ad.Ia{}:
      LA.ad.pick_ia(Ad.room(l, Ad.held(t)), Ad.cnt(Ad.Waiting{}, Ad.Ia{}, t), Ad.cnt(Ad.Holding{}, Ad.Ia{}, t), Ad.cnt(Ad.Waiting{}, Ad.Bg{}, t), ed)
    case Ad.Bg{}:
      LA.ad.bg_wb(t, LA.ad.pbg(l, t, ed))

def ad.cap_tr(-w: Bool, -g: Nat, -a: Nat, -b: Nat, e: {a == b : Nat}, ih: {Bool.or(w, Ad.le(g, a)) == True{} : Bool}) -> {Bool.or(w, Ad.le(g, b)) == True{} : Bool}:
  %e : {Bool.or(w, Ad.le(g, _)) == True{} : Bool}
  ih

def ad.cap_stay(+l: Ad.Lim, +t: List<&2, Ad.Tk>) -> {Bool.or(Ad.within(l, Ad.held(t)), Ad.le(Ad.held(t), Ad.held(t))) == True{} : Bool}:
  %Equal.sym(Bool, Ad.le(Ad.held(t), Ad.held(t)), True{}, LA.ad.le_refl(Ad.held(t))) : {Bool.or(Ad.within(l, Ad.held(t)), _) == True{} : Bool}
  LA.ad.or_t(Ad.within(l, Ad.held(t)))

# grants happen only into free slots
def ad.cap_grant(+n: Nat, +d: Maybe<&2, Ad.Cls>, +l: Ad.Lim, +t: List<&2, Ad.Tk>, +ed: {Ad.pick(l, t) == d : Maybe<&2, Ad.Cls>}) -> {Bool.or(Ad.within(l, Ad.held(Ad.grant.go(n, d, l, t))), Ad.le(Ad.held(Ad.grant.go(n, d, l, t)), Ad.held(t))) == True{} : Bool}:
  match n d:
    case 0n _:
      ad.cap_stay(l, t)
    case 1n+f None{}:
      ad.cap_stay(l, t)
    case 1n+f Some{+c}:
      +t2 = Ad.mark(c, t)
      +g = Ad.held(Ad.grant.go(f, Ad.pick(l, t2), l, t2))
      +w = Ad.within(l, g)
      +rm = ad.pick_room(Ad.room(l, Ad.held(t)), Ad.cnt(Ad.Waiting{}, Ad.Ia{}, t), Ad.cnt(Ad.Holding{}, Ad.Ia{}, t), Ad.cnt(Ad.Waiting{}, Ad.Bg{}, t), c, ed)
      +ih = ad.cap_tr(w, g, Ad.held(t2), 1n+Ad.held(t), ad.held_mark(t, c, ad.nz_of(l, t, c, ed)), ad.cap_grant(f, Ad.pick(l, t2), l, t2, {==}))
      ad.or_tl(w, Ad.le(g, Ad.held(t)), ad.or_elim(w, Ad.le(g, 1n+Ad.held(t)), ih, lg => ad.within_of(l, g, Ad.held(t), lg, rm)))

# Collected, released, left
def ad.held_col(+ts: List<&2, Ad.Tk>, +k: Nat, +c: Ad.Cls, +e: {Ad.get(ts, k) == Some{Ad.Tk{c, Ad.Granted{}}} : Maybe<&2, Ad.Tk>}) -> {Ad.held(Ad.put(ts, k, Ad.Held{})) == Ad.held(ts) : Nat}:
  +t2 = Ad.put(ts, k, Ad.Held{})
  %Equal.sym(Nat, Ad.cnt(Ad.Holding{}, Ad.Ia{}, t2), Ad.cnt(Ad.Holding{}, Ad.Ia{}, ts), LA.ad.col_cnt(Ad.Holding{}, Ad.Ia{}, ts, k, c, e)) : {Nat.add(_, Ad.cnt(Ad.Holding{}, Ad.Bg{}, t2)) == Ad.held(ts) : Nat}
  %Equal.sym(Nat, Ad.cnt(Ad.Holding{}, Ad.Bg{}, t2), Ad.cnt(Ad.Holding{}, Ad.Bg{}, ts), LA.ad.col_cnt(Ad.Holding{}, Ad.Bg{}, ts, k, c, e)) : {Nat.add(Ad.cnt(Ad.Holding{}, Ad.Ia{}, ts), _) == Ad.held(ts) : Nat}
  {==}

# a ticket that holds no slot ends
def ad.held_same(+ts: List<&2, Ad.Tk>, +k: Nat, +c: Ad.Cls, s: Ad.Sts, +e: {Ad.get(ts, k) == Some{Ad.Tk{c, s}} : Maybe<&2, Ad.Tk>}, hs: {Ad.Mode.of(Ad.Holding{}, s) == False{} : Bool}) -> {Ad.held(Ad.put(ts, k, Ad.Ended{})) == Ad.held(ts) : Nat}:
  match s:
    case Ad.Queued{}:
      %LA.ad.end_cnt(Ad.Holding{}, Ad.Ia{}, ts, k, c, Ad.Queued{}, e) : {Nat.add(Ad.cnt(Ad.Holding{}, Ad.Ia{}, Ad.put(ts, k, Ad.Ended{})), Ad.cnt(Ad.Holding{}, Ad.Bg{}, Ad.put(ts, k, Ad.Ended{}))) == Nat.add(_, Ad.cnt(Ad.Holding{}, Ad.Bg{}, ts)) : Nat}
      %LA.ad.end_cnt(Ad.Holding{}, Ad.Bg{}, ts, k, c, Ad.Queued{}, e) : {Nat.add(Ad.cnt(Ad.Holding{}, Ad.Ia{}, Ad.put(ts, k, Ad.Ended{})), Ad.cnt(Ad.Holding{}, Ad.Bg{}, Ad.put(ts, k, Ad.Ended{}))) == Nat.add(Ad.cnt(Ad.Holding{}, Ad.Ia{}, Ad.put(ts, k, Ad.Ended{})), _) : Nat}
      {==}
    case Ad.Granted{}:
      LA.ad.absurd({Ad.held(Ad.put(ts, k, Ad.Ended{})) == Ad.held(ts) : Nat}, Equal.sym(Bool, True{}, False{}, hs))
    case Ad.Held{}:
      LA.ad.absurd({Ad.held(Ad.put(ts, k, Ad.Ended{})) == Ad.held(ts) : Nat}, Equal.sym(Bool, True{}, False{}, hs))
    case Ad.Preempted{}:
      %LA.ad.end_cnt(Ad.Holding{}, Ad.Ia{}, ts, k, c, Ad.Preempted{}, e) : {Nat.add(Ad.cnt(Ad.Holding{}, Ad.Ia{}, Ad.put(ts, k, Ad.Ended{})), Ad.cnt(Ad.Holding{}, Ad.Bg{}, Ad.put(ts, k, Ad.Ended{}))) == Nat.add(_, Ad.cnt(Ad.Holding{}, Ad.Bg{}, ts)) : Nat}
      %LA.ad.end_cnt(Ad.Holding{}, Ad.Bg{}, ts, k, c, Ad.Preempted{}, e) : {Nat.add(Ad.cnt(Ad.Holding{}, Ad.Ia{}, Ad.put(ts, k, Ad.Ended{})), Ad.cnt(Ad.Holding{}, Ad.Bg{}, Ad.put(ts, k, Ad.Ended{}))) == Nat.add(Ad.cnt(Ad.Holding{}, Ad.Ia{}, Ad.put(ts, k, Ad.Ended{})), _) : Nat}
      {==}
    case Ad.Ended{}:
      %LA.ad.end_cnt(Ad.Holding{}, Ad.Ia{}, ts, k, c, Ad.Ended{}, e) : {Nat.add(Ad.cnt(Ad.Holding{}, Ad.Ia{}, Ad.put(ts, k, Ad.Ended{})), Ad.cnt(Ad.Holding{}, Ad.Bg{}, Ad.put(ts, k, Ad.Ended{}))) == Nat.add(_, Ad.cnt(Ad.Holding{}, Ad.Bg{}, ts)) : Nat}
      %LA.ad.end_cnt(Ad.Holding{}, Ad.Bg{}, ts, k, c, Ad.Ended{}, e) : {Nat.add(Ad.cnt(Ad.Holding{}, Ad.Ia{}, Ad.put(ts, k, Ad.Ended{})), Ad.cnt(Ad.Holding{}, Ad.Bg{}, Ad.put(ts, k, Ad.Ended{}))) == Nat.add(Ad.cnt(Ad.Holding{}, Ad.Ia{}, Ad.put(ts, k, Ad.Ended{})), _) : Nat}
      {==}

# a ticket that holds a slot ends: one slot frees
def ad.held_end(+ts: List<&2, Ad.Tk>, +k: Nat, c: Ad.Cls, s: Ad.Sts, +e: {Ad.get(ts, k) == Some{Ad.Tk{c, s}} : Maybe<&2, Ad.Tk>}, hs: {Ad.Mode.of(Ad.Holding{}, s) == True{} : Bool}) -> {1n+Ad.held(Ad.put(ts, k, Ad.Ended{})) == Ad.held(ts) : Nat}:
  match c s:
    case Ad.Ia{} Ad.Granted{}:
      %LA.ad.end_cnt(Ad.Holding{}, Ad.Ia{}, ts, k, Ad.Ia{}, Ad.Granted{}, e) : {1n+Nat.add(Ad.cnt(Ad.Holding{}, Ad.Ia{}, Ad.put(ts, k, Ad.Ended{})), Ad.cnt(Ad.Holding{}, Ad.Bg{}, Ad.put(ts, k, Ad.Ended{}))) == Nat.add(_, Ad.cnt(Ad.Holding{}, Ad.Bg{}, ts)) : Nat}
      %LA.ad.end_cnt(Ad.Holding{}, Ad.Bg{}, ts, k, Ad.Ia{}, Ad.Granted{}, e) : {1n+Nat.add(Ad.cnt(Ad.Holding{}, Ad.Ia{}, Ad.put(ts, k, Ad.Ended{})), Ad.cnt(Ad.Holding{}, Ad.Bg{}, Ad.put(ts, k, Ad.Ended{}))) == Nat.add(1n+Ad.cnt(Ad.Holding{}, Ad.Ia{}, Ad.put(ts, k, Ad.Ended{})), _) : Nat}
      {==}
    case Ad.Ia{} Ad.Held{}:
      %LA.ad.end_cnt(Ad.Holding{}, Ad.Ia{}, ts, k, Ad.Ia{}, Ad.Held{}, e) : {1n+Nat.add(Ad.cnt(Ad.Holding{}, Ad.Ia{}, Ad.put(ts, k, Ad.Ended{})), Ad.cnt(Ad.Holding{}, Ad.Bg{}, Ad.put(ts, k, Ad.Ended{}))) == Nat.add(_, Ad.cnt(Ad.Holding{}, Ad.Bg{}, ts)) : Nat}
      %LA.ad.end_cnt(Ad.Holding{}, Ad.Bg{}, ts, k, Ad.Ia{}, Ad.Held{}, e) : {1n+Nat.add(Ad.cnt(Ad.Holding{}, Ad.Ia{}, Ad.put(ts, k, Ad.Ended{})), Ad.cnt(Ad.Holding{}, Ad.Bg{}, Ad.put(ts, k, Ad.Ended{}))) == Nat.add(1n+Ad.cnt(Ad.Holding{}, Ad.Ia{}, Ad.put(ts, k, Ad.Ended{})), _) : Nat}
      {==}
    case Ad.Bg{} Ad.Granted{}:
      %LA.ad.end_cnt(Ad.Holding{}, Ad.Ia{}, ts, k, Ad.Bg{}, Ad.Granted{}, e) : {1n+Nat.add(Ad.cnt(Ad.Holding{}, Ad.Ia{}, Ad.put(ts, k, Ad.Ended{})), Ad.cnt(Ad.Holding{}, Ad.Bg{}, Ad.put(ts, k, Ad.Ended{}))) == Nat.add(_, Ad.cnt(Ad.Holding{}, Ad.Bg{}, ts)) : Nat}
      %LA.ad.end_cnt(Ad.Holding{}, Ad.Bg{}, ts, k, Ad.Bg{}, Ad.Granted{}, e) : {1n+Nat.add(Ad.cnt(Ad.Holding{}, Ad.Ia{}, Ad.put(ts, k, Ad.Ended{})), Ad.cnt(Ad.Holding{}, Ad.Bg{}, Ad.put(ts, k, Ad.Ended{}))) == Nat.add(Ad.cnt(Ad.Holding{}, Ad.Ia{}, Ad.put(ts, k, Ad.Ended{})), _) : Nat}
      LA.ad.add_succ(Ad.cnt(Ad.Holding{}, Ad.Ia{}, Ad.put(ts, k, Ad.Ended{})), Ad.cnt(Ad.Holding{}, Ad.Bg{}, Ad.put(ts, k, Ad.Ended{})))
    case Ad.Bg{} Ad.Held{}:
      %LA.ad.end_cnt(Ad.Holding{}, Ad.Ia{}, ts, k, Ad.Bg{}, Ad.Held{}, e) : {1n+Nat.add(Ad.cnt(Ad.Holding{}, Ad.Ia{}, Ad.put(ts, k, Ad.Ended{})), Ad.cnt(Ad.Holding{}, Ad.Bg{}, Ad.put(ts, k, Ad.Ended{}))) == Nat.add(_, Ad.cnt(Ad.Holding{}, Ad.Bg{}, ts)) : Nat}
      %LA.ad.end_cnt(Ad.Holding{}, Ad.Bg{}, ts, k, Ad.Bg{}, Ad.Held{}, e) : {1n+Nat.add(Ad.cnt(Ad.Holding{}, Ad.Ia{}, Ad.put(ts, k, Ad.Ended{})), Ad.cnt(Ad.Holding{}, Ad.Bg{}, Ad.put(ts, k, Ad.Ended{}))) == Nat.add(Ad.cnt(Ad.Holding{}, Ad.Ia{}, Ad.put(ts, k, Ad.Ended{})), _) : Nat}
      LA.ad.add_succ(Ad.cnt(Ad.Holding{}, Ad.Ia{}, Ad.put(ts, k, Ad.Ended{})), Ad.cnt(Ad.Holding{}, Ad.Bg{}, Ad.put(ts, k, Ad.Ended{})))
    case _ Ad.Queued{}:
      LA.ad.absurd({1n+Ad.held(Ad.put(ts, k, Ad.Ended{})) == Ad.held(ts) : Nat}, hs)
    case _ Ad.Preempted{}:
      LA.ad.absurd({1n+Ad.held(Ad.put(ts, k, Ad.Ended{})) == Ad.held(ts) : Nat}, hs)
    case _ Ad.Ended{}:
      LA.ad.absurd({1n+Ad.held(Ad.put(ts, k, Ad.Ended{})) == Ad.held(ts) : Nat}, hs)

def ad.cap_id(+l: Ad.Lim, +n: Nat) -> {Bool.or(Ad.within(l, n), Ad.le(Nat.add(n, 0n), n)) == True{} : Bool}:
  %Equal.sym(Nat, Nat.add(n, 0n), n, LA.ad.add_zero(n)) : {Bool.or(Ad.within(l, n), Ad.le(_, n)) == True{} : Bool}
  %Equal.sym(Bool, Ad.le(n, n), True{}, LA.ad.le_refl(n)) : {Bool.or(Ad.within(l, n), _) == True{} : Bool}
  LA.ad.or_t(Ad.within(l, n))

def ad.cap_add(-w: Bool, +g: Nat, +h: Nat, f: Nat, ih: {Bool.or(w, Ad.le(g, h)) == True{} : Bool}) -> {Bool.or(w, Ad.le(Nat.add(g, f), Nat.add(h, f))) == True{} : Bool}:
  match f:
    case 0n:
      %Equal.sym(Nat, Nat.add(g, 0n), g, LA.ad.add_zero(g)) : {Bool.or(w, Ad.le(_, Nat.add(h, 0n))) == True{} : Bool}
      %Equal.sym(Nat, Nat.add(h, 0n), h, LA.ad.add_zero(h)) : {Bool.or(w, Ad.le(g, _)) == True{} : Bool}
      ih
    case 1n+p:
      %LA.ad.add_succ(g, p) : {Bool.or(w, Ad.le(_, Nat.add(h, 1n+p))) == True{} : Bool}
      %LA.ad.add_succ(h, p) : {Bool.or(w, Ad.le(1n+Nat.add(g, p), _)) == True{} : Bool}
      ad.cap_add(w, g, h, p, ih)

# a grant after an op that freed f slots
def ad.cap_after(+l: Ad.Lim, +t2: List<&2, Ad.Tk>, +ts: List<&2, Ad.Tk>, +f: Nat, e: {Nat.add(Ad.held(t2), f) == Ad.held(ts) : Nat}) -> {Bool.or(Ad.within(l, Ad.held(Ad.grant(l, t2))), Ad.le(Nat.add(Ad.held(Ad.grant(l, t2)), f), Ad.held(ts))) == True{} : Bool}:
  +g = Ad.held(Ad.grant(l, t2))
  %e : {Bool.or(Ad.within(l, g), Ad.le(Nat.add(g, f), _)) == True{} : Bool}
  ad.cap_add(Ad.within(l, g), g, Ad.held(t2), f, ad.cap_grant(Ad.waits(t2), Ad.pick(l, t2), l, t2, {==}))

def ad.cap_keep(+l: Ad.Lim, +hi: Nat, +hb: Nat) -> {Bool.or(Ad.within(l, Nat.add(hi, 0n)), Ad.le(Nat.add(Nat.add(hi, 0n), hb), Nat.add(hi, hb))) == True{} : Bool}:
  %Equal.sym(Nat, Nat.add(hi, 0n), hi, LA.ad.add_zero(hi)) : {Bool.or(Ad.within(l, _), Ad.le(Nat.add(_, hb), Nat.add(hi, hb))) == True{} : Bool}
  %Equal.sym(Bool, Ad.le(Nat.add(hi, hb), Nat.add(hi, hb)), True{}, LA.ad.le_refl(Nat.add(hi, hb))) : {Bool.or(Ad.within(l, hi), _) == True{} : Bool}
  LA.ad.or_t(Ad.within(l, hi))

def ad.room_z(-l: Ad.Lim, +hi: Nat, er: {Ad.room(l, hi) == True{} : Bool}) -> {Ad.room(l, Nat.add(hi, 0n)) == True{} : Bool}:
  %Equal.sym(Nat, Nat.add(hi, 0n), hi, LA.ad.add_zero(hi)) : {Ad.room(l, _) == True{} : Bool}
  er

def ad.cap_ia0(+l: Ad.Lim, +hi: Nat, +hb: Nat, r: Bool, u: Bool, er: {Ad.room(l, hi) == r : Bool}) -> {Bool.or(Ad.within(l, Nat.add(Ad.bit(Ad.hit(Ad.Holding{}, Ad.Ia{}, Ad.Tk{Ad.Ia{}, Ad.admit.ia.st(r, u)}), hi), 0n)), Ad.le(Nat.add(Nat.add(Ad.bit(Ad.hit(Ad.Holding{}, Ad.Ia{}, Ad.Tk{Ad.Ia{}, Ad.admit.ia.st(r, u)}), hi), 0n), hb), Nat.add(hi, hb))) == True{} : Bool}:
  match r u:
    case True{} _:
      ad.or_tl(Ad.within(l, 1n+Nat.add(hi, 0n)), Ad.le(1n+Nat.add(Nat.add(hi, 0n), hb), Nat.add(hi, hb)), ad.within_room(l, Nat.add(hi, 0n), ad.room_z(l, hi, er)))
    case False{} True{}:
      ad.cap_keep(l, hi, hb)
    case False{} False{}:
      ad.cap_keep(l, hi, hb)

def ad.cap_ia1(+l: Ad.Lim, +hi: Nat, +hb: Nat, u: Bool) -> {Bool.or(Ad.within(l, Nat.add(Ad.bit(Ad.hit(Ad.Holding{}, Ad.Ia{}, Ad.Tk{Ad.Ia{}, Ad.admit.ia.st(False{}, u)}), hi), 0n)), Ad.le(Nat.add(Nat.add(Ad.bit(Ad.hit(Ad.Holding{}, Ad.Ia{}, Ad.Tk{Ad.Ia{}, Ad.admit.ia.st(False{}, u)}), hi), 0n), hb), Nat.add(hi, hb))) == True{} : Bool}:
  match u:
    case True{}:
      ad.cap_keep(l, hi, hb)
    case False{}:
      ad.cap_keep(l, hi, hb)

def ad.cap_ia(+l: Ad.Lim, +q: Nat, wi: Nat, +hi: Nat, +hb: Nat) -> {Bool.or(Ad.within(l, Nat.add(Ad.bit(Ad.hit(Ad.Holding{}, Ad.Ia{}, Ad.Tk{Ad.Ia{}, Ad.admit.ia.st(Bool.and(Ad.isz(wi), Ad.room(l, hi)), Ad.le(q, wi))}), hi), 0n)), Ad.le(Nat.add(Nat.add(Ad.bit(Ad.hit(Ad.Holding{}, Ad.Ia{}, Ad.Tk{Ad.Ia{}, Ad.admit.ia.st(Bool.and(Ad.isz(wi), Ad.room(l, hi)), Ad.le(q, wi))}), hi), 0n), hb), Nat.add(hi, hb))) == True{} : Bool}:
  match wi:
    case 0n:
      ad.cap_ia0(l, hi, hb, Ad.room(l, hi), Ad.le(q, 0n), {==})
    case 1n+w:
      ad.cap_ia1(l, hi, hb, Ad.le(q, 1n+w))

def ad.cap_bg0(+l: Ad.Lim, +hb: Nat, r: Bool, er: {Ad.room(l, hb) == r : Bool}) -> {Bool.or(Ad.within(l, Ad.bit(Ad.hit(Ad.Holding{}, Ad.Bg{}, Ad.Tk{Ad.Bg{}, Ad.admit.bg.st(r)}), hb)), Ad.le(Nat.add(Ad.bit(Ad.hit(Ad.Holding{}, Ad.Bg{}, Ad.Tk{Ad.Bg{}, Ad.admit.bg.st(r)}), hb), 0n), hb)) == True{} : Bool}:
  match r:
    case True{}:
      ad.or_tl(Ad.within(l, 1n+hb), Ad.le(1n+Nat.add(hb, 0n), hb), ad.within_room(l, hb, er))
    case False{}:
      ad.cap_id(l, hb)

def ad.cap_bg(+l: Ad.Lim, hi: Nat, wi: Nat, wb: Nat, +hb: Nat) -> {Bool.or(Ad.within(l, Nat.add(hi, Ad.bit(Ad.hit(Ad.Holding{}, Ad.Bg{}, Ad.Tk{Ad.Bg{}, Ad.admit.bg.st(Bool.and(Ad.isz(hi), Bool.and(Ad.isz(wi), Bool.and(Ad.isz(wb), Ad.room(l, Nat.add(hi, hb))))))}), hb))), Ad.le(Nat.add(Nat.add(hi, Ad.bit(Ad.hit(Ad.Holding{}, Ad.Bg{}, Ad.Tk{Ad.Bg{}, Ad.admit.bg.st(Bool.and(Ad.isz(hi), Bool.and(Ad.isz(wi), Bool.and(Ad.isz(wb), Ad.room(l, Nat.add(hi, hb))))))}), hb)), 0n), Nat.add(hi, hb))) == True{} : Bool}:
  match hi:
    case 1n+a:
      ad.cap_id(l, Nat.add(1n+a, hb))
    case 0n:
      match wi:
        case 1n+b:
          ad.cap_id(l, hb)
        case 0n:
          match wb:
            case 1n+c:
              ad.cap_id(l, hb)
            case 0n:
              ad.cap_bg0(l, hb, Ad.room(l, hb), {==})

def ad.cap_col(mb: Maybe<&2, Ad.Tk>, +l: Ad.Lim, +q: Nat, +ts: List<&2, Ad.Tk>, +k: Nat, e: {Ad.get(ts, k) == mb : Maybe<&2, Ad.Tk>}) -> {Bool.or(Ad.within(Ad.St.lim(Ad.collect.at(mb, l, q, ts, k)), Ad.held(Ad.St.ts(Ad.collect.at(mb, l, q, ts, k)))), Ad.le(Nat.add(Ad.held(Ad.St.ts(Ad.collect.at(mb, l, q, ts, k))), 0n), Ad.held(ts))) == True{} : Bool}:
  match mb:
    case None{}:
      ad.cap_id(l, Ad.held(ts))
    case Some{Ad.Tk{c, Ad.Queued{}}}:
      ad.cap_id(l, Ad.held(ts))
    case Some{Ad.Tk{+c, Ad.Granted{}}}:
      +t2 = Ad.put(ts, k, Ad.Held{})
      %Equal.sym(Nat, Ad.held(t2), Ad.held(ts), ad.held_col(ts, k, c, e)) : {Bool.or(Ad.within(l, _), Ad.le(Nat.add(_, 0n), Ad.held(ts))) == True{} : Bool}
      ad.cap_id(l, Ad.held(ts))
    case Some{Ad.Tk{c, Ad.Held{}}}:
      ad.cap_id(l, Ad.held(ts))
    case Some{Ad.Tk{c, Ad.Preempted{}}}:
      ad.cap_id(l, Ad.held(ts))
    case Some{Ad.Tk{c, Ad.Ended{}}}:
      ad.cap_id(l, Ad.held(ts))

def ad.cap_rel(mb: Maybe<&2, Ad.Tk>, +l: Ad.Lim, +q: Nat, +ts: List<&2, Ad.Tk>, +k: Nat, e: {Ad.get(ts, k) == mb : Maybe<&2, Ad.Tk>}) -> {Bool.or(Ad.within(Ad.St.lim(Ad.release.at(mb, l, q, ts, k)), Ad.held(Ad.St.ts(Ad.release.at(mb, l, q, ts, k)))), Ad.le(Nat.add(Ad.held(Ad.St.ts(Ad.release.at(mb, l, q, ts, k))), Ad.freed.at(mb, True{})), Ad.held(ts))) == True{} : Bool}:
  match mb:
    case None{}:
      ad.cap_id(l, Ad.held(ts))
    case Some{Ad.Tk{c, Ad.Queued{}}}:
      ad.cap_id(l, Ad.held(ts))
    case Some{Ad.Tk{c, Ad.Granted{}}}:
      ad.cap_id(l, Ad.held(ts))
    case Some{Ad.Tk{+c, Ad.Held{}}}:
      +t2 = Ad.put(ts, k, Ad.Ended{})
      ad.cap_after(l, t2, ts, 1n, Equal.trans(Nat, Nat.add(Ad.held(t2), 1n), 1n+Ad.held(t2), Ad.held(ts), Equal.sym(Nat, 1n+Ad.held(t2), Nat.add(Ad.held(t2), 1n), ad.add_one(Ad.held(t2))), ad.held_end(ts, k, c, Ad.Held{}, e, {==})))
    case Some{Ad.Tk{+c, Ad.Preempted{}}}:
      +t2 = Ad.put(ts, k, Ad.Ended{})
      %Equal.sym(Nat, Ad.held(t2), Ad.held(ts), ad.held_same(ts, k, c, Ad.Preempted{}, e, {==})) : {Bool.or(Ad.within(l, _), Ad.le(Nat.add(_, 0n), Ad.held(ts))) == True{} : Bool}
      ad.cap_id(l, Ad.held(ts))
    case Some{Ad.Tk{c, Ad.Ended{}}}:
      ad.cap_id(l, Ad.held(ts))

def ad.cap_lea(mb: Maybe<&2, Ad.Tk>, +l: Ad.Lim, +q: Nat, +ts: List<&2, Ad.Tk>, +k: Nat, e: {Ad.get(ts, k) == mb : Maybe<&2, Ad.Tk>}) -> {Bool.or(Ad.within(Ad.St.lim(Ad.leave.at(mb, l, q, ts, k)), Ad.held(Ad.St.ts(Ad.leave.at(mb, l, q, ts, k)))), Ad.le(Nat.add(Ad.held(Ad.St.ts(Ad.leave.at(mb, l, q, ts, k))), Ad.freed.at(mb, False{})), Ad.held(ts))) == True{} : Bool}:
  match mb:
    case None{}:
      ad.cap_id(l, Ad.held(ts))
    case Some{Ad.Tk{+c, Ad.Queued{}}}:
      +t2 = Ad.put(ts, k, Ad.Ended{})
      ad.cap_after(l, t2, ts, 0n, Equal.trans(Nat, Nat.add(Ad.held(t2), 0n), Ad.held(t2), Ad.held(ts), LA.ad.add_zero(Ad.held(t2)), ad.held_same(ts, k, c, Ad.Queued{}, e, {==})))
    case Some{Ad.Tk{+c, Ad.Granted{}}}:
      +t2 = Ad.put(ts, k, Ad.Ended{})
      ad.cap_after(l, t2, ts, 1n, Equal.trans(Nat, Nat.add(Ad.held(t2), 1n), 1n+Ad.held(t2), Ad.held(ts), Equal.sym(Nat, 1n+Ad.held(t2), Nat.add(Ad.held(t2), 1n), ad.add_one(Ad.held(t2))), ad.held_end(ts, k, c, Ad.Granted{}, e, {==})))
    case Some{Ad.Tk{c, Ad.Held{}}}:
      ad.cap_id(l, Ad.held(ts))
    case Some{Ad.Tk{c, Ad.Preempted{}}}:
      ad.cap_id(l, Ad.held(ts))
    case Some{Ad.Tk{c, Ad.Ended{}}}:
      ad.cap_id(l, Ad.held(ts))

def capacity(s: Ad.St, o: Ad.Op) -> {Bool.or(Ad.within(Ad.St.lim(Ad.step(s, o)), Ad.held(Ad.St.ts(Ad.step(s, o)))), Ad.le(Nat.add(Ad.held(Ad.St.ts(Ad.step(s, o))), Ad.freed(s, o)), Ad.held(Ad.St.ts(s)))) == True{} : Bool}:
  match s:
    case Ad.St{+l, +q, +ts}:
      match o:
        case Ad.Admit{Ad.Ia{}}:
          +hi = Ad.cnt(Ad.Holding{}, Ad.Ia{}, ts)
          +wi = Ad.cnt(Ad.Waiting{}, Ad.Ia{}, ts)
          +hb = Ad.cnt(Ad.Holding{}, Ad.Bg{}, ts)
          +st = Ad.admit.ia.st(Bool.and(Ad.isz(wi), Ad.room(l, hi)), Ad.le(q, wi))
          +x = {Ad.Tk{Ad.Ia{}, st} : Ad.Tk}
          +t1 = Ad.preempt(ts)
          +t2 = List.append(&2, Ad.Tk, t1, [x])
          +b = Ad.bit(Ad.hit(Ad.Holding{}, Ad.Ia{}, x), hi)
          %Equal.sym(Nat, Ad.cnt(Ad.Holding{}, Ad.Ia{}, t2), b, LA.ad.app_pre(Ad.Holding{}, ts, x)) : {Bool.or(Ad.within(l, Nat.add(_, Ad.cnt(Ad.Holding{}, Ad.Bg{}, t2))), Ad.le(Nat.add(Nat.add(_, Ad.cnt(Ad.Holding{}, Ad.Bg{}, t2)), hb), Nat.add(hi, hb))) == True{} : Bool}
          %Equal.sym(Nat, Ad.cnt(Ad.Holding{}, Ad.Bg{}, t2), 0n, Equal.trans(Nat, Ad.cnt(Ad.Holding{}, Ad.Bg{}, t2), Ad.cnt(Ad.Holding{}, Ad.Bg{}, t1), 0n, LA.ad.app_off(Ad.Holding{}, Ad.Bg{}, t1, x, LA.ad.and_f(Ad.Mode.of(Ad.Holding{}, st))), LA.ad.pre_hb(ts))) : {Bool.or(Ad.within(l, Nat.add(b, _)), Ad.le(Nat.add(Nat.add(b, _), hb), Nat.add(hi, hb))) == True{} : Bool}
          ad.cap_ia(l, q, wi, hi, hb)
        case Ad.Admit{Ad.Bg{}}:
          +hi = Ad.cnt(Ad.Holding{}, Ad.Ia{}, ts)
          +wi = Ad.cnt(Ad.Waiting{}, Ad.Ia{}, ts)
          +hb = Ad.cnt(Ad.Holding{}, Ad.Bg{}, ts)
          +wb = Ad.cnt(Ad.Waiting{}, Ad.Bg{}, ts)
          +st = Ad.admit.bg.st(Bool.and(Ad.isz(hi), Bool.and(Ad.isz(wi), Bool.and(Ad.isz(wb), Ad.room(l, Nat.add(hi, hb))))))
          +y = {Ad.Tk{Ad.Bg{}, st} : Ad.Tk}
          +t2 = List.append(&2, Ad.Tk, ts, [y])
          +b = Ad.bit(Ad.hit(Ad.Holding{}, Ad.Bg{}, y), hb)
          %Equal.sym(Nat, Ad.cnt(Ad.Holding{}, Ad.Ia{}, t2), hi, LA.ad.app_off(Ad.Holding{}, Ad.Ia{}, ts, y, LA.ad.and_f(Ad.Mode.of(Ad.Holding{}, st)))) : {Bool.or(Ad.within(l, Nat.add(_, Ad.cnt(Ad.Holding{}, Ad.Bg{}, t2))), Ad.le(Nat.add(Nat.add(_, Ad.cnt(Ad.Holding{}, Ad.Bg{}, t2)), 0n), Nat.add(hi, hb))) == True{} : Bool}
          %Equal.sym(Nat, Ad.cnt(Ad.Holding{}, Ad.Bg{}, t2), b, LA.ad.cnt_app(Ad.Holding{}, Ad.Bg{}, ts, y)) : {Bool.or(Ad.within(l, Nat.add(hi, _)), Ad.le(Nat.add(Nat.add(hi, _), 0n), Nat.add(hi, hb))) == True{} : Bool}
          ad.cap_bg(l, hi, wi, wb, hb)
        case Ad.Collect{+k}:
          ad.cap_col(Ad.get(ts, k), l, q, ts, k, {==})
        case Ad.Release{+k}:
          ad.cap_rel(Ad.get(ts, k), l, q, ts, k, {==})
        case Ad.Leave{+k}:
          ad.cap_lea(Ad.get(ts, k), l, q, ts, k, {==})
        case Ad.Limit{+l2, q2}:
          ad.cap_after(l2, ts, ts, 0n, LA.ad.add_zero(Ad.held(ts)))

def Laws.admission_capacity(s, o):
  capacity(s, o)
