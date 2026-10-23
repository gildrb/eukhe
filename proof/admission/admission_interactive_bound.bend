# eukhe: the proof of LAW admission_interactive_bound

import Base
import ../../bend/admission.bend as Ad
import ../../LAWS.bend as Laws
import ./base.bend as LA

def aw.le0(a: Nat, e: {Ad.le(a, 0n) == True{} : Bool}) -> {a == 0n : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+x:
      LA.ad.absurd({1n+x == 0n : Nat}, e)

def aw.le_add_l(f: Nat, -x: Nat, -y: Nat, e: {Ad.le(x, y) == True{} : Bool}) -> {Ad.le(Nat.add(f, x), Nat.add(f, y)) == True{} : Bool}:
  match f:
    case 0n:
      e
    case 1n+p:
      aw.le_add_l(p, x, y, e)

# the interactive slots held are part of it
def aw.held_pot(t: List<&2, Ad.Tk>, +w: Nat) -> {Ad.le(Ad.cnt(Ad.Holding{}, Ad.Ia{}, t), Ad.pot(t, w)) == True{} : Bool}:
  match t w:
    case Nil{} _:
      {==}
    case +h <> +r 0n:
      LA.ad.le_refl(Ad.cnt(Ad.Holding{}, Ad.Ia{}, h <> r))
    case +h <> +r 1n+p:
      +hh = Ad.hit(Ad.Holding{}, Ad.Ia{}, h)
      +hw = Ad.hit(Ad.Waiting{}, Ad.Ia{}, h)
      LA.ad.le_trans(Ad.bit(hh, Ad.cnt(Ad.Holding{}, Ad.Ia{}, r)), Ad.bit(hh, Ad.pot(r, p)), Ad.bit(Bool.or(hh, hw), Ad.pot(r, p)), LA.aw.bit_mono(hh, Ad.cnt(Ad.Holding{}, Ad.Ia{}, r), Ad.pot(r, p), aw.held_pot(r, p)), LA.aw.bit_or(hh, hw, Ad.pot(r, p)))

def aw.room_t(l: Ad.Lim) -> {Ad.room(l, 0n) == True{} : Bool}:
  match l:
    case Ad.Unl{}:
      {==}
    case Ad.Cap{p}:
      {==}

def aw.room00(-l: Ad.Lim, -hi: Nat, -hb: Nat, zh: {hi == 0n : Nat}, zb: {hb == 0n : Nat}, rf: {Ad.room(l, Nat.add(hi, hb)) == False{} : Bool}) -> {Ad.room(l, 0n) == False{} : Bool}:
  %zh : {Ad.room(l, Nat.add(_, 0n)) == False{} : Bool}
  %zb : {Ad.room(l, Nat.add(hi, _)) == False{} : Bool}
  rf

# with no interactive slot held, an interactive waiter would have a
# free slot
def aw.no_idle(-X: Type, +l: Ad.Lim, +hi: Nat, +wi: Nat, +hb: Nat, +wb: Nat, zh: {hi == 0n : Nat}, nz: {Ad.isz(wi) == False{} : Bool}, +h: {LA.ad.ok.n(l, hi, wi, hb, wb) == True{} : Bool}) -> X:
  match wi:
    case 0n:
      LA.ad.absurd_t(X, nz)
    case 1n+w:
      +cn = Ad.calm.n(hi, 1n+w, hb)
      +zb = LA.ad.calm_hb0(hi, w, hb, LA.ad.and_r(Bool.not(Maybe.is_some(&2, Ad.Cls, Ad.pick.go(Ad.room(l, Nat.add(hi, hb)), 1n+w, hi, wb))), cn, h))
      +rf = LA.ad.ok_room(Ad.room(l, Nat.add(hi, hb)), w, hi, wb, cn, h)
      LA.ad.absurd_t(X, Equal.trans(Bool, True{}, Ad.room(l, 0n), False{}, Equal.sym(Bool, Ad.room(l, 0n), True{}, aw.room_t(l)), aw.room00(l, hi, hb, zh, zb, rf)))

def aw.held_le0(+ts: List<&2, Ad.Tk>, +w: Nat, ep: {Ad.pot(ts, w) == 0n : Nat}) -> {Ad.le(Ad.cnt(Ad.Holding{}, Ad.Ia{}, ts), 0n) == True{} : Bool}:
  %ep : {Ad.le(Ad.cnt(Ad.Holding{}, Ad.Ia{}, ts), _) == True{} : Bool}
  aw.held_pot(ts, w)

def aw.pos_go(p: Nat, +l: Ad.Lim, +ts: List<&2, Ad.Tk>, +w: Nat, ep: {Ad.pot(ts, w) == p : Nat}, +inv: {LA.ad.ok(l, ts) == True{} : Bool}, ws: {Ad.waits.ia(Ad.get(ts, w)) == True{} : Bool}) -> {Ad.le(1n, p) == True{} : Bool}:
  match p:
    case 1n+x:
      {==}
    case 0n:
      +hi = Ad.cnt(Ad.Holding{}, Ad.Ia{}, ts)
      aw.no_idle({Ad.le(1n, 0n) == True{} : Bool}, l, hi, Ad.cnt(Ad.Waiting{}, Ad.Ia{}, ts), Ad.cnt(Ad.Holding{}, Ad.Bg{}, ts), Ad.cnt(Ad.Waiting{}, Ad.Bg{}, ts), aw.le0(hi, aw.held_le0(ts, w, ep)), LA.aw.wait_cnt(ts, w, ws), inv)

# while w waits, it waits for something
def aw.pot_pos(s: Ad.St, +w: Nat, inv: {LA.ad.okS(s) == True{} : Bool}, ws: {Ad.waits.ia(Ad.status(s, w)) == True{} : Bool}) -> {Ad.le(1n, Ad.ahead(s, w)) == True{} : Bool}:
  match s:
    case Ad.St{+l, q, +ts}:
      aw.pos_go(Ad.pot(ts, w), l, ts, w, {==}, inv, ws)

# A run
# -----

def aw.thru_head(os: List<&2, Ad.Op>, +s: Ad.St, +w: Nat, e: {Ad.waits.thru(os, s, w) == True{} : Bool}) -> {Ad.waits.ia(Ad.status(s, w)) == True{} : Bool}:
  match os:
    case Nil{}:
      e
    case +o <> r:
      LA.ad.and_l(Ad.waits.ia(Ad.status(s, w)), Ad.waits.thru(r, Ad.step(s, o), w), e)

def aw.trace(os: List<&2, Ad.Op>, +s: Ad.St, +w: Nat, +inv: {LA.ad.okS(s) == True{} : Bool}, +e: {Ad.waits.thru(os, s, w) == True{} : Bool}) -> {Ad.le(1n+Ad.frees.run(os, s), Ad.ahead(s, w)) == True{} : Bool}:
  match os:
    case Nil{}:
      aw.pot_pos(s, w, inv, e)
    case +o <> +r:
      +s2 = Ad.step(s, o)
      +f = Ad.frees(s, o)
      +ff = Ad.frees.run(r, s2)
      +a1 = Ad.ahead(s2, w)
      +a0 = Ad.ahead(s, w)
      +e2 = LA.ad.and_r(Ad.waits.ia(Ad.status(s, w)), Ad.waits.thru(r, s2, w), e)
      +ih = aw.trace(r, s2, w, LA.ad.step_ok(s, o, inv), e2)
      +st = LA.aw.step(s, o, w, LA.ad.and_l(Ad.waits.ia(Ad.status(s, w)), Ad.waits.thru(r, s2, w), e), aw.thru_head(r, s2, w, e2))
      %Equal.sym(Nat, 1n+Nat.add(f, ff), Nat.add(f, 1n+ff), LA.ad.add_succ(f, ff)) : {Ad.le(_, a0) == True{} : Bool}
      LA.ad.le_trans(Nat.add(f, 1n+ff), Nat.add(f, a1), a0, aw.le_add_l(f, 1n+ff, a1, ih), st)

def interactive_bound(+l: Ad.Lim, +q: Nat, +pre: List<&2, Ad.Op>, +os: List<&2, Ad.Op>, +w: Nat, e: {Ad.waits.thru(os, Ad.run(pre, Ad.St.new(l, q)), w) == True{} : Bool}) -> {Ad.le(1n+Ad.frees.run(os, Ad.run(pre, Ad.St.new(l, q))), Ad.ahead(Ad.run(pre, Ad.St.new(l, q)), w)) == True{} : Bool}:
  aw.trace(os, Ad.run(pre, Ad.St.new(l, q)), w, LA.ad.run_ok(pre, Ad.St.new(l, q), LA.ad.new_ok(l, q)), e)

def Laws.admission_interactive_bound(l, q, pre, os, w, waits):
  interactive_bound(l, q, pre, os, w, waits)
