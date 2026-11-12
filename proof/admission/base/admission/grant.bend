# eukhe: lemmas the proofs of area admission share: admission/grant. The model's grant loop, which
# grants one waiter at a time (Ad.grant.go), is the spec's two passes
# (Admission.ads_grant). A pass with no waiter of its class, or no free
# slot, changes nothing (pag.none_waits, pag.no_slot); granting the oldest
# waiter first and then passing with one slot fewer is the pass
# (pag.mark_some, pag.mark_none); so each turn of the loop keeps the
# spec's answer (pag.turn_ia, pag.turn_bg) and a loop that stops has
# nothing left to grant (pag.idle, pag.none).

import Base
import ../../../../bend/admission.bend as Ad
import ../../../../laws/admission.bend as Admission
import ./bit.bend as LAAdmissionBit
import ./cnt.bend as LAAdmissionCnt
import ./isz.bend as LAAdmissionIsz
import ./le.bend as LAAdmissionLe
import ../logic.bend as LALogic
import ../nat.bend as LANat
import ./count.bend as PC

# Free slots
# ----------

# with n below 1 + p, one more held leaves one slot fewer
def pag.left_up(n: Nat, p: Nat, h: {Ad.le(n, p) == True{} : Bool}) -> {Admission.ads_left(1n+p, n) == 1n+Admission.ads_left(p, n) : Nat}:
  match n p:
    case 0n 0n:
      {==}
    case 0n 1n+b:
      {==}
    case 1n+m 0n:
      PC.pac.false_true({Admission.ads_left(1n, 1n+m) == 1n+Admission.ads_left(0n, 1n+m) : Nat}, h)
    case 1n+m 1n+b:
      pag.left_up(m, b, h)

# with n past p, no slot is left
def pag.left_zero(n: Nat, p: Nat, h: {Ad.le(n, p) == False{} : Bool}) -> {Admission.ads_left(1n+p, n) == 0n : Nat}:
  match n p:
    case 0n _:
      PC.pac.true_false({Admission.ads_left(1n+p, 0n) == 0n : Nat}, h)
    case 1n+m 0n:
      {==}
    case 1n+m 1n+b:
      pag.left_zero(m, b, h)

def pag.free_zero(l: Ad.Lim, n: Nat, h: {Ad.room(l, n) == False{} : Bool}) -> {Admission.ads_free(l, n) == Some{0n} : Maybe<&2, Nat>}:
  match l:
    case Ad.Unl{}:
      PC.pac.true_false({Admission.ads_free(Ad.Unl{}, n) == Some{0n} : Maybe<&2, Nat>}, h)
    case Ad.Cap{p}:
      %Equal.sym(Nat, Admission.ads_left(1n+p, n), 0n, pag.left_zero(n, p, h)) : {Some{_} == Some{0n} : Maybe<&2, Nat>}
      {==}

# Passes that change nothing
# --------------------------

def pag.head0(w: Bool, c: Ad.Cls, h: Ad.Tk) -> {Admission.ads_head(w, Some{0n}, c, h) == h : Ad.Tk}:
  match w:
    case True{}:
      {==}
    case False{}:
      {==}

def pag.next0(w: Bool) -> {Admission.ads_next(w, Some{0n}) == Some{0n} : Maybe<&2, Nat>}:
  match w:
    case True{}:
      {==}
    case False{}:
      {==}

# a pass with no slot left changes nothing
def pag.no_slot(+c: Ad.Cls, ts: List<&2, Ad.Tk>) -> {Admission.ads_take(c, ts, Some{0n}) == ts : List<&2, Ad.Tk>}:
  match ts:
    case Nil{}:
      {==}
    case +h <> +r:
      %Equal.sym(Maybe<&2, Nat>, Admission.ads_next(Admission.ads_waits(c, h), Some{0n}), Some{0n}, pag.next0(Admission.ads_waits(c, h))) : {Admission.ads_head(Admission.ads_waits(c, h), Some{0n}, c, h) <> Admission.ads_take(c, r, _) == h <> r : List<&2, Ad.Tk>}
      %Equal.sym(Ad.Tk, Admission.ads_head(Admission.ads_waits(c, h), Some{0n}, c, h), h, pag.head0(Admission.ads_waits(c, h), c, h)) : {_ <> Admission.ads_take(c, r, Some{0n}) == h <> r : List<&2, Ad.Tk>}
      %Equal.sym(List<&2, Ad.Tk>, Admission.ads_take(c, r, Some{0n}), r, pag.no_slot(c, r)) : {h <> _ == h <> r : List<&2, Ad.Tk>}
      {==}

def pag.nw_q(c: Ad.Cls, tc: Ad.Cls, +r: List<&2, Ad.Tk>, +f: Maybe<&2, Nat>, z: {Admission.ads_queued(c, Ad.Tk{tc, Ad.Queued{}} <> r) == 0n : Nat}, ih: {Admission.ads_queued(c, r) == 0n : Nat} -> {Admission.ads_take(c, r, f) == r : List<&2, Ad.Tk>}) -> {Admission.ads_take(c, Ad.Tk{tc, Ad.Queued{}} <> r, f) == Ad.Tk{tc, Ad.Queued{}} <> r : List<&2, Ad.Tk>}:
  match c tc:
    case Ad.Ia{} Ad.Ia{}:
      PC.pac.succ_zero({Admission.ads_take(Ad.Ia{}, Ad.Tk{Ad.Ia{}, Ad.Queued{}} <> r, f) == Ad.Tk{Ad.Ia{}, Ad.Queued{}} <> r : List<&2, Ad.Tk>}, Admission.ads_queued(Ad.Ia{}, r), z)
    case Ad.Ia{} Ad.Bg{}:
      %Equal.sym(List<&2, Ad.Tk>, Admission.ads_take(Ad.Ia{}, r, f), r, ih(z)) : {Ad.Tk{Ad.Bg{}, Ad.Queued{}} <> _ == Ad.Tk{Ad.Bg{}, Ad.Queued{}} <> r : List<&2, Ad.Tk>}
      {==}
    case Ad.Bg{} Ad.Ia{}:
      %Equal.sym(List<&2, Ad.Tk>, Admission.ads_take(Ad.Bg{}, r, f), r, ih(z)) : {Ad.Tk{Ad.Ia{}, Ad.Queued{}} <> _ == Ad.Tk{Ad.Ia{}, Ad.Queued{}} <> r : List<&2, Ad.Tk>}
      {==}
    case Ad.Bg{} Ad.Bg{}:
      PC.pac.succ_zero({Admission.ads_take(Ad.Bg{}, Ad.Tk{Ad.Bg{}, Ad.Queued{}} <> r, f) == Ad.Tk{Ad.Bg{}, Ad.Queued{}} <> r : List<&2, Ad.Tk>}, Admission.ads_queued(Ad.Bg{}, r), z)

# a pass of a class with no waiter changes nothing
def pag.none_waits(+c: Ad.Cls, ts: List<&2, Ad.Tk>, +f: Maybe<&2, Nat>, z: {Admission.ads_queued(c, ts) == 0n : Nat}) -> {Admission.ads_take(c, ts, f) == ts : List<&2, Ad.Tk>}:
  match ts:
    case Nil{}:
      {==}
    case Ad.Tk{+tc, +s} <> +r:
      match s:
        case Ad.Queued{}:
          pag.nw_q(c, tc, r, f, z, (zr => pag.none_waits(c, r, f, zr)))
        case Ad.Granted{}:
          %Equal.sym(List<&2, Ad.Tk>, Admission.ads_take(c, r, f), r, pag.none_waits(c, r, f, z)) : {Ad.Tk{tc, Ad.Granted{}} <> _ == Ad.Tk{tc, Ad.Granted{}} <> r : List<&2, Ad.Tk>}
          {==}
        case Ad.Held{}:
          %Equal.sym(List<&2, Ad.Tk>, Admission.ads_take(c, r, f), r, pag.none_waits(c, r, f, z)) : {Ad.Tk{tc, Ad.Held{}} <> _ == Ad.Tk{tc, Ad.Held{}} <> r : List<&2, Ad.Tk>}
          {==}
        case Ad.Preempted{}:
          %Equal.sym(List<&2, Ad.Tk>, Admission.ads_take(c, r, f), r, pag.none_waits(c, r, f, z)) : {Ad.Tk{tc, Ad.Preempted{}} <> _ == Ad.Tk{tc, Ad.Preempted{}} <> r : List<&2, Ad.Tk>}
          {==}
        case Ad.Ended{}:
          %Equal.sym(List<&2, Ad.Tk>, Admission.ads_take(c, r, f), r, pag.none_waits(c, r, f, z)) : {Ad.Tk{tc, Ad.Ended{}} <> _ == Ad.Tk{tc, Ad.Ended{}} <> r : List<&2, Ad.Tk>}
          {==}

# A pass is its first grant, then a pass with one slot fewer
# ----------------------------------------------------------

def pag.mark_some_at(b: Bool, +c: Ad.Cls, +h: Ad.Tk, +r: List<&2, Ad.Tk>, +k: Nat, eb: {Admission.ads_waits(c, h) == b : Bool}, nz: {Ad.isz(Ad.bit(b, Ad.cnt(Ad.Waiting{}, c, r))) == False{} : Bool}, ih: {Ad.isz(Ad.cnt(Ad.Waiting{}, c, r)) == False{} : Bool} -> {Admission.ads_take(c, Ad.mark(c, r), Some{k}) == Admission.ads_take(c, r, Some{1n+k}) : List<&2, Ad.Tk>}) -> {Admission.ads_take(c, Ad.mark.at(b, c, h, r, Ad.mark(c, r)), Some{k}) == Admission.ads_head(Admission.ads_waits(c, h), Some{1n+k}, c, h) <> Admission.ads_take(c, r, Admission.ads_next(Admission.ads_waits(c, h), Some{1n+k})) : List<&2, Ad.Tk>}:
  match b:
    case True{}:
      %Equal.sym(Bool, Admission.ads_waits(c, h), True{}, eb) : {Admission.ads_take(c, Ad.Tk{c, Ad.Granted{}} <> r, Some{k}) == Admission.ads_head(_, Some{1n+k}, c, h) <> Admission.ads_take(c, r, Admission.ads_next(_, Some{1n+k})) : List<&2, Ad.Tk>}
      {==}
    case False{}:
      %Equal.sym(Bool, Admission.ads_waits(c, h), False{}, eb) : {Admission.ads_head(_, Some{k}, c, h) <> Admission.ads_take(c, Ad.mark(c, r), Admission.ads_next(_, Some{k})) == Admission.ads_head(_, Some{1n+k}, c, h) <> Admission.ads_take(c, r, Admission.ads_next(_, Some{1n+k})) : List<&2, Ad.Tk>}
      %ih(nz) : {h <> Admission.ads_take(c, Ad.mark(c, r), Some{k}) == h <> _ : List<&2, Ad.Tk>}
      {==}

# granting the oldest waiter, then passing with one slot fewer, is the pass
def pag.mark_some(+c: Ad.Cls, ts: List<&2, Ad.Tk>, +k: Nat, nz: {Ad.isz(Ad.cnt(Ad.Waiting{}, c, ts)) == False{} : Bool}) -> {Admission.ads_take(c, Ad.mark(c, ts), Some{k}) == Admission.ads_take(c, ts, Some{1n+k}) : List<&2, Ad.Tk>}:
  match ts:
    case Nil{}:
      PC.pac.true_false({Admission.ads_take(c, Ad.mark(c, Nil{}), Some{k}) == Admission.ads_take(c, Nil{}, Some{1n+k}) : List<&2, Ad.Tk>}, nz)
    case +h <> +r:
      pag.mark_some_at(Ad.hit(Ad.Waiting{}, c, h), c, h, r, k, PC.pac.waits(c, h), nz, (nzr => pag.mark_some(c, r, k, nzr)))

def pag.mark_none_at(b: Bool, +c: Ad.Cls, +h: Ad.Tk, +r: List<&2, Ad.Tk>, eb: {Admission.ads_waits(c, h) == b : Bool}, nz: {Ad.isz(Ad.bit(b, Ad.cnt(Ad.Waiting{}, c, r))) == False{} : Bool}, ih: {Ad.isz(Ad.cnt(Ad.Waiting{}, c, r)) == False{} : Bool} -> {Admission.ads_take(c, Ad.mark(c, r), None{}) == Admission.ads_take(c, r, None{}) : List<&2, Ad.Tk>}) -> {Admission.ads_take(c, Ad.mark.at(b, c, h, r, Ad.mark(c, r)), None{}) == Admission.ads_head(Admission.ads_waits(c, h), None{}, c, h) <> Admission.ads_take(c, r, Admission.ads_next(Admission.ads_waits(c, h), None{})) : List<&2, Ad.Tk>}:
  match b:
    case True{}:
      %Equal.sym(Bool, Admission.ads_waits(c, h), True{}, eb) : {Admission.ads_take(c, Ad.Tk{c, Ad.Granted{}} <> r, None{}) == Admission.ads_head(_, None{}, c, h) <> Admission.ads_take(c, r, Admission.ads_next(_, None{})) : List<&2, Ad.Tk>}
      {==}
    case False{}:
      %Equal.sym(Bool, Admission.ads_waits(c, h), False{}, eb) : {Admission.ads_head(_, None{}, c, h) <> Admission.ads_take(c, Ad.mark(c, r), Admission.ads_next(_, None{})) == Admission.ads_head(_, None{}, c, h) <> Admission.ads_take(c, r, Admission.ads_next(_, None{})) : List<&2, Ad.Tk>}
      %ih(nz) : {h <> Admission.ads_take(c, Ad.mark(c, r), None{}) == h <> _ : List<&2, Ad.Tk>}
      {==}

# with no limit, granting the oldest waiter first changes no pass
def pag.mark_none(+c: Ad.Cls, ts: List<&2, Ad.Tk>, nz: {Ad.isz(Ad.cnt(Ad.Waiting{}, c, ts)) == False{} : Bool}) -> {Admission.ads_take(c, Ad.mark(c, ts), None{}) == Admission.ads_take(c, ts, None{}) : List<&2, Ad.Tk>}:
  match ts:
    case Nil{}:
      PC.pac.true_false({Admission.ads_take(c, Ad.mark(c, Nil{}), None{}) == Admission.ads_take(c, Nil{}, None{}) : List<&2, Ad.Tk>}, nz)
    case +h <> +r:
      pag.mark_none_at(Ad.hit(Ad.Waiting{}, c, h), c, h, r, PC.pac.waits(c, h), nz, (nzr => pag.mark_none(c, r, nzr)))

# with a slot free, granting the oldest waiter, then passing with the
# slots the grant leaves, is the pass
def pag.take_mark(+c: Ad.Cls, l: Ad.Lim, ts: List<&2, Ad.Tk>, +n: Nat, er: {Ad.room(l, n) == True{} : Bool}, nz: {Ad.isz(Ad.cnt(Ad.Waiting{}, c, ts)) == False{} : Bool}) -> {Admission.ads_take(c, Ad.mark(c, ts), Admission.ads_free(l, 1n+n)) == Admission.ads_take(c, ts, Admission.ads_free(l, n)) : List<&2, Ad.Tk>}:
  match l:
    case Ad.Unl{}:
      pag.mark_none(c, ts, nz)
    case Ad.Cap{+p}:
      %Equal.sym(Nat, Admission.ads_left(1n+p, n), 1n+Admission.ads_left(p, n), pag.left_up(n, p, er)) : {Admission.ads_take(c, Ad.mark(c, ts), Some{Admission.ads_left(p, n)}) == Admission.ads_take(c, ts, Some{_}) : List<&2, Ad.Tk>}
      pag.mark_some(c, ts, Admission.ads_left(p, n), nz)

# A pass keeps an interactive slot held
# -------------------------------------

def pag.one_nz(b: Bool, -x: Nat, e: {Nat.is_eq(x, 0n) == False{} : Bool}) -> {Nat.is_eq(Admission.ads_one(b, x), 0n) == False{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      e

def pag.held_nz_tk(+c: Ad.Cls, tc: Ad.Cls, s: Ad.Sts, +r: List<&2, Ad.Tk>, +f: Maybe<&2, Nat>, nz: {Nat.is_eq(Admission.ads_held(Ad.Ia{}, Ad.Tk{tc, s} <> r), 0n) == False{} : Bool}, ih: @g: Maybe<&2, Nat> -> {Nat.is_eq(Admission.ads_held(Ad.Ia{}, r), 0n) == False{} : Bool} -> {Nat.is_eq(Admission.ads_held(Ad.Ia{}, Admission.ads_take(c, r, g)), 0n) == False{} : Bool}) -> {Nat.is_eq(Admission.ads_held(Ad.Ia{}, Admission.ads_take(c, Ad.Tk{tc, s} <> r, f)), 0n) == False{} : Bool}:
  match tc s:
    case Ad.Ia{} Ad.Queued{}:
      +w = Admission.ads_waits(c, Ad.Tk{Ad.Ia{}, Ad.Queued{}})
      pag.one_nz(Admission.ads_holds(Ad.Ia{}, Admission.ads_head(w, f, c, Ad.Tk{Ad.Ia{}, Ad.Queued{}})), Admission.ads_held(Ad.Ia{}, Admission.ads_take(c, r, Admission.ads_next(w, f))), ih(Admission.ads_next(w, f), nz))
    case Ad.Ia{} Ad.Granted{}:
      {==}
    case Ad.Ia{} Ad.Held{}:
      {==}
    case Ad.Ia{} Ad.Preempted{}:
      ih(f, nz)
    case Ad.Ia{} Ad.Ended{}:
      ih(f, nz)
    case Ad.Bg{} Ad.Queued{}:
      +w = Admission.ads_waits(c, Ad.Tk{Ad.Bg{}, Ad.Queued{}})
      pag.one_nz(Admission.ads_holds(Ad.Ia{}, Admission.ads_head(w, f, c, Ad.Tk{Ad.Bg{}, Ad.Queued{}})), Admission.ads_held(Ad.Ia{}, Admission.ads_take(c, r, Admission.ads_next(w, f))), ih(Admission.ads_next(w, f), nz))
    case Ad.Bg{} Ad.Granted{}:
      ih(f, nz)
    case Ad.Bg{} Ad.Held{}:
      ih(f, nz)
    case Ad.Bg{} Ad.Preempted{}:
      ih(f, nz)
    case Ad.Bg{} Ad.Ended{}:
      ih(f, nz)

def pag.held_nz(+c: Ad.Cls, ts: List<&2, Ad.Tk>, +f: Maybe<&2, Nat>, nz: {Nat.is_eq(Admission.ads_held(Ad.Ia{}, ts), 0n) == False{} : Bool}) -> {Nat.is_eq(Admission.ads_held(Ad.Ia{}, Admission.ads_take(c, ts, f)), 0n) == False{} : Bool}:
  match ts:
    case Nil{}:
      PC.pac.true_false({Nat.is_eq(Admission.ads_held(Ad.Ia{}, Admission.ads_take(c, Nil{}, f)), 0n) == False{} : Bool}, nz)
    case Ad.Tk{tc, s} <> +r:
      pag.held_nz_tk(c, tc, s, r, f, nz, (g => nzr => pag.held_nz(c, r, g, nzr)))

# The two passes
# --------------

def pag.then_id(b: Bool, f: Maybe<&2, Nat>, +t: List<&2, Ad.Tk>, h: {Admission.ads_take(Ad.Bg{}, t, f) == t : List<&2, Ad.Tk>}) -> {Admission.ads_grant.then(b, f, t) == t : List<&2, Ad.Tk>}:
  match b:
    case True{}:
      h
    case False{}:
      {==}

def pag.then_off(b: Bool, f: Maybe<&2, Nat>, g: Maybe<&2, Nat>, t: List<&2, Ad.Tk>, e: {b == False{} : Bool}) -> {Admission.ads_grant.then(b, f, t) == Admission.ads_grant.then(b, g, t) : List<&2, Ad.Tk>}:
  match b:
    case True{}:
      PC.pac.true_false({Admission.ads_grant.then(True{}, f, t) == Admission.ads_grant.then(True{}, g, t) : List<&2, Ad.Tk>}, e)
    case False{}:
      {==}

# with no waiter, the passes change nothing
def pag.idle(+l: Ad.Lim, +t: List<&2, Ad.Tk>, z: {Ad.cnt(Ad.Waiting{}, Ad.Ia{}, t) == 0n : Nat} & {Ad.cnt(Ad.Waiting{}, Ad.Bg{}, t) == 0n : Nat}) -> {Admission.ads_grant(l, t) == t : List<&2, Ad.Tk>}:
  (+zi, +zb) = z
  +f = Admission.ads_free(l, Admission.ads_busy(t))
  +zi2 = Equal.trans(Nat, Admission.ads_queued(Ad.Ia{}, t), Ad.cnt(Ad.Waiting{}, Ad.Ia{}, t), 0n, PC.pac.queued(Ad.Ia{}, t), zi)
  +zb2 = Equal.trans(Nat, Admission.ads_queued(Ad.Bg{}, t), Ad.cnt(Ad.Waiting{}, Ad.Bg{}, t), 0n, PC.pac.queued(Ad.Bg{}, t), zb)
  %Equal.sym(List<&2, Ad.Tk>, Admission.ads_take(Ad.Ia{}, t, f), t, pag.none_waits(Ad.Ia{}, t, f, zi2)) : {Admission.ads_grant.then(Bool.and(Nat.is_eq(Admission.ads_held(Ad.Ia{}, _), 0n), Nat.is_eq(Admission.ads_queued(Ad.Ia{}, _), 0n)), f, _) == t : List<&2, Ad.Tk>}
  pag.then_id(Bool.and(Nat.is_eq(Admission.ads_held(Ad.Ia{}, t), 0n), Nat.is_eq(Admission.ads_queued(Ad.Ia{}, t), 0n)), f, t, pag.none_waits(Ad.Bg{}, t, f, zb2))

# a loop that grants nothing: the passes change nothing
def pag.none.go(r: Bool, wi: Nat, hi: Nat, wb: Nat, +l: Ad.Lim, +t: List<&2, Ad.Tk>, er: {Ad.room(l, Ad.held(t)) == r : Bool}, ewi: {Ad.cnt(Ad.Waiting{}, Ad.Ia{}, t) == wi : Nat}, ehi: {Ad.cnt(Ad.Holding{}, Ad.Ia{}, t) == hi : Nat}, ewb: {Ad.cnt(Ad.Waiting{}, Ad.Bg{}, t) == wb : Nat}, e: {Ad.pick.go(r, wi, hi, wb) == None{} : Maybe<&2, Ad.Cls>}) -> {Admission.ads_grant(l, t) == t : List<&2, Ad.Tk>}:
  match r wi hi wb:
    case False{} _ _ _:
      +z = pag.free_zero(l, Ad.held(t), er)
      %Equal.sym(Nat, Admission.ads_busy(t), Ad.held(t), PC.pac.busy(t)) : {Admission.ads_grant.then(Bool.and(Nat.is_eq(Admission.ads_held(Ad.Ia{}, Admission.ads_take(Ad.Ia{}, t, Admission.ads_free(l, _))), 0n), Nat.is_eq(Admission.ads_queued(Ad.Ia{}, Admission.ads_take(Ad.Ia{}, t, Admission.ads_free(l, _))), 0n)), Admission.ads_free(l, _), Admission.ads_take(Ad.Ia{}, t, Admission.ads_free(l, _))) == t : List<&2, Ad.Tk>}
      %Equal.sym(Maybe<&2, Nat>, Admission.ads_free(l, Ad.held(t)), Some{0n}, z) : {Admission.ads_grant.then(Bool.and(Nat.is_eq(Admission.ads_held(Ad.Ia{}, Admission.ads_take(Ad.Ia{}, t, _)), 0n), Nat.is_eq(Admission.ads_queued(Ad.Ia{}, Admission.ads_take(Ad.Ia{}, t, _)), 0n)), _, Admission.ads_take(Ad.Ia{}, t, _)) == t : List<&2, Ad.Tk>}
      %Equal.sym(List<&2, Ad.Tk>, Admission.ads_take(Ad.Ia{}, t, Some{0n}), t, pag.no_slot(Ad.Ia{}, t)) : {Admission.ads_grant.then(Bool.and(Nat.is_eq(Admission.ads_held(Ad.Ia{}, _), 0n), Nat.is_eq(Admission.ads_queued(Ad.Ia{}, _), 0n)), Some{0n}, _) == t : List<&2, Ad.Tk>}
      pag.then_id(Bool.and(Nat.is_eq(Admission.ads_held(Ad.Ia{}, t), 0n), Nat.is_eq(Admission.ads_queued(Ad.Ia{}, t), 0n)), Some{0n}, t, pag.no_slot(Ad.Bg{}, t))
    case True{} 1n+a _ _:
      PC.pac.some_none({Admission.ads_grant(l, t) == t : List<&2, Ad.Tk>}, Ad.Ia{}, e)
    case True{} 0n 1n+b _:
      +f = Admission.ads_free(l, Admission.ads_busy(t))
      +zi2 = Equal.trans(Nat, Admission.ads_queued(Ad.Ia{}, t), Ad.cnt(Ad.Waiting{}, Ad.Ia{}, t), 0n, PC.pac.queued(Ad.Ia{}, t), ewi)
      +hi2 = Equal.trans(Nat, Admission.ads_held(Ad.Ia{}, t), Ad.cnt(Ad.Holding{}, Ad.Ia{}, t), 1n+b, PC.pac.held(Ad.Ia{}, t), ehi)
      %Equal.sym(List<&2, Ad.Tk>, Admission.ads_take(Ad.Ia{}, t, f), t, pag.none_waits(Ad.Ia{}, t, f, zi2)) : {Admission.ads_grant.then(Bool.and(Nat.is_eq(Admission.ads_held(Ad.Ia{}, _), 0n), Nat.is_eq(Admission.ads_queued(Ad.Ia{}, _), 0n)), f, _) == t : List<&2, Ad.Tk>}
      %Equal.sym(Nat, Admission.ads_held(Ad.Ia{}, t), 1n+b, hi2) : {Admission.ads_grant.then(Bool.and(Nat.is_eq(_, 0n), Nat.is_eq(Admission.ads_queued(Ad.Ia{}, t), 0n)), f, t) == t : List<&2, Ad.Tk>}
      {==}
    case True{} 0n 0n 0n:
      +f = Admission.ads_free(l, Admission.ads_busy(t))
      +zi2 = Equal.trans(Nat, Admission.ads_queued(Ad.Ia{}, t), Ad.cnt(Ad.Waiting{}, Ad.Ia{}, t), 0n, PC.pac.queued(Ad.Ia{}, t), ewi)
      +zb2 = Equal.trans(Nat, Admission.ads_queued(Ad.Bg{}, t), Ad.cnt(Ad.Waiting{}, Ad.Bg{}, t), 0n, PC.pac.queued(Ad.Bg{}, t), ewb)
      %Equal.sym(List<&2, Ad.Tk>, Admission.ads_take(Ad.Ia{}, t, f), t, pag.none_waits(Ad.Ia{}, t, f, zi2)) : {Admission.ads_grant.then(Bool.and(Nat.is_eq(Admission.ads_held(Ad.Ia{}, _), 0n), Nat.is_eq(Admission.ads_queued(Ad.Ia{}, _), 0n)), f, _) == t : List<&2, Ad.Tk>}
      pag.then_id(Bool.and(Nat.is_eq(Admission.ads_held(Ad.Ia{}, t), 0n), Nat.is_eq(Admission.ads_queued(Ad.Ia{}, t), 0n)), f, t, pag.none_waits(Ad.Bg{}, t, f, zb2))
    case True{} 0n 0n 1n+d:
      PC.pac.some_none({Admission.ads_grant(l, t) == t : List<&2, Ad.Tk>}, Ad.Bg{}, e)

def pag.none(+l: Ad.Lim, +t: List<&2, Ad.Tk>, e: {Ad.pick(l, t) == None{} : Maybe<&2, Ad.Cls>}) -> {Admission.ads_grant(l, t) == t : List<&2, Ad.Tk>}:
  pag.none.go(Ad.room(l, Ad.held(t)), Ad.cnt(Ad.Waiting{}, Ad.Ia{}, t), Ad.cnt(Ad.Holding{}, Ad.Ia{}, t), Ad.cnt(Ad.Waiting{}, Ad.Bg{}, t), l, t, {==}, {==}, {==}, {==}, e)

# a picked waiter's class: a slot was free
def pag.pick_room(r: Bool, wi: Nat, hi: Nat, wb: Nat, -c: Ad.Cls, e: {Ad.pick.go(r, wi, hi, wb) == Some{c} : Maybe<&2, Ad.Cls>}) -> {r == True{} : Bool}:
  match r:
    case True{}:
      {==}
    case False{}:
      PC.pac.some_none({False{} == True{} : Bool}, c, Equal.sym(Maybe<&2, Ad.Cls>, Ad.pick.go(False{}, wi, hi, wb), Some{c}, e))

# one turn of the loop that grants the oldest interactive waiter keeps the
# spec's answer
def pag.turn_ia(+l: Ad.Lim, +t: List<&2, Ad.Tk>, er: {Ad.room(l, Ad.held(t)) == True{} : Bool}, +nz: {Ad.isz(Ad.cnt(Ad.Waiting{}, Ad.Ia{}, t)) == False{} : Bool}) -> {Admission.ads_grant(l, Ad.mark(Ad.Ia{}, t)) == Admission.ads_grant(l, t) : List<&2, Ad.Tk>}:
  +t2 = Ad.mark(Ad.Ia{}, t)
  +n = Ad.held(t)
  +hi = LAAdmissionBit.ad.cnt_mark(Ad.Holding{}, Ad.Ia{}, t, Ad.Ia{}, nz)
  +hb = LAAdmissionBit.ad.cnt_mark(Ad.Holding{}, Ad.Bg{}, t, Ad.Ia{}, nz)
  +busy2 = Equal.trans(Nat, Admission.ads_busy(t2), Ad.held(t2), 1n+n, PC.pac.busy(t2), Equal.trans(Nat, Ad.held(t2), Nat.add(1n+Ad.cnt(Ad.Holding{}, Ad.Ia{}, t), Ad.cnt(Ad.Holding{}, Ad.Bg{}, t2)), 1n+n, Equal.cong(Nat, Nat, x => Nat.add(x, Ad.cnt(Ad.Holding{}, Ad.Bg{}, t2)), Ad.cnt(Ad.Holding{}, Ad.Ia{}, t2), 1n+Ad.cnt(Ad.Holding{}, Ad.Ia{}, t), hi), Equal.cong(Nat, Nat, x => 1n+Nat.add(Ad.cnt(Ad.Holding{}, Ad.Ia{}, t), x), Ad.cnt(Ad.Holding{}, Ad.Bg{}, t2), Ad.cnt(Ad.Holding{}, Ad.Bg{}, t), hb)))
  +busy1 = PC.pac.busy(t)
  +same = pag.take_mark(Ad.Ia{}, l, t, n, er, nz)
  +big = Admission.ads_take(Ad.Ia{}, t2, Admission.ads_free(l, 1n+n))
  +held2 = Equal.trans(Nat, Admission.ads_held(Ad.Ia{}, t2), Ad.cnt(Ad.Holding{}, Ad.Ia{}, t2), 1n+Ad.cnt(Ad.Holding{}, Ad.Ia{}, t), PC.pac.held(Ad.Ia{}, t2), hi)
  +nzh = pag.held_nz(Ad.Ia{}, t2, Admission.ads_free(l, 1n+n), Equal.cong(Nat, Bool, x => Nat.is_eq(x, 0n), Admission.ads_held(Ad.Ia{}, t2), 1n+Ad.cnt(Ad.Holding{}, Ad.Ia{}, t), held2))
  %Equal.sym(Nat, Admission.ads_busy(t2), 1n+n, busy2) : {Admission.ads_grant.then(Bool.and(Nat.is_eq(Admission.ads_held(Ad.Ia{}, Admission.ads_take(Ad.Ia{}, t2, Admission.ads_free(l, _))), 0n), Nat.is_eq(Admission.ads_queued(Ad.Ia{}, Admission.ads_take(Ad.Ia{}, t2, Admission.ads_free(l, _))), 0n)), Admission.ads_free(l, _), Admission.ads_take(Ad.Ia{}, t2, Admission.ads_free(l, _))) == Admission.ads_grant(l, t) : List<&2, Ad.Tk>}
  %Equal.sym(Nat, Admission.ads_busy(t), Ad.held(t), busy1) : {Admission.ads_grant.then(Bool.and(Nat.is_eq(Admission.ads_held(Ad.Ia{}, big), 0n), Nat.is_eq(Admission.ads_queued(Ad.Ia{}, big), 0n)), Admission.ads_free(l, 1n+n), big) == Admission.ads_grant.then(Bool.and(Nat.is_eq(Admission.ads_held(Ad.Ia{}, Admission.ads_take(Ad.Ia{}, t, Admission.ads_free(l, _))), 0n), Nat.is_eq(Admission.ads_queued(Ad.Ia{}, Admission.ads_take(Ad.Ia{}, t, Admission.ads_free(l, _))), 0n)), Admission.ads_free(l, _), Admission.ads_take(Ad.Ia{}, t, Admission.ads_free(l, _))) : List<&2, Ad.Tk>}
  %same : {Admission.ads_grant.then(Bool.and(Nat.is_eq(Admission.ads_held(Ad.Ia{}, big), 0n), Nat.is_eq(Admission.ads_queued(Ad.Ia{}, big), 0n)), Admission.ads_free(l, 1n+n), big) == Admission.ads_grant.then(Bool.and(Nat.is_eq(Admission.ads_held(Ad.Ia{}, _), 0n), Nat.is_eq(Admission.ads_queued(Ad.Ia{}, _), 0n)), Admission.ads_free(l, n), _) : List<&2, Ad.Tk>}
  pag.then_off(Bool.and(Nat.is_eq(Admission.ads_held(Ad.Ia{}, big), 0n), Nat.is_eq(Admission.ads_queued(Ad.Ia{}, big), 0n)), Admission.ads_free(l, 1n+n), Admission.ads_free(l, n), big, Equal.cong(Bool, Bool, x => Bool.and(x, Nat.is_eq(Admission.ads_queued(Ad.Ia{}, big), 0n)), Nat.is_eq(Admission.ads_held(Ad.Ia{}, big), 0n), False{}, nzh))

# one turn of the loop that grants the oldest background waiter (no
# interactive request holds or waits) keeps the spec's answer
def pag.turn_bg(+l: Ad.Lim, +t: List<&2, Ad.Tk>, er: {Ad.room(l, Ad.held(t)) == True{} : Bool}, +zi: {Ad.cnt(Ad.Waiting{}, Ad.Ia{}, t) == 0n : Nat}, +zh: {Ad.cnt(Ad.Holding{}, Ad.Ia{}, t) == 0n : Nat}, +nz: {Ad.isz(Ad.cnt(Ad.Waiting{}, Ad.Bg{}, t)) == False{} : Bool}) -> {Admission.ads_grant(l, Ad.mark(Ad.Bg{}, t)) == Admission.ads_grant(l, t) : List<&2, Ad.Tk>}:
  +t2 = Ad.mark(Ad.Bg{}, t)
  +n = Ad.held(t)
  +wi2 = LAAdmissionBit.ad.cnt_mark(Ad.Waiting{}, Ad.Ia{}, t, Ad.Bg{}, nz)
  +hi2 = LAAdmissionBit.ad.cnt_mark(Ad.Holding{}, Ad.Ia{}, t, Ad.Bg{}, nz)
  +hb2 = LAAdmissionBit.ad.cnt_mark(Ad.Holding{}, Ad.Bg{}, t, Ad.Bg{}, nz)
  +qi = Equal.trans(Nat, Admission.ads_queued(Ad.Ia{}, t), Ad.cnt(Ad.Waiting{}, Ad.Ia{}, t), 0n, PC.pac.queued(Ad.Ia{}, t), zi)
  +hi = Equal.trans(Nat, Admission.ads_held(Ad.Ia{}, t), Ad.cnt(Ad.Holding{}, Ad.Ia{}, t), 0n, PC.pac.held(Ad.Ia{}, t), zh)
  +qi2 = Equal.trans(Nat, Admission.ads_queued(Ad.Ia{}, t2), Ad.cnt(Ad.Waiting{}, Ad.Ia{}, t), 0n, Equal.trans(Nat, Admission.ads_queued(Ad.Ia{}, t2), Ad.cnt(Ad.Waiting{}, Ad.Ia{}, t2), Ad.cnt(Ad.Waiting{}, Ad.Ia{}, t), PC.pac.queued(Ad.Ia{}, t2), wi2), zi)
  +hi3 = Equal.trans(Nat, Admission.ads_held(Ad.Ia{}, t2), Ad.cnt(Ad.Holding{}, Ad.Ia{}, t), 0n, Equal.trans(Nat, Admission.ads_held(Ad.Ia{}, t2), Ad.cnt(Ad.Holding{}, Ad.Ia{}, t2), Ad.cnt(Ad.Holding{}, Ad.Ia{}, t), PC.pac.held(Ad.Ia{}, t2), hi2), zh)
  +busy2 = Equal.trans(Nat, Admission.ads_busy(t2), Ad.held(t2), 1n+n, PC.pac.busy(t2), Equal.trans(Nat, Ad.held(t2), Nat.add(Ad.cnt(Ad.Holding{}, Ad.Ia{}, t), 1n+Ad.cnt(Ad.Holding{}, Ad.Bg{}, t)), 1n+n, Equal.trans(Nat, Ad.held(t2), Nat.add(Ad.cnt(Ad.Holding{}, Ad.Ia{}, t), Ad.cnt(Ad.Holding{}, Ad.Bg{}, t2)), Nat.add(Ad.cnt(Ad.Holding{}, Ad.Ia{}, t), 1n+Ad.cnt(Ad.Holding{}, Ad.Bg{}, t)), Equal.cong(Nat, Nat, x => Nat.add(x, Ad.cnt(Ad.Holding{}, Ad.Bg{}, t2)), Ad.cnt(Ad.Holding{}, Ad.Ia{}, t2), Ad.cnt(Ad.Holding{}, Ad.Ia{}, t), hi2), Equal.cong(Nat, Nat, x => Nat.add(Ad.cnt(Ad.Holding{}, Ad.Ia{}, t), x), Ad.cnt(Ad.Holding{}, Ad.Bg{}, t2), 1n+Ad.cnt(Ad.Holding{}, Ad.Bg{}, t), hb2)), Equal.sym(Nat, 1n+n, Nat.add(Ad.cnt(Ad.Holding{}, Ad.Ia{}, t), 1n+Ad.cnt(Ad.Holding{}, Ad.Bg{}, t)), LANat.ad.add_succ(Ad.cnt(Ad.Holding{}, Ad.Ia{}, t), Ad.cnt(Ad.Holding{}, Ad.Bg{}, t)))))
  +f2 = Admission.ads_free(l, 1n+n)
  +f1 = Admission.ads_free(l, n)
  %Equal.sym(Nat, Admission.ads_busy(t2), 1n+n, busy2) : {Admission.ads_grant.then(Bool.and(Nat.is_eq(Admission.ads_held(Ad.Ia{}, Admission.ads_take(Ad.Ia{}, t2, Admission.ads_free(l, _))), 0n), Nat.is_eq(Admission.ads_queued(Ad.Ia{}, Admission.ads_take(Ad.Ia{}, t2, Admission.ads_free(l, _))), 0n)), Admission.ads_free(l, _), Admission.ads_take(Ad.Ia{}, t2, Admission.ads_free(l, _))) == Admission.ads_grant(l, t) : List<&2, Ad.Tk>}
  %Equal.sym(Nat, Admission.ads_busy(t), Ad.held(t), PC.pac.busy(t)) : {Admission.ads_grant.then(Bool.and(Nat.is_eq(Admission.ads_held(Ad.Ia{}, Admission.ads_take(Ad.Ia{}, t2, f2)), 0n), Nat.is_eq(Admission.ads_queued(Ad.Ia{}, Admission.ads_take(Ad.Ia{}, t2, f2)), 0n)), f2, Admission.ads_take(Ad.Ia{}, t2, f2)) == Admission.ads_grant.then(Bool.and(Nat.is_eq(Admission.ads_held(Ad.Ia{}, Admission.ads_take(Ad.Ia{}, t, Admission.ads_free(l, _))), 0n), Nat.is_eq(Admission.ads_queued(Ad.Ia{}, Admission.ads_take(Ad.Ia{}, t, Admission.ads_free(l, _))), 0n)), Admission.ads_free(l, _), Admission.ads_take(Ad.Ia{}, t, Admission.ads_free(l, _))) : List<&2, Ad.Tk>}
  %Equal.sym(List<&2, Ad.Tk>, Admission.ads_take(Ad.Ia{}, t2, f2), t2, pag.none_waits(Ad.Ia{}, t2, f2, qi2)) : {Admission.ads_grant.then(Bool.and(Nat.is_eq(Admission.ads_held(Ad.Ia{}, _), 0n), Nat.is_eq(Admission.ads_queued(Ad.Ia{}, _), 0n)), f2, _) == Admission.ads_grant.then(Bool.and(Nat.is_eq(Admission.ads_held(Ad.Ia{}, Admission.ads_take(Ad.Ia{}, t, f1)), 0n), Nat.is_eq(Admission.ads_queued(Ad.Ia{}, Admission.ads_take(Ad.Ia{}, t, f1)), 0n)), f1, Admission.ads_take(Ad.Ia{}, t, f1)) : List<&2, Ad.Tk>}
  %Equal.sym(List<&2, Ad.Tk>, Admission.ads_take(Ad.Ia{}, t, f1), t, pag.none_waits(Ad.Ia{}, t, f1, qi)) : {Admission.ads_grant.then(Bool.and(Nat.is_eq(Admission.ads_held(Ad.Ia{}, t2), 0n), Nat.is_eq(Admission.ads_queued(Ad.Ia{}, t2), 0n)), f2, t2) == Admission.ads_grant.then(Bool.and(Nat.is_eq(Admission.ads_held(Ad.Ia{}, _), 0n), Nat.is_eq(Admission.ads_queued(Ad.Ia{}, _), 0n)), f1, _) : List<&2, Ad.Tk>}
  %Equal.sym(Nat, Admission.ads_held(Ad.Ia{}, t2), 0n, hi3) : {Admission.ads_grant.then(Bool.and(Nat.is_eq(_, 0n), Nat.is_eq(Admission.ads_queued(Ad.Ia{}, t2), 0n)), f2, t2) == Admission.ads_grant.then(Bool.and(Nat.is_eq(Admission.ads_held(Ad.Ia{}, t), 0n), Nat.is_eq(Admission.ads_queued(Ad.Ia{}, t), 0n)), f1, t) : List<&2, Ad.Tk>}
  %Equal.sym(Nat, Admission.ads_queued(Ad.Ia{}, t2), 0n, qi2) : {Admission.ads_grant.then(Bool.and(True{}, Nat.is_eq(_, 0n)), f2, t2) == Admission.ads_grant.then(Bool.and(Nat.is_eq(Admission.ads_held(Ad.Ia{}, t), 0n), Nat.is_eq(Admission.ads_queued(Ad.Ia{}, t), 0n)), f1, t) : List<&2, Ad.Tk>}
  %Equal.sym(Nat, Admission.ads_held(Ad.Ia{}, t), 0n, hi) : {Admission.ads_take(Ad.Bg{}, t2, f2) == Admission.ads_grant.then(Bool.and(Nat.is_eq(_, 0n), Nat.is_eq(Admission.ads_queued(Ad.Ia{}, t), 0n)), f1, t) : List<&2, Ad.Tk>}
  %Equal.sym(Nat, Admission.ads_queued(Ad.Ia{}, t), 0n, qi) : {Admission.ads_take(Ad.Bg{}, t2, f2) == Admission.ads_grant.then(Bool.and(True{}, Nat.is_eq(_, 0n)), f1, t) : List<&2, Ad.Tk>}
  pag.take_mark(Ad.Bg{}, l, t, n, er, nz)

# The loop is the passes
# ----------------------

def pag.go(n: Nat, d: Maybe<&2, Ad.Cls>, +l: Ad.Lim, +t: List<&2, Ad.Tk>, +ed: {Ad.pick(l, t) == d : Maybe<&2, Ad.Cls>}, fuel: {Ad.le(Ad.waits(t), n) == True{} : Bool}) -> {Ad.grant.go(n, d, l, t) == Admission.ads_grant(l, t) : List<&2, Ad.Tk>}:
  match n d:
    case 0n _:
      Equal.sym(List<&2, Ad.Tk>, Admission.ads_grant(l, t), t, pag.idle(l, t, LALogic.ad.zero2(Ad.cnt(Ad.Waiting{}, Ad.Ia{}, t), Ad.cnt(Ad.Waiting{}, Ad.Bg{}, t), fuel)))
    case 1n+f None{}:
      Equal.sym(List<&2, Ad.Tk>, Admission.ads_grant(l, t), t, pag.none(l, t, ed))
    case 1n+f Some{Ad.Ia{}}:
      +nz = LAAdmissionIsz.ad.pick_ia(Ad.room(l, Ad.held(t)), Ad.cnt(Ad.Waiting{}, Ad.Ia{}, t), Ad.cnt(Ad.Holding{}, Ad.Ia{}, t), Ad.cnt(Ad.Waiting{}, Ad.Bg{}, t), ed)
      +er = pag.pick_room(Ad.room(l, Ad.held(t)), Ad.cnt(Ad.Waiting{}, Ad.Ia{}, t), Ad.cnt(Ad.Holding{}, Ad.Ia{}, t), Ad.cnt(Ad.Waiting{}, Ad.Bg{}, t), Ad.Ia{}, ed)
      +t2 = Ad.mark(Ad.Ia{}, t)
      Equal.trans(List<&2, Ad.Tk>, Ad.grant.go(f, Ad.pick(l, t2), l, t2), Admission.ads_grant(l, t2), Admission.ads_grant(l, t), pag.go(f, Ad.pick(l, t2), l, t2, {==}, LAAdmissionLe.ad.fuel_ia(t, f, nz, fuel)), pag.turn_ia(l, t, er, nz))
    case 1n+f Some{Ad.Bg{}}:
      +zi = LAAdmissionCnt.ad.bg_wi(t, LAAdmissionIsz.ad.pbg(l, t, ed))
      +zh = LAAdmissionCnt.ad.bg_hi(t, LAAdmissionIsz.ad.pbg(l, t, ed))
      +nz = LAAdmissionIsz.ad.bg_wb(t, LAAdmissionIsz.ad.pbg(l, t, ed))
      +er = pag.pick_room(Ad.room(l, Ad.held(t)), Ad.cnt(Ad.Waiting{}, Ad.Ia{}, t), Ad.cnt(Ad.Holding{}, Ad.Ia{}, t), Ad.cnt(Ad.Waiting{}, Ad.Bg{}, t), Ad.Bg{}, ed)
      +t2 = Ad.mark(Ad.Bg{}, t)
      Equal.trans(List<&2, Ad.Tk>, Ad.grant.go(f, Ad.pick(l, t2), l, t2), Admission.ads_grant(l, t2), Admission.ads_grant(l, t), pag.go(f, Ad.pick(l, t2), l, t2, {==}, LAAdmissionLe.ad.fuel_bg(t, f, zi, nz, fuel)), pag.turn_bg(l, t, er, zi, zh, nz))

# the model's grant is the spec's
def pag.grant(+l: Ad.Lim, +ts: List<&2, Ad.Tk>) -> {Ad.grant(l, ts) == Admission.ads_grant(l, ts) : List<&2, Ad.Tk>}:
  pag.go(Ad.waits(ts), Ad.pick(l, ts), l, ts, {==}, LAAdmissionLe.ad.le_refl(Ad.waits(ts)))
