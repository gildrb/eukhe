# eukhe: lemmas the proofs of area retry_idle share

import Base
import ../../bend/ffi_retry_idle.bend as Fi
import ../../bend/retry.bend as R
import ../../bend/wire.bend as Wr
import ../../laws/retry_idle.bend as RetryIdle
import ../../laws/wire.bend as Wire
import ../../laws/base.bend as LawsBase
import ../base/logic/logic.bend as LLogicLogic
import ./idle_wake_exact.bend as PIdleWakeExact

# Nat facts
# ---------

def ri.gt_zero(d: Nat) -> {Nat.is_gt(0n, d) == False{} : Bool}:
  match d:
    case 0n:
      {==}
    case 1n+q:
      {==}

def ri.gt_refl(d: Nat) -> {Nat.is_gt(d, d) == False{} : Bool}:
  match d:
    case 0n:
      {==}
    case 1n+q:
      ri.gt_refl(q)

def ri.sub_zero(d: Nat) -> {Nat.sub(d, 0n) == d : Nat}:
  match d:
    case 0n:
      {==}
    case 1n+q:
      {==}

# a <= b <= c: a <= c
def ri.ngt_trans(g: Nat, k: Nat, d: Nat, e1: {Nat.is_gt(g, k) == False{} : Bool}, e2: {Nat.is_gt(k, d) == False{} : Bool}) -> {Nat.is_gt(g, d) == False{} : Bool}:
  match g:
    case 0n:
      ri.gt_zero(d)
    case 1n+p:
      match k:
        case 0n:
          LLogicLogic.pf.absurd_tf({Nat.is_gt(1n+p, d) == False{} : Bool}, e1)
        case 1n+q:
          match d:
            case 0n:
              LLogicLogic.pf.absurd_tf({Nat.is_gt(1n+p, 0n) == False{} : Bool}, e2)
            case 1n+r:
              ri.ngt_trans(p, q, r, e1, e2)

# neither above the other: equal
def ri.eq_of_ngt(k: Nat, d: Nat, e1: {Nat.is_gt(k, d) == False{} : Bool}, e2: {Nat.is_gt(d, k) == False{} : Bool}) -> {k == d : Nat}:
  match k:
    case 0n:
      match d:
        case 0n:
          {==}
        case 1n+q:
          LLogicLogic.pf.absurd_tf({0n == 1n+q : Nat}, e2)
    case 1n++p:
      match d:
        case 0n:
          LLogicLogic.pf.absurd_tf({1n+p == 0n : Nat}, e1)
        case 1n++q:
          Equal.cong(Nat, Nat, x => 1n+x, p, q, ri.eq_of_ngt(p, q, e1, e2))

# k below d: k and what is left of d make d
def ri.add_sub(k: Nat, d: Nat, e: {Nat.is_gt(d, k) == True{} : Bool}) -> {Nat.add(k, Nat.sub(d, k)) == d : Nat}:
  match k:
    case 0n:
      match d:
        case 0n:
          {==}
        case 1n+q:
          {==}
    case 1n++p:
      match d:
        case 0n:
          LLogicLogic.wr_absurd({Nat.add(1n+p, Nat.sub(0n, 1n+p)) == 0n : Nat}, e)
        case 1n++q:
          Equal.cong(Nat, Nat, x => 1n+x, Nat.add(p, Nat.sub(q, p)), q, ri.add_sub(p, q, e))

def ri.ngt_succ(x: Nat, p: Nat, e: {Nat.is_gt(x, p) == False{} : Bool}) -> {Nat.is_gt(x, 1n+p) == False{} : Bool}:
  match x:
    case 0n:
      {==}
    case 1n+a:
      match p:
        case 0n:
          LLogicLogic.pf.absurd_tf({Nat.is_gt(1n+a, 1n) == False{} : Bool}, e)
        case 1n+b:
          ri.ngt_succ(a, b, e)

# k - g is at most k
def ri.sub_ngt(k: Nat, g: Nat) -> {Nat.is_gt(Nat.sub(k, g), k) == False{} : Bool}:
  match k:
    case 0n:
      {==}
    case 1n++p:
      match g:
        case 0n:
          ri.gt_refl(1n+p)
        case 1n++q:
          ri.ngt_succ(Nat.sub(p, q), p, ri.sub_ngt(p, q))

# An event, under a timer within the deadline
# --------------------------------------------

# the timer after an event that came: k - g when it came before the
# timer, d - g when it came after a re-arm
def ri.came(late: Bool, +g: Nat, +d: Nat, +k: Nat) -> Nat:
  match late:
    case False{}:
      Nat.sub(k, g)
    case True{}:
      Nat.sub(d, g)

def ri.asel(over: Bool, +last: Nat, +d: Nat, c: Nat) -> RetryIdle.Arrive:
  match over:
    case True{}:
      RetryIdle.ArrStall{Nat.add(last, d)}
    case False{}:
      RetryIdle.ArrCame{c}

# what an event g after last meets, the timer k <= d after last: the
# stall at last + d past the deadline, else the event and the timer after it
def ri.arr(+g: Nat, +d: Nat, +last: Nat, +k: Nat) -> RetryIdle.Arrive:
  ri.asel(Nat.is_gt(g, d), last, d, ri.came(Nat.is_gt(g, k), g, d, k))

def ri.a3(b3: Bool, +g: Nat, +d: Nat, +last: Nat, +k: Nat, e3: {Nat.is_gt(g, d) == b3 : Bool}, e1: {Nat.is_gt(g, k) == True{} : Bool}) -> {RetryIdle.arrive.after(b3, g, d, last, d) == ri.arr(g, d, last, k) : RetryIdle.Arrive}:
  match b3:
    case False{}:
      %Equal.sym(Bool, Nat.is_gt(g, d), False{}, e3) : {RetryIdle.ArrCame{Nat.sub(d, g)} == ri.asel(_, last, d, ri.came(Nat.is_gt(g, k), g, d, k)) : RetryIdle.Arrive}
      %Equal.sym(Bool, Nat.is_gt(g, k), True{}, e1) : {RetryIdle.ArrCame{Nat.sub(d, g)} == ri.asel(False{}, last, d, ri.came(_, g, d, k)) : RetryIdle.Arrive}
      {==}
    case True{}:
      %Equal.sym(Bool, Nat.is_gt(d, d), False{}, ri.gt_refl(d)) : {RetryIdle.arrive.fire2(last, d, R.idle.wake.sel(_, Nat.sub(d, d))) == ri.arr(g, d, last, k) : RetryIdle.Arrive}
      %Equal.sym(Bool, Nat.is_gt(g, d), True{}, e3) : {RetryIdle.ArrStall{Nat.add(last, d)} == ri.asel(_, last, d, ri.came(Nat.is_gt(g, k), g, d, k)) : RetryIdle.Arrive}
      {==}

def ri.a2(b2: Bool, +g: Nat, +d: Nat, +last: Nat, +k: Nat, e2: {Nat.is_gt(d, k) == b2 : Bool}, +e1: {Nat.is_gt(g, k) == True{} : Bool}, hk: {Nat.is_gt(k, d) == False{} : Bool}) -> {RetryIdle.arrive.fire1(g, d, last, k, R.idle.wake.sel(b2, Nat.sub(d, k))) == ri.arr(g, d, last, k) : RetryIdle.Arrive}:
  match b2:
    case False{}:
      +ekd = ri.eq_of_ngt(k, d, hk, e2)
      +egd = Equal.trans(Bool, Nat.is_gt(g, d), Nat.is_gt(g, k), True{}, Equal.cong(Nat, Bool, x => Nat.is_gt(g, x), d, k, Equal.sym(Nat, k, d, ekd)), e1)
      %Equal.sym(Bool, Nat.is_gt(g, d), True{}, egd) : {RetryIdle.ArrStall{Nat.add(last, k)} == ri.asel(_, last, d, ri.came(Nat.is_gt(g, k), g, d, k)) : RetryIdle.Arrive}
      Equal.cong(Nat, RetryIdle.Arrive, x => RetryIdle.ArrStall{Nat.add(last, x)}, k, d, ekd)
    case True{}:
      %Equal.sym(Nat, Nat.add(k, Nat.sub(d, k)), d, ri.add_sub(k, d, e2)) : {RetryIdle.arrive.after(Nat.is_gt(g, _), g, d, last, _) == ri.arr(g, d, last, k) : RetryIdle.Arrive}
      ri.a3(Nat.is_gt(g, d), g, d, last, k, {==}, e1)

def ri.a1(b1: Bool, +g: Nat, +d: Nat, +last: Nat, +k: Nat, +e1: {Nat.is_gt(g, k) == b1 : Bool}, +hk: {Nat.is_gt(k, d) == False{} : Bool}) -> {RetryIdle.arrive.first(b1, g, d, last, k) == ri.arr(g, d, last, k) : RetryIdle.Arrive}:
  match b1:
    case False{}:
      %Equal.sym(Bool, Nat.is_gt(g, d), False{}, ri.ngt_trans(g, k, d, e1, hk)) : {RetryIdle.ArrCame{Nat.sub(k, g)} == ri.asel(_, last, d, ri.came(Nat.is_gt(g, k), g, d, k)) : RetryIdle.Arrive}
      %Equal.sym(Bool, Nat.is_gt(g, k), False{}, e1) : {RetryIdle.ArrCame{Nat.sub(k, g)} == ri.asel(False{}, last, d, ri.came(_, g, d, k)) : RetryIdle.Arrive}
      {==}
    case True{}:
      ri.a2(Nat.is_gt(d, k), g, d, last, k, {==}, e1, hk)

# the loop meets an event as ri.arr says
def ri.arrive(+g: Nat, +d: Nat, +last: Nat, +k: Nat, hk: {Nat.is_gt(k, d) == False{} : Bool}) -> {RetryIdle.arrive(g, d, last, k) == ri.arr(g, d, last, k) : RetryIdle.Arrive}:
  ri.a1(Nat.is_gt(g, k), g, d, last, k, {==}, hk)

def ri.l2(b: Bool, +g: Nat, +d: Nat, +k: Nat, hk: {Nat.is_gt(k, d) == False{} : Bool}) -> {Nat.is_gt(ri.came(b, g, d, k), d) == False{} : Bool}:
  match b:
    case False{}:
      ri.ngt_trans(Nat.sub(k, g), k, d, ri.sub_ngt(k, g), hk)
    case True{}:
      ri.sub_ngt(d, g)

def ri.l1(b: Bool, +g: Nat, +d: Nat, +last: Nat, +k: Nat, hk: {Nat.is_gt(k, d) == False{} : Bool}) -> {Nat.is_gt(RetryIdle.arrive.left(ri.asel(b, last, d, ri.came(Nat.is_gt(g, k), g, d, k))), d) == False{} : Bool}:
  match b:
    case True{}:
      ri.gt_zero(d)
    case False{}:
      ri.l2(Nat.is_gt(g, k), g, d, k, hk)

# the timer after an event stays within the deadline
def ri.left_ngt(+g: Nat, +d: Nat, +last: Nat, +k: Nat, hk: {Nat.is_gt(k, d) == False{} : Bool}) -> {Nat.is_gt(RetryIdle.arrive.left(ri.arr(g, d, last, k)), d) == False{} : Bool}:
  ri.l1(Nat.is_gt(g, d), g, d, last, k, hk)

# The loop over the events
# ------------------------

def ri.m_nil(b: Bool, +g: Nat, +d: Nat, +last: Nat, +k: Nat) -> {RetryIdle.drive.sel(ri.asel(b, last, d, ri.came(Nat.is_gt(g, k), g, d, k)), Nil{}, Nat.add(last, g), RetryIdle.drive(Nil{}, d, Nat.add(last, g), RetryIdle.arrive.left(ri.asel(b, last, d, ri.came(Nat.is_gt(g, k), g, d, k))))) == Some{R.idle.sel(b, R.IdleStall{Nat.add(last, d)}, R.idle.go(Nil{}, d, Nat.add(last, g)))} : Maybe<&2, R.Idle>}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def ri.m_cons(b: Bool, +g: Nat, +h: Nat, +t: List<&2, Nat>, +d: Nat, +last: Nat, +k: Nat, ih: {RetryIdle.drive(h <> t, d, Nat.add(last, g), RetryIdle.arrive.left(ri.asel(b, last, d, ri.came(Nat.is_gt(g, k), g, d, k)))) == Some{R.idle.go(h <> t, d, Nat.add(last, g))} : Maybe<&2, R.Idle>}) -> {RetryIdle.drive.sel(ri.asel(b, last, d, ri.came(Nat.is_gt(g, k), g, d, k)), h <> t, Nat.add(last, g), RetryIdle.drive(h <> t, d, Nat.add(last, g), RetryIdle.arrive.left(ri.asel(b, last, d, ri.came(Nat.is_gt(g, k), g, d, k))))) == Some{R.idle.sel(b, R.IdleStall{Nat.add(last, d)}, R.idle.go(h <> t, d, Nat.add(last, g)))} : Maybe<&2, R.Idle>}:
  match b:
    case True{}:
      {==}
    case False{}:
      ih

# the loop ends the events g, rest after last as the idle model does,
# from any timer within the deadline
def ri.drive(rest: List<&2, Nat>, +g: Nat, +d: Nat, +last: Nat, +k: Nat, +hk: {Nat.is_gt(k, d) == False{} : Bool}) -> {RetryIdle.drive(g <> rest, d, last, k) == Some{R.idle.go(g <> rest, d, last)} : Maybe<&2, R.Idle>}:
  match rest:
    case Nil{}:
      %Equal.sym(RetryIdle.Arrive, RetryIdle.arrive(g, d, last, k), ri.arr(g, d, last, k), ri.arrive(g, d, last, k, hk)) : {RetryIdle.drive.sel(_, Nil{}, Nat.add(last, g), RetryIdle.drive(Nil{}, d, Nat.add(last, g), RetryIdle.arrive.left(_))) == Some{R.idle.go(g <> Nil{}, d, last)} : Maybe<&2, R.Idle>}
      ri.m_nil(Nat.is_gt(g, d), g, d, last, k)
    case +h <> +t:
      +ih = ri.drive(t, h, d, Nat.add(last, g), RetryIdle.arrive.left(ri.arr(g, d, last, k)), ri.left_ngt(g, d, last, k, hk))
      %Equal.sym(RetryIdle.Arrive, RetryIdle.arrive(g, d, last, k), ri.arr(g, d, last, k), ri.arrive(g, d, last, k, hk)) : {RetryIdle.drive.sel(_, h <> t, Nat.add(last, g), RetryIdle.drive(h <> t, d, Nat.add(last, g), RetryIdle.arrive.left(_))) == Some{R.idle.go(g <> (h <> t), d, last)} : Maybe<&2, R.Idle>}
      ri.m_cons(Nat.is_gt(g, d), g, h, t, d, last, k, ih)

# The stepper (bend/ffi_retry_idle.bend)
# --------------------------------------

def ri.BD(b: Bool, t: Type, f: Type) -> Type:
  match b:
    case True{}:
      t
    case False{}:
      f

def ri.absurd(-G: Type, h: {False{} == True{} : Bool}) -> G:
  %h : ri.BD(_, G, Unit)
  Unit{}

def ri.and_l(a: Bool, -b: Bool, h: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      h

def ri.and_r(a: Bool, -b: Bool, h: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      h
    case False{}:
      ri.absurd({b == True{} : Bool}, h)

def ri.MD(-A: Data, m: Maybe<&2, A>, G: Type) -> Type:
  match m:
    case None{}:
      Unit
    case Some{x}:
      G

# None is not Some
def ri.none_some(-A: Data, -G: Type, -x: A, h: {None{} == Some{x} : Maybe<&2, A>}) -> G:
  %h : ri.MD(A, _, G)
  Unit{}

def ri.get(-A: Data, m: Maybe<&2, A>, d: A) -> A:
  match m:
    case None{}:
      d
    case Some{x}:
      x

# Some is injective
def ri.some_inj(-A: Data, +a: A, +b: A, h: {Some{a} == Some{b} : Maybe<&2, A>}) -> {a == b : A}:
  Equal.cong(Maybe<&2, A>, A, m => ri.get(A, m, a), Some{a}, Some{b}, h)

def ri.bool_rt(b: Bool, rest: String) -> {Wr.Got{b, rest} == Wr.get_bool(Wr.put_bool(b, rest)) : Wr.Dec<Bool>}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def ri.nat_rt(+n: Nat, rest: String, fits: {LawsBase.wire_fits(n) == True{} : Bool}) -> {Wr.Got{n, rest} == Wr.get_nat(Wr.put_nat(n, rest)) : Wr.Dec<Nat>}:
  Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(n, rest)), Wr.Got{n, rest}, Wire.wire_nat_round_trip(n, rest, fits))

def ri.put_wake(w: R.Wake) -> {RetryIdle.spell_wake(w) == Fi.put_wake(w) : String}:
  match w:
    case R.WakeStall{}:
      {==}
    case R.WakeSleep{us}:
      {==}

# the stepper spells its replies as the laws do
def ri.reply(m: Maybe<&2, R.Wake>) -> {RetryIdle.spell_reply(m) == Fi.put_reply(m) : String}:
  match m:
    case None{}:
      {==}
    case Some{w}:
      %ri.put_wake(w) : {Wr.put_nat(1n, RetryIdle.spell_wake(w)) == Wr.put_nat(1n, _) : String}
      {==}

# the reply of a step is the laws' spelling of the model's step
def ri.reply_pair(p: R.IdleSt & Maybe<&2, R.Wake>) -> {Fi.reply(p) == (Fi.Live{RetryIdle.ri_mst(p)}, RetryIdle.spell_reply(RetryIdle.ri_mans(p))) : Fi.St & String}:
  match p:
    case (s, m):
      %ri.reply(m) : {(Fi.Live{s}, _) == (Fi.Live{s}, RetryIdle.spell_reply(m)) : Fi.St & String}
      {==}

# The model's step, as section 6 states it
# ----------------------------------------

def ri.fired(+d: Nat, +last: Nat, +holds: Nat, w: R.Wake) -> {R.idle.fired(d, last, holds, w) == RetryIdle.step_spec.fire(d, last, holds, w) : R.IdleSt & Maybe<&2, R.Wake>}:
  match w:
    case R.WakeStall{}:
      {==}
    case R.WakeSleep{us}:
      {==}

def ri.fire(+d: Nat, +last: Nat, holds: Nat, +now: Nat) -> {R.idle.fired(d, last, holds, R.idle.wake(R.idle.held(holds), Nat.sub(now, last), d)) == RetryIdle.step_spec.fire(d, last, holds, RetryIdle.wake_spec(Nat.is_gt(holds, 0n), Nat.sub(now, last), d)) : R.IdleSt & Maybe<&2, R.Wake>}:
  match holds:
    case 0n:
      %RetryIdle.idle_wake_exact(False{}, Nat.sub(now, last), d) : {R.idle.fired(d, last, 0n, R.idle.wake(False{}, Nat.sub(now, last), d)) == RetryIdle.step_spec.fire(d, last, 0n, _) : R.IdleSt & Maybe<&2, R.Wake>}
      ri.fired(d, last, 0n, R.idle.wake(False{}, Nat.sub(now, last), d))
    case 1n+p:
      %RetryIdle.idle_wake_exact(True{}, Nat.sub(now, last), d) : {R.idle.fired(d, last, 1n+p, R.idle.wake(True{}, Nat.sub(now, last), d)) == RetryIdle.step_spec.fire(d, last, 1n+p, _) : R.IdleSt & Maybe<&2, R.Wake>}
      ri.fired(d, last, 1n+p, R.idle.wake(True{}, Nat.sub(now, last), d))

def ri.drop(holds: Nat) -> {R.idle.drop(holds) == Nat.sub(holds, 1n) : Nat}:
  match holds:
    case 0n:
      {==}
    case 1n+p:
      Equal.sym(Nat, Nat.sub(p, 0n), p, ri.sub_zero(p))

def ri.live(+d: Nat, +last: Nat, e: R.IdleEv, +holds: Nat) -> {R.idle.live(d, last, holds, e) == RetryIdle.step_spec.live(d, last, holds, e) : R.IdleSt & Maybe<&2, R.Wake>}:
  match e:
    case R.IdleLife{now}:
      {==}
    case R.IdleHold{}:
      {==}
    case R.IdleFree{now}:
      %ri.drop(holds) : {(R.IdleSt{d, Nat.max(last, now), R.idle.drop(holds), False{}}, None{}) == (R.IdleSt{d, Nat.max(last, now), _, False{}}, None{}) : R.IdleSt & Maybe<&2, R.Wake>}
      {==}
    case R.IdleFire{now}:
      ri.fire(d, last, holds, now)

# the model's step is the laws' step_spec
def ri.step(s: R.IdleSt, e: R.IdleEv) -> {R.idle.step(s, e) == RetryIdle.step_spec(s, e) : R.IdleSt & Maybe<&2, R.Wake>}:
  match s:
    case R.IdleSt{d, last, holds, over}:
      match over:
        case True{}:
          {==}
        case False{}:
          ri.live(d, last, e, holds)

# The entry's step
# ----------------

# a spelled event that fits is read whole: the stepper runs the model's step
def ri.ev(s: R.IdleSt, e: R.IdleEv, fits: {RetryIdle.ev_fits(e) == True{} : Bool}) -> {Fi.step(Fi.Live{s}, RetryIdle.spell_ev(e)) == Fi.reply(R.idle.step(s, e)) : Fi.St & String}:
  match e:
    case R.IdleLife{now}:
      %ri.nat_rt(now, "", fits) : {Fi.step.ev(s, Fi.get_ev.life(_)) == Fi.reply(R.idle.step(s, R.IdleLife{now})) : Fi.St & String}
      {==}
    case R.IdleHold{}:
      {==}
    case R.IdleFree{now}:
      %ri.nat_rt(now, "", fits) : {Fi.step.ev(s, Fi.get_ev.free(_)) == Fi.reply(R.idle.step(s, R.IdleFree{now})) : Fi.St & String}
      {==}
    case R.IdleFire{now}:
      %ri.nat_rt(now, "", fits) : {Fi.step.ev(s, Fi.get_ev.fire(_)) == Fi.reply(R.idle.step(s, R.IdleFire{now})) : Fi.St & String}
      {==}

# every spelled event that fits moves the stepper as the model
def ri.model(+s: R.IdleSt, +e: R.IdleEv, fits: {RetryIdle.ev_fits(e) == True{} : Bool}) -> {Fi.step(Fi.Live{s}, RetryIdle.spell_ev(e)) == (Fi.Live{RetryIdle.ri_mst(R.idle.step(s, e))}, RetryIdle.spell_reply(RetryIdle.ri_mans(R.idle.step(s, e)))) : Fi.St & String}:
  Equal.trans(Fi.St & String, Fi.step(Fi.Live{s}, RetryIdle.spell_ev(e)), Fi.reply(R.idle.step(s, e)), (Fi.Live{RetryIdle.ri_mst(R.idle.step(s, e))}, RetryIdle.spell_reply(RetryIdle.ri_mans(R.idle.step(s, e)))), ri.ev(s, e, fits), ri.reply_pair(R.idle.step(s, e)))

# The entry's open
# ----------------

# a spelled open that fits is read whole, one field at a time
def ri.open_spelled(+nan: Bool, +neg: Bool, +whole: Nat, +frac: Bool, +d: Nat, +fits: {Bool.and(LawsBase.wire_fits(whole), LawsBase.wire_fits(d)) == True{} : Bool}) -> {Fi.open(RetryIdle.spell_open(nan, neg, whole, frac, d)) == Fi.open.end(True{}, Fi.Open{nan, neg, whole, frac, d}) : Fi.St & String}:
  %ri.bool_rt(nan, Wr.put_bool(neg, Wr.put_nat(whole, Wr.put_bool(frac, Wr.put_nat(d, ""))))) : {Fi.open.go(Fi.get_open.go(_)) == Fi.open.end(True{}, Fi.Open{nan, neg, whole, frac, d}) : Fi.St & String}
  %ri.bool_rt(neg, Wr.put_nat(whole, Wr.put_bool(frac, Wr.put_nat(d, "")))) : {Fi.open.go(Fi.get_open.neg(nan, _)) == Fi.open.end(True{}, Fi.Open{nan, neg, whole, frac, d}) : Fi.St & String}
  %ri.nat_rt(whole, Wr.put_bool(frac, Wr.put_nat(d, "")), ri.and_l(LawsBase.wire_fits(whole), LawsBase.wire_fits(d), fits)) : {Fi.open.go(Fi.get_open.whole(nan, neg, _)) == Fi.open.end(True{}, Fi.Open{nan, neg, whole, frac, d}) : Fi.St & String}
  %ri.bool_rt(frac, Wr.put_nat(d, "")) : {Fi.open.go(Fi.get_open.frac(nan, neg, whole, _)) == Fi.open.end(True{}, Fi.Open{nan, neg, whole, frac, d}) : Fi.St & String}
  %ri.nat_rt(d, "", ri.and_r(LawsBase.wire_fits(whole), LawsBase.wire_fits(d), fits)) : {Fi.open.go(Fi.get_open.d(nan, neg, whole, frac, _)) == Fi.open.end(True{}, Fi.Open{nan, neg, whole, frac, d}) : Fi.St & String}
  {==}
