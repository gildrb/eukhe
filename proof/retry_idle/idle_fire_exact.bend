# eukhe: the proof of LAW idle_fire_exact
# The stepper Rust opens with a deadline above 0 is the model's fresh
# deadline (fe.opened). Fed events with no stall answered, it holds the
# deadline, the latest life the events reported and the holds they left
# (fe.inv: a fire that answered no stall slept and kept the state). A fire
# from there answers the model's decision, which is wake_spec's
# (LARetryIdle.ri.fire).

import Base
import ../../bend/ffi_retry_idle.bend as Fi
import ../../bend/retry.bend as R
import ../../bend/wire.bend as Wr
import ../../laws/retry_idle.bend as RetryIdle
import ../../laws/base.bend as LawsBase
import ./base.bend as LA

# the stepper Rust opens with a deadline above 0
def fe.opened(+d: Nat, fits: {LawsBase.wire_fits(d) == True{} : Bool}, positive: {Nat.is_gt(d, 0n) == True{} : Bool}) -> {Fi.Live{R.IdleSt{d, 0n, 0n, False{}}} == RetryIdle.ri_opened(d) : Fi.St}:
  %Equal.sym(Fi.St & String, Fi.open(RetryIdle.spell_open(False{}, False{}, 1n, False{}, d)), Fi.open.end(True{}, Fi.Open{False{}, False{}, 1n, False{}, d}), LA.ri.open_spelled(False{}, False{}, 1n, False{}, d, fits)) : {Fi.Live{R.IdleSt{d, 0n, 0n, False{}}} == RetryIdle.ri_state(_) : Fi.St}
  %Equal.sym(Bool, Nat.is_gt(d, 0n), True{}, positive) : {Fi.Live{R.IdleSt{d, 0n, 0n, False{}}} == RetryIdle.ri_state(Fi.reply(R.idle.fired(d, 0n, 0n, R.idle.wake.sel(_, Nat.sub(d, 0n))))) : Fi.St}
  {==}

# a fire that answered no stall slept, and kept the state
def fe.slept(w: R.Wake, +d: Nat, +l: Nat, +h: Nat, q: {Bool.not(String.eq(RetryIdle.ri_reply(Fi.reply(R.idle.fired(d, l, h, w))), "1,0,")) == True{} : Bool}) -> {Fi.Live{R.IdleSt{d, l, h, False{}}} == RetryIdle.ri_state(Fi.reply(R.idle.fired(d, l, h, w))) : Fi.St}:
  match w:
    case R.WakeStall{}:
      LA.ri.absurd({Fi.Live{R.IdleSt{d, l, h, False{}}} == RetryIdle.ri_state(Fi.reply(R.idle.fired(d, l, h, R.WakeStall{}))) : Fi.St}, q)
    case R.WakeSleep{us}:
      {==}

# the quiet premise, read after the model's step: its reply was no stall
def fe.qa(+s: R.IdleSt, +e: R.IdleEv, -rest: List<&2, R.IdleEv>, fits: {RetryIdle.ev_fits(e) == True{} : Bool}, quiet: {RetryIdle.ri_quiet(e <> rest, Fi.Live{s}) == True{} : Bool}) -> {Bool.not(String.eq(RetryIdle.ri_reply(Fi.reply(R.idle.step(s, e))), "1,0,")) == True{} : Bool}:
  Equal.trans(Bool, Bool.not(String.eq(RetryIdle.ri_reply(Fi.reply(R.idle.step(s, e))), "1,0,")), Bool.not(String.eq(RetryIdle.ri_reply(Fi.step(Fi.Live{s}, RetryIdle.spell_ev(e))), "1,0,")), True{}, Equal.cong(Fi.St & String, Bool, x => Bool.not(String.eq(RetryIdle.ri_reply(x), "1,0,")), Fi.reply(R.idle.step(s, e)), Fi.step(Fi.Live{s}, RetryIdle.spell_ev(e)), Equal.sym(Fi.St & String, Fi.step(Fi.Live{s}, RetryIdle.spell_ev(e)), Fi.reply(R.idle.step(s, e)), LA.ri.ev(s, e, fits))), LA.ri.and_l(Bool.not(String.eq(RetryIdle.ri_reply(Fi.step(Fi.Live{s}, RetryIdle.spell_ev(e))), "1,0,")), RetryIdle.ri_quiet(rest, RetryIdle.ri_state(Fi.step(Fi.Live{s}, RetryIdle.spell_ev(e)))), quiet))

# the quiet premise, read after the model's step: the rest is quiet
def fe.qb(+s: R.IdleSt, +e: R.IdleEv, +rest: List<&2, R.IdleEv>, fits: {RetryIdle.ev_fits(e) == True{} : Bool}, quiet: {RetryIdle.ri_quiet(e <> rest, Fi.Live{s}) == True{} : Bool}) -> {RetryIdle.ri_quiet(rest, RetryIdle.ri_state(Fi.reply(R.idle.step(s, e)))) == True{} : Bool}:
  Equal.trans(Bool, RetryIdle.ri_quiet(rest, RetryIdle.ri_state(Fi.reply(R.idle.step(s, e)))), RetryIdle.ri_quiet(rest, RetryIdle.ri_state(Fi.step(Fi.Live{s}, RetryIdle.spell_ev(e)))), True{}, Equal.cong(Fi.St & String, Bool, x => RetryIdle.ri_quiet(rest, RetryIdle.ri_state(x)), Fi.reply(R.idle.step(s, e)), Fi.step(Fi.Live{s}, RetryIdle.spell_ev(e)), Equal.sym(Fi.St & String, Fi.step(Fi.Live{s}, RetryIdle.spell_ev(e)), Fi.reply(R.idle.step(s, e)), LA.ri.ev(s, e, fits))), LA.ri.and_r(Bool.not(String.eq(RetryIdle.ri_reply(Fi.step(Fi.Live{s}, RetryIdle.spell_ev(e))), "1,0,")), RetryIdle.ri_quiet(rest, RetryIdle.ri_state(Fi.step(Fi.Live{s}, RetryIdle.spell_ev(e)))), quiet))

# fed quiet events, the stepper holds the latest life and the holds they
# report
def fe.inv(pre: List<&2, R.IdleEv>, +d: Nat, +l: Nat, +h: Nat, +fits: {RetryIdle.evs_fit(pre) == True{} : Bool}, +quiet: {RetryIdle.ri_quiet(pre, Fi.Live{R.IdleSt{d, l, h, False{}}}) == True{} : Bool}) -> {Fi.Live{R.IdleSt{d, RetryIdle.ri_latest(pre, l), RetryIdle.ri_holds(pre, h), False{}}} == RetryIdle.ri_feed(pre, Fi.Live{R.IdleSt{d, l, h, False{}}}) : Fi.St}:
  match pre:
    case Nil{}:
      {==}
    case +e <> +rest:
      match e:
        case R.IdleLife{+now}:
          +fe1 = LA.ri.and_l(RetryIdle.ev_fits(R.IdleLife{now}), RetryIdle.evs_fit(rest), fits)
          +q = fe.qb(R.IdleSt{d, l, h, False{}}, R.IdleLife{now}, rest, fe1, quiet)
          %Equal.sym(Fi.St & String, Fi.step(Fi.Live{R.IdleSt{d, l, h, False{}}}, RetryIdle.spell_ev(R.IdleLife{now})), Fi.reply(R.idle.step(R.IdleSt{d, l, h, False{}}, R.IdleLife{now})), LA.ri.ev(R.IdleSt{d, l, h, False{}}, R.IdleLife{now}, fe1)) : {Fi.Live{R.IdleSt{d, RetryIdle.ri_latest(rest, Nat.max(l, now)), RetryIdle.ri_holds(rest, h), False{}}} == RetryIdle.ri_feed(rest, RetryIdle.ri_state(_)) : Fi.St}
          fe.inv(rest, d, Nat.max(l, now), h, LA.ri.and_r(RetryIdle.ev_fits(R.IdleLife{now}), RetryIdle.evs_fit(rest), fits), q)
        case R.IdleHold{}:
          +q = fe.qb(R.IdleSt{d, l, h, False{}}, R.IdleHold{}, rest, {==}, quiet)
          fe.inv(rest, d, l, 1n+h, LA.ri.and_r(True{}, RetryIdle.evs_fit(rest), fits), q)
        case R.IdleFree{+now}:
          +fe1 = LA.ri.and_l(RetryIdle.ev_fits(R.IdleFree{now}), RetryIdle.evs_fit(rest), fits)
          +q = fe.qb(R.IdleSt{d, l, h, False{}}, R.IdleFree{now}, rest, fe1, quiet)
          %Equal.sym(Fi.St & String, Fi.step(Fi.Live{R.IdleSt{d, l, h, False{}}}, RetryIdle.spell_ev(R.IdleFree{now})), Fi.reply(R.idle.step(R.IdleSt{d, l, h, False{}}, R.IdleFree{now})), LA.ri.ev(R.IdleSt{d, l, h, False{}}, R.IdleFree{now}, fe1)) : {Fi.Live{R.IdleSt{d, RetryIdle.ri_latest(rest, Nat.max(l, now)), RetryIdle.ri_holds(rest, Nat.sub(h, 1n)), False{}}} == RetryIdle.ri_feed(rest, RetryIdle.ri_state(_)) : Fi.St}
          %LA.ri.drop(h) : {Fi.Live{R.IdleSt{d, RetryIdle.ri_latest(rest, Nat.max(l, now)), RetryIdle.ri_holds(rest, _), False{}}} == RetryIdle.ri_feed(rest, Fi.Live{R.IdleSt{d, Nat.max(l, now), R.idle.drop(h), False{}}}) : Fi.St}
          fe.inv(rest, d, Nat.max(l, now), R.idle.drop(h), LA.ri.and_r(RetryIdle.ev_fits(R.IdleFree{now}), RetryIdle.evs_fit(rest), fits), q)
        case R.IdleFire{+now}:
          +fe1 = LA.ri.and_l(RetryIdle.ev_fits(R.IdleFire{now}), RetryIdle.evs_fit(rest), fits)
          +w = R.idle.wake(R.idle.held(h), Nat.sub(now, l), d)
          +kept = fe.slept(w, d, l, h, fe.qa(R.IdleSt{d, l, h, False{}}, R.IdleFire{now}, rest, fe1, quiet))
          +q2 = Equal.trans(Bool, RetryIdle.ri_quiet(rest, Fi.Live{R.IdleSt{d, l, h, False{}}}), RetryIdle.ri_quiet(rest, RetryIdle.ri_state(Fi.reply(R.idle.fired(d, l, h, w)))), True{}, Equal.cong(Fi.St, Bool, x => RetryIdle.ri_quiet(rest, x), Fi.Live{R.IdleSt{d, l, h, False{}}}, RetryIdle.ri_state(Fi.reply(R.idle.fired(d, l, h, w))), kept), fe.qb(R.IdleSt{d, l, h, False{}}, R.IdleFire{now}, rest, fe1, quiet))
          %Equal.sym(Fi.St & String, Fi.step(Fi.Live{R.IdleSt{d, l, h, False{}}}, RetryIdle.spell_ev(R.IdleFire{now})), Fi.reply(R.idle.step(R.IdleSt{d, l, h, False{}}, R.IdleFire{now})), LA.ri.ev(R.IdleSt{d, l, h, False{}}, R.IdleFire{now}, fe1)) : {Fi.Live{R.IdleSt{d, RetryIdle.ri_latest(rest, l), RetryIdle.ri_holds(rest, h), False{}}} == RetryIdle.ri_feed(rest, RetryIdle.ri_state(_)) : Fi.St}
          %kept : {Fi.Live{R.IdleSt{d, RetryIdle.ri_latest(rest, l), RetryIdle.ri_holds(rest, h), False{}}} == RetryIdle.ri_feed(rest, _) : Fi.St}
          fe.inv(rest, d, l, h, LA.ri.and_r(RetryIdle.ev_fits(R.IdleFire{now}), RetryIdle.evs_fit(rest), fits), q2)

# the reply to a fire: the timer's decision, spelled
def fe.last(+d: Nat, +l: Nat, +h: Nat, w: R.Wake) -> {RetryIdle.ri_reply(Fi.reply(RetryIdle.step_spec.fire(d, l, h, w))) == RetryIdle.spell_reply(Some{w}) : String}:
  match w:
    case R.WakeStall{}:
      {==}
    case R.WakeSleep{us}:
      {==}

def fe.go(+d: Nat, +pre: List<&2, R.IdleEv>, +now: Nat, +fits: {Bool.and(LawsBase.wire_fits(d), Bool.and(LawsBase.wire_fits(now), RetryIdle.evs_fit(pre))) == True{} : Bool}, +positive: {Nat.is_gt(d, 0n) == True{} : Bool}, quiet: {RetryIdle.ri_quiet(pre, RetryIdle.ri_opened(d)) == True{} : Bool}) -> {RetryIdle.ri_reply(Fi.step(RetryIdle.ri_feed(pre, RetryIdle.ri_opened(d)), RetryIdle.spell_ev(R.IdleFire{now}))) == RetryIdle.spell_reply(Some{RetryIdle.wake_spec(Nat.is_gt(RetryIdle.ri_holds(pre, 0n), 0n), Nat.sub(now, RetryIdle.ri_latest(pre, 0n)), d)}) : String}:
  +fd = LA.ri.and_l(LawsBase.wire_fits(d), Bool.and(LawsBase.wire_fits(now), RetryIdle.evs_fit(pre)), fits)
  +fr = LA.ri.and_r(LawsBase.wire_fits(d), Bool.and(LawsBase.wire_fits(now), RetryIdle.evs_fit(pre)), fits)
  +opened = fe.opened(d, fd, positive)
  +q = Equal.trans(Bool, RetryIdle.ri_quiet(pre, Fi.Live{R.IdleSt{d, 0n, 0n, False{}}}), RetryIdle.ri_quiet(pre, RetryIdle.ri_opened(d)), True{}, Equal.cong(Fi.St, Bool, x => RetryIdle.ri_quiet(pre, x), Fi.Live{R.IdleSt{d, 0n, 0n, False{}}}, RetryIdle.ri_opened(d), opened), quiet)
  +lp = RetryIdle.ri_latest(pre, 0n)
  +hp = RetryIdle.ri_holds(pre, 0n)
  %opened : {RetryIdle.ri_reply(Fi.step(RetryIdle.ri_feed(pre, _), RetryIdle.spell_ev(R.IdleFire{now}))) == RetryIdle.spell_reply(Some{RetryIdle.wake_spec(Nat.is_gt(hp, 0n), Nat.sub(now, lp), d)}) : String}
  %fe.inv(pre, d, 0n, 0n, LA.ri.and_r(LawsBase.wire_fits(now), RetryIdle.evs_fit(pre), fr), q) : {RetryIdle.ri_reply(Fi.step(_, RetryIdle.spell_ev(R.IdleFire{now}))) == RetryIdle.spell_reply(Some{RetryIdle.wake_spec(Nat.is_gt(hp, 0n), Nat.sub(now, lp), d)}) : String}
  %Equal.sym(Fi.St & String, Fi.step(Fi.Live{R.IdleSt{d, lp, hp, False{}}}, RetryIdle.spell_ev(R.IdleFire{now})), Fi.reply(R.idle.step(R.IdleSt{d, lp, hp, False{}}, R.IdleFire{now})), LA.ri.ev(R.IdleSt{d, lp, hp, False{}}, R.IdleFire{now}, LA.ri.and_l(LawsBase.wire_fits(now), RetryIdle.evs_fit(pre), fr))) : {RetryIdle.ri_reply(_) == RetryIdle.spell_reply(Some{RetryIdle.wake_spec(Nat.is_gt(hp, 0n), Nat.sub(now, lp), d)}) : String}
  %Equal.sym(R.IdleSt & Maybe<&2, R.Wake>, R.idle.fired(d, lp, hp, R.idle.wake(R.idle.held(hp), Nat.sub(now, lp), d)), RetryIdle.step_spec.fire(d, lp, hp, RetryIdle.wake_spec(Nat.is_gt(hp, 0n), Nat.sub(now, lp), d)), LA.ri.fire(d, lp, hp, now)) : {RetryIdle.ri_reply(Fi.reply(_)) == RetryIdle.spell_reply(Some{RetryIdle.wake_spec(Nat.is_gt(hp, 0n), Nat.sub(now, lp), d)}) : String}
  fe.last(d, lp, hp, RetryIdle.wake_spec(Nat.is_gt(hp, 0n), Nat.sub(now, lp), d))

def RetryIdle.idle_fire_exact(d, pre, now, fits, positive, quiet):
  fe.go(d, pre, now, fits, positive, quiet)
