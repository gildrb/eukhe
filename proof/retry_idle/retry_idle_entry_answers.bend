# eukhe: the proof of LAW retry_idle_entry_answers
# Each field of a spelled request reads back (a Bool by its two cases, a
# Nat that fits by the wire's round trip); the entry then answers the
# model's decision, which is the spec's (idle_arm_exact, idle_wake_exact).

import Base
import ../../bend/ffi_retry_idle.bend as Fi
import ../../bend/retry.bend as R
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/retry_idle.bend as RetryIdle
import ../base/logic/bool.bend as LLogicBool
import ../base/wire.bend as LWire
import ./base.bend as LARetryIdle
import ./idle_arm_exact.bend as PIdleArmExact
import ./idle_wake_exact.bend as PIdleWakeExact

def ra.arm(+nan: Bool, +neg: Bool, +whole: Nat, +frac: Bool, fits: {LawsBase.wire_fits(whole) == True{} : Bool}) -> {Fi.ffi(RetryIdle.spell_ask(RetryIdle.idle.AskArm{nan, neg, whole, frac})) == RetryIdle.spell_answer(RetryIdle.idle.AskArm{nan, neg, whole, frac}) : String}:
  %LARetryIdle.ri.bool_rt(nan, Wr.put_bool(neg, Wr.put_nat(whole, Wr.put_bool(frac, "")))) : {Fi.run(Fi.get_arm(_)) == RetryIdle.spell_answer(RetryIdle.idle.AskArm{nan, neg, whole, frac}) : String}
  %LARetryIdle.ri.bool_rt(neg, Wr.put_nat(whole, Wr.put_bool(frac, ""))) : {Fi.run(Fi.get_arm.neg(nan, _)) == RetryIdle.spell_answer(RetryIdle.idle.AskArm{nan, neg, whole, frac}) : String}
  %LWire.pc.nat(whole, Wr.put_bool(frac, ""), fits) : {Fi.run(Fi.get_arm.whole(nan, neg, _)) == RetryIdle.spell_answer(RetryIdle.idle.AskArm{nan, neg, whole, frac}) : String}
  %LARetryIdle.ri.bool_rt(frac, "") : {Fi.run(Fi.get_arm.frac(nan, neg, whole, _)) == RetryIdle.spell_answer(RetryIdle.idle.AskArm{nan, neg, whole, frac}) : String}
  Equal.cong(Bool, String, b => Wr.put_bool(b, ""), R.idle.arm(nan, neg, whole, frac), RetryIdle.arm_spec(nan, neg, whole, frac), RetryIdle.idle_arm_exact(nan, neg, whole, frac))

def ra.wake(+held: Bool, +since: Nat, +d: Nat, +fits: {Bool.and(LawsBase.wire_fits(since), LawsBase.wire_fits(d)) == True{} : Bool}) -> {Fi.ffi(RetryIdle.spell_ask(RetryIdle.idle.AskWake{held, since, d})) == RetryIdle.spell_answer(RetryIdle.idle.AskWake{held, since, d}) : String}:
  %LARetryIdle.ri.bool_rt(held, Wr.put_nat(since, Wr.put_nat(d, ""))) : {Fi.run(Fi.get_wake(_)) == RetryIdle.spell_answer(RetryIdle.idle.AskWake{held, since, d}) : String}
  %LWire.pc.nat(since, Wr.put_nat(d, ""), LLogicBool.wr_and_l(LawsBase.wire_fits(since), LawsBase.wire_fits(d), fits)) : {Fi.run(Fi.get_wake.since(held, _)) == RetryIdle.spell_answer(RetryIdle.idle.AskWake{held, since, d}) : String}
  %LWire.pc.nat(d, "", LLogicBool.wr_and_r(LawsBase.wire_fits(since), LawsBase.wire_fits(d), fits)) : {Fi.run(Fi.get_wake.d(held, since, _)) == RetryIdle.spell_answer(RetryIdle.idle.AskWake{held, since, d}) : String}
  %Equal.sym(R.Wake, R.idle.wake(held, since, d), RetryIdle.wake_spec(held, since, d), RetryIdle.idle_wake_exact(held, since, d)) : {Fi.put_wake(_) == RetryIdle.spell_wake(RetryIdle.wake_spec(held, since, d)) : String}
  LARetryIdle.ri.put_wake(RetryIdle.wake_spec(held, since, d))

def RetryIdle.retry_idle_entry_answers(a, fits):
  match a:
    case RetryIdle.idle.AskArm{nan, neg, whole, frac}:
      ra.arm(nan, neg, whole, frac, fits)
    case RetryIdle.idle.AskWake{held, since, d}:
      ra.wake(held, since, d, fits)
