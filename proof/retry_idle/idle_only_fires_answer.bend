# eukhe: the proof of LAW idle_only_fires_answer
# Each event is read whole (LARetryIdle.ri.ev); the model answers none
# to a life, a hold and the end of a hold, ended or not.

import Base
import ../../bend/ffi_retry_idle.bend as Fi
import ../../bend/retry.bend as R
import ../../bend/wire.bend as Wr
import ../../laws/retry_idle.bend as RetryIdle
import ../../laws/base.bend as LawsBase
import ./base.bend as LARetryIdle

def ofa.go(s: R.IdleSt, +now: Nat) -> {[RetryIdle.ri_reply(Fi.reply(R.idle.step(s, R.IdleLife{now}))), RetryIdle.ri_reply(Fi.reply(R.idle.step(s, R.IdleHold{}))), RetryIdle.ri_reply(Fi.reply(R.idle.step(s, R.IdleFree{now})))] == ["0,", "0,", "0,"] : List<&2, String>}:
  match s:
    case R.IdleSt{d, last, holds, over}:
      match over:
        case True{}:
          {==}
        case False{}:
          {==}

def ofa.all(+s: R.IdleSt, +now: Nat, +fits: {LawsBase.wire_fits(now) == True{} : Bool}) -> {[RetryIdle.ri_reply(Fi.step(Fi.Live{s}, RetryIdle.spell_ev(R.IdleLife{now}))), RetryIdle.ri_reply(Fi.step(Fi.Live{s}, RetryIdle.spell_ev(R.IdleHold{}))), RetryIdle.ri_reply(Fi.step(Fi.Live{s}, RetryIdle.spell_ev(R.IdleFree{now})))] == ["0,", "0,", "0,"] : List<&2, String>}:
  %Equal.sym(Fi.St & String, Fi.step(Fi.Live{s}, RetryIdle.spell_ev(R.IdleLife{now})), Fi.reply(R.idle.step(s, R.IdleLife{now})), LARetryIdle.ri.ev(s, R.IdleLife{now}, fits)) : {[RetryIdle.ri_reply(_), RetryIdle.ri_reply(Fi.step(Fi.Live{s}, RetryIdle.spell_ev(R.IdleHold{}))), RetryIdle.ri_reply(Fi.step(Fi.Live{s}, RetryIdle.spell_ev(R.IdleFree{now})))] == ["0,", "0,", "0,"] : List<&2, String>}
  %Equal.sym(Fi.St & String, Fi.step(Fi.Live{s}, RetryIdle.spell_ev(R.IdleFree{now})), Fi.reply(R.idle.step(s, R.IdleFree{now})), LARetryIdle.ri.ev(s, R.IdleFree{now}, fits)) : {[RetryIdle.ri_reply(Fi.reply(R.idle.step(s, R.IdleLife{now}))), RetryIdle.ri_reply(Fi.step(Fi.Live{s}, RetryIdle.spell_ev(R.IdleHold{}))), RetryIdle.ri_reply(_)] == ["0,", "0,", "0,"] : List<&2, String>}
  ofa.go(s, now)

def RetryIdle.idle_only_fires_answer(s, now, fits):
  ofa.all(s, now, fits)
