# eukhe: the proof of LAW retry_idle_open_first
# A spelled 1 ms open is read whole (LA.ri.open_spelled) and arms the
# model's open: its fire at 0 sleeps 1 + e - 0. A deadline of 0 computes to
# a stall, and the stalled state answers every event nothing (so.last of
# idle_stalls_once).
import Base
import ../../bend/ffi_retry_idle.bend as Fi
import ../../bend/retry.bend as R
import ../../bend/wire.bend as Wr
import ../../laws/retry_idle.bend as RetryIdle
import ../../laws/base.bend as LawsBase
import ./base.bend as LA
import ./idle_stalls_once.bend as PSO

def of.first(+e: Nat, +f1: {LawsBase.wire_fits(1n+e) == True{} : Bool}) -> {RetryIdle.ri_reply(Fi.open(RetryIdle.spell_open(False{}, False{}, 1n, False{}, 1n+e))) == RetryIdle.spell_reply(Some{R.WakeSleep{1n+e}}) : String}:
  %Equal.sym(Fi.St & String, Fi.open(RetryIdle.spell_open(False{}, False{}, 1n, False{}, 1n+e)), Fi.open.end(True{}, Fi.Open{False{}, False{}, 1n, False{}, 1n+e}), LA.ri.open_spelled(False{}, False{}, 1n, False{}, 1n+e, f1)) : {RetryIdle.ri_reply(_) == RetryIdle.spell_reply(Some{R.WakeSleep{1n+e}}) : String}
  {==}

def of.go(+e: Nat, +es: List<&2, R.IdleEv>, +ev: R.IdleEv, +fits: {Bool.and(LawsBase.wire_fits(1n+e), RetryIdle.ev_fits(ev)) == True{} : Bool}) -> {RetryIdle.ri_reply(Fi.open(RetryIdle.spell_open(False{}, False{}, 1n, False{}, 1n+e))) == RetryIdle.spell_reply(Some{R.WakeSleep{1n+e}}) : String} & {RetryIdle.ri_reply(Fi.open(RetryIdle.spell_open(False{}, False{}, 1n, False{}, 0n))) == RetryIdle.spell_reply(Some{R.WakeStall{}}) : String} & {RetryIdle.ri_reply(Fi.step(RetryIdle.ri_feed(es, RetryIdle.ri_opened(0n)), RetryIdle.spell_ev(ev))) == RetryIdle.spell_reply(None{}) : String}:
  +f1 = LA.ri.and_l(LawsBase.wire_fits(1n+e), RetryIdle.ev_fits(ev), fits)
  +f2 = LA.ri.and_r(LawsBase.wire_fits(1n+e), RetryIdle.ev_fits(ev), fits)
  (of.first(e, f1), {==}, PSO.so.last(0n, 0n, 0n, es, ev, f2))

def RetryIdle.retry_idle_open_first(e, es, ev, fits):
  of.go(e, es, ev, fits)
