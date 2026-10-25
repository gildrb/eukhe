# eukhe: the proof of LAW retry_idle_entry_reads
# The entry reads every event as the laws' reader does, one field at a
# time, and runs the model's step on it; a spelled event is read whole
# too (LA.ri.ev).
import Base
import ../../bend/ffi_retry_idle.bend as Fi
import ../../bend/retry.bend as R
import ../../bend/wire.bend as Wr
import ../../laws/retry_idle.bend as RetryIdle
import ./base.bend as LA

def rd.fin(b: Bool, e0: R.IdleEv, +s: R.IdleSt, +e: R.IdleEv, got: {RetryIdle.read_ev.fin(b, e0) == Some{e} : Maybe<&2, R.IdleEv>}) -> {Fi.step.end(b, s, e0) == Fi.reply(R.idle.step(s, e)) : Fi.St & String}:
  match b:
    case True{}:
      %LA.ri.some_inj(R.IdleEv, e0, e, got) : {Fi.step.end(True{}, s, e0) == Fi.reply(R.idle.step(s, _)) : Fi.St & String}
      {==}
    case False{}:
      LA.ri.none_some(R.IdleEv, {(Fi.Live{s}, Fi.fail()) == Fi.reply(R.idle.step(s, e)) : Fi.St & String}, e, got)

def rd.life(r: Wr.Dec<Nat>, +s: R.IdleSt, +e: R.IdleEv, got: {RetryIdle.read_ev.life(r) == Some{e} : Maybe<&2, R.IdleEv>}) -> {Fi.step.ev(s, Fi.get_ev.life(r)) == Fi.reply(R.idle.step(s, e)) : Fi.St & String}:
  match r:
    case Wr.Got{now, rest}:
      rd.fin(Wr.end(rest), R.IdleLife{now}, s, e, got)
    case Wr.Bad{}:
      LA.ri.none_some(R.IdleEv, {(Fi.Live{s}, Fi.fail()) == Fi.reply(R.idle.step(s, e)) : Fi.St & String}, e, got)

def rd.free(r: Wr.Dec<Nat>, +s: R.IdleSt, +e: R.IdleEv, got: {RetryIdle.read_ev.free(r) == Some{e} : Maybe<&2, R.IdleEv>}) -> {Fi.step.ev(s, Fi.get_ev.free(r)) == Fi.reply(R.idle.step(s, e)) : Fi.St & String}:
  match r:
    case Wr.Got{now, rest}:
      rd.fin(Wr.end(rest), R.IdleFree{now}, s, e, got)
    case Wr.Bad{}:
      LA.ri.none_some(R.IdleEv, {(Fi.Live{s}, Fi.fail()) == Fi.reply(R.idle.step(s, e)) : Fi.St & String}, e, got)

def rd.fire(r: Wr.Dec<Nat>, +s: R.IdleSt, +e: R.IdleEv, got: {RetryIdle.read_ev.fire(r) == Some{e} : Maybe<&2, R.IdleEv>}) -> {Fi.step.ev(s, Fi.get_ev.fire(r)) == Fi.reply(R.idle.step(s, e)) : Fi.St & String}:
  match r:
    case Wr.Got{now, rest}:
      rd.fin(Wr.end(rest), R.IdleFire{now}, s, e, got)
    case Wr.Bad{}:
      LA.ri.none_some(R.IdleEv, {(Fi.Live{s}, Fi.fail()) == Fi.reply(R.idle.step(s, e)) : Fi.St & String}, e, got)

def rd.tag(t: Nat, rest: String, +s: R.IdleSt, +e: R.IdleEv, got: {RetryIdle.read_ev.tag(t, rest) == Some{e} : Maybe<&2, R.IdleEv>}) -> {Fi.step.ev(s, Fi.get_ev.tag(t, rest)) == Fi.reply(R.idle.step(s, e)) : Fi.St & String}:
  match t:
    case 0n:
      rd.life(Wr.get_nat(rest), s, e, got)
    case 1n:
      rd.fin(Wr.end(rest), R.IdleHold{}, s, e, got)
    case 2n:
      rd.free(Wr.get_nat(rest), s, e, got)
    case 3n:
      rd.fire(Wr.get_nat(rest), s, e, got)
    case 4n+p:
      LA.ri.none_some(R.IdleEv, {(Fi.Live{s}, Fi.fail()) == Fi.reply(R.idle.step(s, e)) : Fi.St & String}, e, got)

def rd.go(r: Wr.Dec<Nat>, +s: R.IdleSt, +e: R.IdleEv, got: {RetryIdle.read_ev.go(r) == Some{e} : Maybe<&2, R.IdleEv>}) -> {Fi.step.ev(s, Fi.get_ev.go(r)) == Fi.reply(R.idle.step(s, e)) : Fi.St & String}:
  match r:
    case Wr.Got{t, rest}:
      rd.tag(t, rest, s, e, got)
    case Wr.Bad{}:
      LA.ri.none_some(R.IdleEv, {(Fi.Live{s}, Fi.fail()) == Fi.reply(R.idle.step(s, e)) : Fi.St & String}, e, got)

def RetryIdle.retry_idle_entry_reads(s, i, e, got, fits):
  Equal.trans(Fi.St & String, Fi.step(Fi.Live{s}, i), Fi.reply(R.idle.step(s, e)), Fi.step(Fi.Live{s}, RetryIdle.spell_ev(e)), rd.go(Wr.get_nat(i), s, e, got), Equal.sym(Fi.St & String, Fi.step(Fi.Live{s}, RetryIdle.spell_ev(e)), Fi.reply(R.idle.step(s, e)), LA.ri.ev(s, e, fits)))
