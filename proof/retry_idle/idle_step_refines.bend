# eukhe: the proof of LAW idle_step_refines
# The host's loop over the stepper is the loop of `drive` step for step:
# the stepper answers a fire k after the last life at last with the wake
# decision of `drive` ((last + k) - last is k), and a life at last + g
# moves its latest life to last + g (the later of the two). So `sd.run` is
# `drive.run`, which ends every stream as R.idle (idle_wake_refines).

import Base
import ../../bend/retry.bend as R
import ../../laws/retry_idle.bend as RetryIdle
import ./base.bend as LARetryIdle
import ./idle_wake_refines.bend as PIdleWakeRefines

# (last + k) - last is k
def sr.add_sub(last: Nat, +k: Nat) -> {k == Nat.sub(Nat.add(last, k), last) : Nat}:
  match last:
    case 0n:
      Equal.sym(Nat, Nat.sub(k, 0n), k, LARetryIdle.ri.sub_zero(k))
    case 1n+l:
      sr.add_sub(l, k)

# the later of last and last + g is last + g
def sr.max_add(last: Nat, +g: Nat) -> {Nat.add(last, g) == Nat.max(last, Nat.add(last, g)) : Nat}:
  match last:
    case 0n:
      {==}
    case 1n+l:
      Equal.cong(Nat, Nat, x => 1n+x, Nat.add(l, g), Nat.max(l, Nat.add(l, g)), sr.max_add(l, g))

def sr.wake.of(+d: Nat, +last: Nat, w: R.Wake) -> {w == RetryIdle.sd.wake.of(RetryIdle.ri_mans(R.idle.fired(d, last, 0n, w))) : R.Wake}:
  match w:
    case R.WakeStall{}:
      {==}
    case R.WakeSleep{us}:
      {==}

# the stepper answers a fire k after the last life with drive's decision
def sr.wake(+d: Nat, +last: Nat, +k: Nat) -> {R.idle.wake(False{}, k, d) == RetryIdle.sd.wake(d, last, k) : R.Wake}:
  %sr.add_sub(last, k) : {R.idle.wake(False{}, k, d) == RetryIdle.sd.wake.of(RetryIdle.ri_mans(R.idle.fired(d, last, 0n, R.idle.wake(False{}, _, d)))) : R.Wake}
  sr.wake.of(d, last, R.idle.wake(False{}, k, d))

# a life at last + g moves the stepper's latest life there
def sr.life(+d: Nat, +last: Nat, +g: Nat) -> {Nat.add(last, g) == RetryIdle.sd.life(d, last, g) : Nat}:
  sr.max_add(last, g)

def sr.fire2(+last: Nat, +k: Nat, w: R.Wake) -> {RetryIdle.arrive.fire2(last, k, w) == RetryIdle.sd.arrive.fire2(last, k, w) : RetryIdle.Arrive}:
  match w:
    case R.WakeStall{}:
      {==}
    case R.WakeSleep{s}:
      {==}

def sr.after(on: Bool, +g: Nat, +d: Nat, +last: Nat, +k: Nat) -> {RetryIdle.arrive.after(on, g, d, last, k) == RetryIdle.sd.arrive.after(on, g, d, last, k) : RetryIdle.Arrive}:
  match on:
    case False{}:
      {==}
    case True{}:
      %sr.wake(d, last, k) : {RetryIdle.arrive.fire2(last, k, R.idle.wake(False{}, k, d)) == RetryIdle.sd.arrive.fire2(last, k, _) : RetryIdle.Arrive}
      sr.fire2(last, k, R.idle.wake(False{}, k, d))

def sr.fire1(+g: Nat, +d: Nat, +last: Nat, +k: Nat, w: R.Wake) -> {RetryIdle.arrive.fire1(g, d, last, k, w) == RetryIdle.sd.arrive.fire1(g, d, last, k, w) : RetryIdle.Arrive}:
  match w:
    case R.WakeStall{}:
      {==}
    case R.WakeSleep{+s}:
      sr.after(Nat.is_gt(g, Nat.add(k, s)), g, d, last, Nat.add(k, s))

def sr.first(late: Bool, +g: Nat, +d: Nat, +last: Nat, +k: Nat) -> {RetryIdle.arrive.first(late, g, d, last, k) == RetryIdle.sd.arrive.first(late, g, d, last, k) : RetryIdle.Arrive}:
  match late:
    case False{}:
      {==}
    case True{}:
      %sr.wake(d, last, k) : {RetryIdle.arrive.fire1(g, d, last, k, R.idle.wake(False{}, k, d)) == RetryIdle.sd.arrive.fire1(g, d, last, k, _) : RetryIdle.Arrive}
      sr.fire1(g, d, last, k, R.idle.wake(False{}, k, d))

def sr.arrive(+g: Nat, +d: Nat, +last: Nat, +k: Nat) -> {RetryIdle.arrive(g, d, last, k) == RetryIdle.sd.arrive(g, d, last, k) : RetryIdle.Arrive}:
  sr.first(Nat.is_gt(g, k), g, d, last, k)

def sr.sfire2(+last: Nat, +k: Nat, w: R.Wake) -> {RetryIdle.silent.fire2(last, k, w) == RetryIdle.sd.silent.fire2(last, k, w) : Maybe<&2, R.Idle>}:
  match w:
    case R.WakeStall{}:
      {==}
    case R.WakeSleep{s}:
      {==}

def sr.sfire1(+d: Nat, +last: Nat, +k: Nat, w: R.Wake) -> {RetryIdle.silent.fire1(d, last, k, w) == RetryIdle.sd.silent.fire1(d, last, k, w) : Maybe<&2, R.Idle>}:
  match w:
    case R.WakeStall{}:
      {==}
    case R.WakeSleep{+s}:
      %sr.wake(d, last, Nat.add(k, s)) : {RetryIdle.silent.fire2(last, Nat.add(k, s), R.idle.wake(False{}, Nat.add(k, s), d)) == RetryIdle.sd.silent.fire2(last, Nat.add(k, s), _) : Maybe<&2, R.Idle>}
      sr.sfire2(last, Nat.add(k, s), R.idle.wake(False{}, Nat.add(k, s), d))

def sr.silent(+d: Nat, +last: Nat, +k: Nat) -> {RetryIdle.silent(d, last, k) == RetryIdle.sd.silent(d, last, k) : Maybe<&2, R.Idle>}:
  %sr.wake(d, last, k) : {RetryIdle.silent.fire1(d, last, k, R.idle.wake(False{}, k, d)) == RetryIdle.sd.silent.fire1(d, last, k, _) : Maybe<&2, R.Idle>}
  sr.sfire1(d, last, k, R.idle.wake(False{}, k, d))

def sr.drive(gs: List<&2, Nat>, +d: Nat, +last: Nat, +k: Nat) -> {RetryIdle.drive(gs, d, last, k) == RetryIdle.sd.drive(gs, d, last, k) : Maybe<&2, R.Idle>}:
  match gs:
    case Nil{}:
      sr.silent(d, last, k)
    case +g <> +rest:
      %sr.arrive(g, d, last, k) : {RetryIdle.drive.sel(RetryIdle.arrive(g, d, last, k), rest, Nat.add(last, g), RetryIdle.drive(rest, d, Nat.add(last, g), RetryIdle.arrive.left(RetryIdle.arrive(g, d, last, k)))) == RetryIdle.drive.sel(_, rest, RetryIdle.sd.life(d, last, g), RetryIdle.sd.drive(rest, d, RetryIdle.sd.life(d, last, g), RetryIdle.arrive.left(_))) : Maybe<&2, R.Idle>}
      %sr.life(d, last, g) : {RetryIdle.drive.sel(RetryIdle.arrive(g, d, last, k), rest, Nat.add(last, g), RetryIdle.drive(rest, d, Nat.add(last, g), RetryIdle.arrive.left(RetryIdle.arrive(g, d, last, k)))) == RetryIdle.drive.sel(RetryIdle.arrive(g, d, last, k), rest, _, RetryIdle.sd.drive(rest, d, _, RetryIdle.arrive.left(RetryIdle.arrive(g, d, last, k)))) : Maybe<&2, R.Idle>}
      %sr.drive(rest, d, Nat.add(last, g), RetryIdle.arrive.left(RetryIdle.arrive(g, d, last, k))) : {RetryIdle.drive.sel(RetryIdle.arrive(g, d, last, k), rest, Nat.add(last, g), RetryIdle.drive(rest, d, Nat.add(last, g), RetryIdle.arrive.left(RetryIdle.arrive(g, d, last, k)))) == RetryIdle.drive.sel(RetryIdle.arrive(g, d, last, k), rest, Nat.add(last, g), _) : Maybe<&2, R.Idle>}
      {==}

def sr.open(w: R.Wake, gs: List<&2, Nat>, +d: Nat) -> {RetryIdle.drive.start(w, gs, d) == RetryIdle.sd.drive.start(RetryIdle.ri_mans(R.idle.fired(d, 0n, 0n, w)), gs, d) : Maybe<&2, R.Idle>}:
  match w:
    case R.WakeStall{}:
      {==}
    case R.WakeSleep{k}:
      sr.drive(gs, d, 0n, k)

def sr.fin(+gs: List<&2, Nat>, +d: Nat, positive: {Nat.is_gt(d, 0n) == True{} : Bool}) -> {RetryIdle.sd.run(gs, d) == Some{R.idle(gs, d)} : Maybe<&2, R.Idle>}:
  Equal.trans(Maybe<&2, R.Idle>, RetryIdle.sd.run(gs, d), RetryIdle.drive.run(gs, d), Some{R.idle(gs, d)}, Equal.sym(Maybe<&2, R.Idle>, RetryIdle.drive.run(gs, d), RetryIdle.sd.run(gs, d), sr.open(R.idle.wake(False{}, 0n, d), gs, d)), RetryIdle.idle_wake_refines(gs, d, positive))

def RetryIdle.idle_step_refines(gs, d, positive):
  sr.fin(gs, d, positive)
