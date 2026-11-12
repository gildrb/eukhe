# eukhe: the proof of LAW idle_fire_total
# A held clock: a sleep of a whole d. A free one: before the deadline, a
# sleep of what is left (since + (d - since) = d: LA.ri.add_sub); at or
# past it, a stall (LA.ri.nlt_le).

import Base
import ../../bend/retry.bend as R
import ../../laws/retry_idle.bend as RetryIdle
import ./base.bend as LA

# before the deadline: a sleep of what is left is right
def ft.sleep(+since: Nat, +d: Nat, +hl: {Nat.is_lt(since, d) == True{} : Bool}) -> {RetryIdle.fire_ok(False{}, since, d, R.WakeSleep{Nat.sub(d, since)}) == True{} : Bool}:
  %Equal.sym(Bool, Nat.is_lt(since, d), True{}, hl) : {Bool.and(_, Nat.is_eq(Nat.add(since, Nat.sub(d, since)), d)) == True{} : Bool}
  %Equal.sym(Nat, Nat.add(since, Nat.sub(d, since)), d, LA.ri.add_sub(since, d, Equal.trans(Bool, Nat.is_gt(d, since), Nat.is_lt(since, d), True{}, Equal.sym(Bool, Nat.is_lt(since, d), Nat.is_gt(d, since), LA.ri.flip(since, d)), hl))) : {Bool.and(True{}, Nat.is_eq(_, d)) == True{} : Bool}
  LA.ri.eq_refl(d)

def ft.free(b: Bool, +since: Nat, +d: Nat, hb: {Nat.is_lt(since, d) == b : Bool}) -> Sigma<&1, &1, R.Wake, w => {RetryIdle.fire_ok(False{}, since, d, w) == True{} : Bool}>:
  match b:
    case True{}:
      (R.WakeSleep{Nat.sub(d, since)}, ft.sleep(since, d, hb))
    case False{}:
      (R.WakeStall{}, LA.ri.nlt_le(since, d, hb))

def RetryIdle.idle_fire_total(held, since, d):
  match held:
    case True{}:
      (R.WakeSleep{d}, LA.ri.eq_refl(d))
    case False{}:
      ft.free(Nat.is_lt(since, d), since, d, {==})
