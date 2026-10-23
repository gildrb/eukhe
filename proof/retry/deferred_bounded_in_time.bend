# eukhe: the proof of LAW deferred_bounded_in_time

import Base
import ../../bend/retry.bend as R
import ../../laws/retry.bend as Retry
import ../base.bend as L
import ./base.bend as LA

def rp.late_off(a: R.Act, +left: Nat) -> {R.tally.late(a, left, False{}) == 0n : Nat}:
  match a:
    case R.Send{}:
      {==}
    case R.Poll{}:
      {==}
    case R.Cancel{}:
      {==}
    case R.Settle{}:
      {==}
    case R.Quit{}:
      {==}

def rp.pending_late(over: Bool, left: Nat, +gap: Nat, e: {Nat.is_eq(left, 0n) == over : Bool}) -> {R.tally.late(R.Step.act(R.live.pending(over, left, gap)), left, True{}) == 0n : Nat}:
  match over left:
    case True{} l:
      {==}
    case False{} 0n:
      L.rp.absurdT({R.late.at(0n) == 0n : Nat}, e)
    case False{} 1n+k:
      {==}

def rp.failed_late(again: Bool, r: Bool, +failed: Nat, +fails: Nat, left: Nat, +gap: Nat, e: {Bool.and(r, Bool.and(Nat.is_lt(failed, fails), Nat.is_gt(left, 0n))) == again : Bool}) -> {R.tally.late(R.Step.act(R.live.failed(again, failed, left, gap)), left, True{}) == 0n : Nat}:
  match again left:
    case False{} l:
      {==}
    case True{} 0n:
      L.rp.absurdF({R.late.at(0n) == 0n : Nat}, L.rp.and_r(Nat.is_lt(failed, fails), False{}, L.rp.and_r(r, Bool.and(Nat.is_lt(failed, fails), False{}), e)))
    case True{} 1n+k:
      {==}

# a step never polls a live job with 0 ms left
def rp.step_late(+fails: Nat, +budget: Nat, job: R.Job, g: R.Got) -> {R.tally.late(R.Step.act(R.step(fails, budget, job, g)), R.Job.left(job), R.Job.live(job)) == 0n : Nat}:
  match job:
    case R.NoJob{}:
      rp.late_off(R.Step.act(R.step(fails, budget, R.NoJob{}, g)), 0n)
    case R.Live{+failed, +left}:
      match g:
        case R.Answer{}:
          {==}
        case R.Later{+gap}:
          rp.pending_late(Nat.is_eq(left, 0n), left, gap, {==})
        case R.Broke{+r, +gap}:
          rp.failed_late(Bool.and(r, Bool.and(Nat.is_lt(failed, fails), Nat.is_gt(left, 0n))), r, failed, fails, left, gap, {==})

def rp.late_go(gots: List<&2, R.Got>, +fails: Nat, +budget: Nat, +job: R.Job, +s: Nat, +l: Nat) -> {R.Tally.late(R.run.go(gots, fails, budget, job, R.Tally{s, l})) == l : Nat}:
  match gots:
    case Nil{}:
      {==}
    case +g <> +rest:
      +x = R.tally.send(R.Step.act(R.step(fails, budget, job, g)), R.Job.live(job))
      +y = R.tally.late(R.Step.act(R.step(fails, budget, job, g)), R.Job.left(job), R.Job.live(job))
      Equal.trans(Nat, R.Tally.late(R.run.go(rest, fails, budget, R.Step.job(R.step(fails, budget, job, g)), R.Tally{Nat.add(s, x), Nat.add(l, y)})), Nat.add(l, y), l, rp.late_go(rest, fails, budget, R.Step.job(R.step(fails, budget, job, g)), Nat.add(s, x), Nat.add(l, y)), LA.rp.add_none(l, y, rp.step_late(fails, budget, job, g)))

def bounded_in_time(+fails: Nat, +budget: Nat, gots: List<&2, R.Got>) -> {R.Tally.late(R.run(fails, budget, gots)) == 0n : Nat}:
  rp.late_go(gots, fails, budget, R.NoJob{}, 0n, 0n)

def Retry.deferred_bounded_in_time(fails, budget, gots):
  bounded_in_time(fails, budget, gots)
