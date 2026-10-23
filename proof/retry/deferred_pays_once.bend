# eukhe: the proof of LAW deferred_pays_once

import Base
import ../../bend/retry.bend as R
import ../../LAWS.bend as Laws
import ./base.bend as LA

# (R4) The deferred job
# ---------------------

def rp.send_off(a: R.Act) -> {R.tally.send(a, False{}) == 0n : Nat}:
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

def rp.pending_send(over: Bool, +left: Nat, +gap: Nat) -> {R.tally.send(R.Step.act(R.live.pending(over, left, gap)), True{}) == 0n : Nat}:
  match over:
    case True{}:
      {==}
    case False{}:
      {==}

def rp.failed_send(again: Bool, +failed: Nat, +left: Nat, +gap: Nat) -> {R.tally.send(R.Step.act(R.live.failed(again, failed, left, gap)), True{}) == 0n : Nat}:
  match again:
    case True{}:
      {==}
    case False{}:
      {==}

# a step sends nothing while the job is live
def rp.step_send(+fails: Nat, +budget: Nat, job: R.Job, g: R.Got) -> {R.tally.send(R.Step.act(R.step(fails, budget, job, g)), R.Job.live(job)) == 0n : Nat}:
  match job:
    case R.NoJob{}:
      rp.send_off(R.Step.act(R.step(fails, budget, R.NoJob{}, g)))
    case R.Live{+failed, +left}:
      match g:
        case R.Answer{}:
          {==}
        case R.Later{+gap}:
          rp.pending_send(Nat.is_eq(left, 0n), left, gap)
        case R.Broke{r, +gap}:
          rp.failed_send(Bool.and(r, Bool.and(Nat.is_lt(failed, fails), Nat.is_gt(left, 0n))), failed, left, gap)

def rp.sends_go(gots: List<&2, R.Got>, +fails: Nat, +budget: Nat, +job: R.Job, +s: Nat, +l: Nat) -> {R.Tally.sends(R.run.go(gots, fails, budget, job, R.Tally{s, l})) == s : Nat}:
  match gots:
    case Nil{}:
      {==}
    case +g <> +rest:
      +x = R.tally.send(R.Step.act(R.step(fails, budget, job, g)), R.Job.live(job))
      +y = R.tally.late(R.Step.act(R.step(fails, budget, job, g)), R.Job.left(job), R.Job.live(job))
      Equal.trans(Nat, R.Tally.sends(R.run.go(rest, fails, budget, R.Step.job(R.step(fails, budget, job, g)), R.Tally{Nat.add(s, x), Nat.add(l, y)})), Nat.add(s, x), s, rp.sends_go(rest, fails, budget, R.Step.job(R.step(fails, budget, job, g)), Nat.add(s, x), Nat.add(l, y)), LA.rp.add_none(s, x, rp.step_send(fails, budget, job, g)))

def pays_once(+fails: Nat, +budget: Nat, gots: List<&2, R.Got>) -> {R.Tally.sends(R.run(fails, budget, gots)) == 0n : Nat}:
  rp.sends_go(gots, fails, budget, R.NoJob{}, 0n, 0n)

def Laws.deferred_pays_once(fails, budget, gots):
  pays_once(fails, budget, gots)
