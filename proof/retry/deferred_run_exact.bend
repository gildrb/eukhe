# eukhe: the proof of LAW deferred_run_exact

import Base
import ../../bend/retry.bend as R
import ../../laws/retry.bend as Retry
import ./base.bend as LA

def rp.step_act(s: R.Step) -> {R.Step.act(s) == Retry.rs.step.act(s) : R.Act}:
  match s:
    case R.Step{a, j}:
      {==}

def rp.step_job(s: R.Step) -> {R.Step.job(s) == Retry.rs.step.job(s) : R.Job}:
  match s:
    case R.Step{a, j}:
      {==}

# a step is counted as the spec counts it, with the job before it
def rp.count(t: R.Tally, +a: R.Act, +job: R.Job) -> {R.tally.add(t, a, job) == Retry.rs.job.count(t, a, job) : R.Tally}:
  match t:
    case R.Tally{+s, +l}:
      match a:
        case R.Send{}:
          match job:
            case R.NoJob{}:
              {==}
            case R.Live{f, left}:
              {==}
        case R.Poll{}:
          match job:
            case R.NoJob{}:
              {==}
            case R.Live{f, left}:
              match left:
                case 0n:
                  {==}
                case 1n+k:
                  {==}
        case R.Cancel{}:
          match job:
            case R.NoJob{}:
              {==}
            case R.Live{f, left}:
              {==}
        case R.Settle{}:
          match job:
            case R.NoJob{}:
              {==}
            case R.Live{f, left}:
              {==}
        case R.Quit{}:
          match job:
            case R.NoJob{}:
              {==}
            case R.Live{f, left}:
              {==}

def rp.run_go(gots: List<&2, R.Got>, +fails: Nat, +budget: Nat, +job: R.Job, +t: R.Tally) -> {R.run.go(gots, fails, budget, job, t) == Retry.rs.job_run.go(gots, fails, budget, job, t) : R.Tally}:
  match gots:
    case Nil{}:
      {==}
    case +g <> +rest:
      %LA.rp.job_step(fails, budget, job, g) : {R.run.go(rest, fails, budget, R.Step.job(R.step(fails, budget, job, g)), R.tally.add(t, R.Step.act(R.step(fails, budget, job, g)), job)) == Retry.rs.job_run.go(rest, fails, budget, Retry.rs.step.job(_), Retry.rs.job.count(t, Retry.rs.step.act(_), job)) : R.Tally}
      %rp.step_job(R.step(fails, budget, job, g)) : {R.run.go(rest, fails, budget, R.Step.job(R.step(fails, budget, job, g)), R.tally.add(t, R.Step.act(R.step(fails, budget, job, g)), job)) == Retry.rs.job_run.go(rest, fails, budget, _, Retry.rs.job.count(t, Retry.rs.step.act(R.step(fails, budget, job, g)), job)) : R.Tally}
      %rp.step_act(R.step(fails, budget, job, g)) : {R.run.go(rest, fails, budget, R.Step.job(R.step(fails, budget, job, g)), R.tally.add(t, R.Step.act(R.step(fails, budget, job, g)), job)) == Retry.rs.job_run.go(rest, fails, budget, R.Step.job(R.step(fails, budget, job, g)), Retry.rs.job.count(t, _, job)) : R.Tally}
      %rp.count(t, R.Step.act(R.step(fails, budget, job, g)), job) : {R.run.go(rest, fails, budget, R.Step.job(R.step(fails, budget, job, g)), R.tally.add(t, R.Step.act(R.step(fails, budget, job, g)), job)) == Retry.rs.job_run.go(rest, fails, budget, R.Step.job(R.step(fails, budget, job, g)), _) : R.Tally}
      rp.run_go(rest, fails, budget, R.Step.job(R.step(fails, budget, job, g)), R.tally.add(t, R.Step.act(R.step(fails, budget, job, g)), job))

def job_run(+fails: Nat, +budget: Nat, gots: List<&2, R.Got>) -> {R.run(fails, budget, gots) == Retry.rs.job_run(fails, budget, gots) : R.Tally}:
  rp.run_go(gots, fails, budget, R.NoJob{}, R.Tally{0n, 0n})

def Retry.deferred_run_exact(fails, budget, gots):
  job_run(fails, budget, gots)
