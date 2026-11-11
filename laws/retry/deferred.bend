# eukhe: the laws of area retry, section R4: the deferred job

import Base
import ../../bend/retry.bend as R

# ---- retry: the deferred job ----

# LAWS (R4 of laws/retry.bend, whose header holds the area's requirement
# table): crates/eukhe-durable/src/harness/generation/deferred.rs and the
# poll decisions of generation.rs `classify`, as the step R.step of
# bend/retry.bend section 4: fails is retry.maxRetries; budget, the ms a
# new job may run; the job before the reply; the reply. Every input is
# free: any limits, any job, any reply. Together the laws below fix the
# whole step (act and job after it) for every input. PROOF.bend proves
# them (as RetryDeferred.<law>) with the lemmas of proof/retry/.

def rs.step.act(s: R.Step) -> R.Act:
  match s:
    case R.Step{act, job}:
      act

def rs.step.job(s: R.Step) -> R.Job:
  match s:
    case R.Step{act, job}:
      job

def rs.sent(a: R.Act) -> Bool:
  match a:
    case R.Send{}:
      True{}
    case R.Poll{}:
      False{}
    case R.Cancel{}:
      False{}
    case R.Settle{}:
      False{}
    case R.Quit{}:
      False{}

def rs.polled(a: R.Act) -> Bool:
  match a:
    case R.Send{}:
      False{}
    case R.Poll{}:
      True{}
    case R.Cancel{}:
      False{}
    case R.Settle{}:
      False{}
    case R.Quit{}:
      False{}

def rs.quits(a: R.Act) -> Bool:
  match a:
    case R.Send{}:
      False{}
    case R.Poll{}:
      False{}
    case R.Cancel{}:
      False{}
    case R.Settle{}:
      False{}
    case R.Quit{}:
      True{}

def rs.live(j: R.Job) -> Bool:
  match j:
    case R.NoJob{}:
      False{}
    case R.Live{failed, left}:
      True{}

# the ms the job a reply is for has left: a new job's budget when none is
# live
def rs.time(+budget: Nat, j: R.Job) -> Nat:
  match j:
    case R.NoJob{}:
      budget
    case R.Live{failed, left}:
      left

# the failures in a row of the job after a step (0 when none is live)
def rs.failed(s: R.Step) -> Nat:
  match s:
    case R.Step{act, job}:
      match job:
        case R.NoJob{}:
          0n
        case R.Live{failed, left}:
          failed

# the gap a reply asks the next poll to wait past (0 for an answer)
def rs.gap(g: R.Got) -> Nat:
  match g:
    case R.Answer{}:
      0n
    case R.Later{gap}:
      gap
    case R.Broke{r, gap}:
      gap

# a poll is charged its wait: it leaves a live job with gap+1 ms fewer
# than `before` (0 at least); a step that does not poll is not charged
def rs.charged(s: R.Step, +before: Nat, +gap: Nat) -> Bool:
  match s:
    case R.Step{act, job}:
      match act:
        case R.Poll{}:
          match job:
            case R.NoJob{}:
              False{}
            case R.Live{failed, left}:
              Nat.is_eq(left, Nat.sub(before, 1n+gap))
        case R.Send{}:
          True{}
        case R.Cancel{}:
          True{}
        case R.Settle{}:
          True{}
        case R.Quit{}:
          True{}

# LAW deferred_pays_once (R4): no request goes out while the request's deferred job is live,
# whatever the reply (a new request would pay for the work twice)
# EXCLUDES: a failed poll or a deferred reply answered by sending the request again
law deferred_pays_once:
  for fails: Nat
  for budget: Nat
  for failed: Nat
  for left: Nat
  for g: R.Got
  {rs.sent(rs.step.act(R.step(fails, budget, R.Live{failed, left}, g))) == False{} : Bool}

# LAW deferred_bounded_in_time (R4): no poll goes out at or after the job's deadline: a live job
# with no ms left, or a new job with a budget of 0, is never polled, whatever the reply
# EXCLUDES: a poll past the deadline (a job that runs forever)
law deferred_bounded_in_time:
  for fails: Nat
  for budget: Nat
  for job: R.Job
  for g: R.Got
  for none: {rs.time(budget, job) == 0n : Nat}
  {rs.polled(rs.step.act(R.step(fails, budget, job, g))) == False{} : Bool}

# LAW deferred_poll_charged (R4): every poll goes out gap+1 ms later, charged to the job's time:
# it leaves a live job with the ms it had (a new job: its budget) less gap+1, never fewer than 0;
# with deferred_bounded_in_time, a job polls at most once per ms of its budget
# EXCLUDES: a poll sooner than the reply asked, a poll that keeps the ms left (no deadline), a poll
#   that drops the job
law deferred_poll_charged:
  for fails: Nat
  for budget: Nat
  for job: R.Job
  for g: R.Got
  {rs.charged(R.step(fails, budget, job, g), rs.time(budget, job), rs.gap(g)) == True{} : Bool}

# LAW deferred_answer_settles (R4): an answer settles the request, live job or not: no job is
# left
# EXCLUDES: an answer that polls, sends again or keeps a job
law deferred_answer_settles:
  for fails: Nat
  for budget: Nat
  for job: R.Job
  {R.step(fails, budget, job, R.Answer{}) == R.Step{R.Settle{}, R.NoJob{}} : R.Step}

# LAW deferred_failed_poll_cancels (R4): a failed poll of a live job that the classifier does not
# retry, that reaches retry.maxRetries failures in a row, or that has no ms left, cancels the job
# EXCLUDES: a failed poll that keeps a job past retry.maxRetries, a non-retryable failure or the
#   deadline, a failed poll that quits with the job still running
law deferred_failed_poll_cancels:
  for fails: Nat
  for budget: Nat
  for failed: Nat
  for left: Nat
  for r: Bool
  for gap: Nat
  for stop: {Bool.or(Bool.not(r), Bool.or(Nat.is_le(fails, failed), Nat.is_eq(left, 0n))) == True{} : Bool}
  {R.step(fails, budget, R.Live{failed, left}, R.Broke{r, gap}) == R.Step{R.Cancel{}, R.NoJob{}} : R.Step}

# LAW deferred_failed_poll_repolls (R4): a retryable failed poll of a live job, below
# retry.maxRetries failures in a row and with time left, polls the same job again, with one more
# failure in a row
# EXCLUDES: a step that cancels (or quits) on every failed poll, a count of failures that does not
#   grow (a job polled forever)
law deferred_failed_poll_repolls:
  for fails: Nat
  for budget: Nat
  for failed: Nat
  for left: Nat
  for gap: Nat
  for below: {Nat.is_lt(failed, fails) == True{} : Bool}
  for live: {Nat.is_gt(left, 0n) == True{} : Bool}
  {rs.polled(rs.step.act(R.step(fails, budget, R.Live{failed, left}, R.Broke{True{}, gap}))) == True{} : Bool} & {rs.failed(R.step(fails, budget, R.Live{failed, left}, R.Broke{True{}, gap})) == 1n+failed : Nat}

# LAW deferred_reply_polls (R4): a deferred reply while the job has time left (a new job: a
# positive budget) polls the job, and its failures in a row start over
# EXCLUDES: a deferred reply that cancels with time left, one that keeps the failures in a row
law deferred_reply_polls:
  for fails: Nat
  for budget: Nat
  for job: R.Job
  for gap: Nat
  for some: {Nat.is_gt(rs.time(budget, job), 0n) == True{} : Bool}
  {rs.polled(rs.step.act(R.step(fails, budget, job, R.Later{gap}))) == True{} : Bool} & {rs.failed(R.step(fails, budget, job, R.Later{gap})) == 0n : Nat}

# LAW deferred_deadline_cancels (R4): a deferred reply with no time left (a new job: a budget of
# 0) cancels the job
# EXCLUDES: a job kept, or the request sent again, at its deadline
law deferred_deadline_cancels:
  for fails: Nat
  for budget: Nat
  for job: R.Job
  for gap: Nat
  for none: {rs.time(budget, job) == 0n : Nat}
  {R.step(fails, budget, job, R.Later{gap}) == R.Step{R.Cancel{}, R.NoJob{}} : R.Step}

# LAW deferred_fresh_failure (R4): a failure with no live job sends the request again exactly
# when the classifier retries it, else the request quits; no job is left
# EXCLUDES: a retryable failure that ends the run, a failure the classifier refuses sent again, a
#   failure that leaves a job
law deferred_fresh_failure:
  for fails: Nat
  for budget: Nat
  for r: Bool
  for gap: Nat
  {rs.sent(rs.step.act(R.step(fails, budget, R.NoJob{}, R.Broke{r, gap}))) == r : Bool} & {rs.quits(rs.step.act(R.step(fails, budget, R.NoJob{}, R.Broke{r, gap}))) == Bool.not(r) : Bool} & {rs.live(rs.step.job(R.step(fails, budget, R.NoJob{}, R.Broke{r, gap}))) == False{} : Bool}
