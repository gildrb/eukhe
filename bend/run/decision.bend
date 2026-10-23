# run: the decisions Rust calls (decide.rs): Lim/At counts left, Then, Th, Prepared, End, Stuck, Help and decide.*

import Base
import ./state.bend as RnState
import ./step.bend as RnStep
import ./recovery.bend as RnRecovery

# The decisions Rust calls
# ------------------------
# crates/eukhe-durable/src/harness/generation/decide.rs and deferred.rs
# call these through the compiled core (bend/ffi_run.bend): each is one
# pure call, and the phases of generation.rs and round.rs do the IO
# around it. Rust keeps its counters as they grow (Counts, Rounds): the
# attempt, the noted retries, the ms the request waited, whether the
# generation compacted, the rounds the run made. A decision turns them
# into the counts left that the steps above read (Lim.cfg, At.a, At.n,
# At.p, At.c, Lim.r), takes the step of the model, and reads its answer
# back. So the code that runs is the model: every law of H4 and H4.8 is a
# law of it. LAWS.bend (H4.9) proves that each decision is the Rust rule
# it replaced, for every input, and that the counts left lose nothing.

# rounds: maxToolRounds (at least 1); wait: the ms the request's
# deferred job may run (`Limits::max_wait`); retries: retry.maxRetries;
# notes: MAX_NOTES
type Lim is Data:
  Lim{rounds: Nat, wait: Nat, retries: Nat, notes: Nat}

def Lim.rounds(l: Lim) -> Nat:
  match l:
    case Lim{rounds, wait, retries, notes}:
      rounds

def Lim.wait(l: Lim) -> Nat:
  match l:
    case Lim{rounds, wait, retries, notes}:
      wait

def Lim.retries(l: Lim) -> Nat:
  match l:
    case Lim{rounds, wait, retries, notes}:
      retries

def Lim.notes(l: Lim) -> Nat:
  match l:
    case Lim{rounds, wait, retries, notes}:
      notes

# the counters of one request (`Counts`): attempt, 1 for a generation's
# first request and one more per retry; notes, the noted retries so far;
# waited, the ms since the request was sent; compacted, the generation
# compacted (it compacts at most once)
type At is Data:
  At{attempt: Nat, notes: Nat, waited: Nat, compacted: Bool}

def At.attempt(t: At) -> Nat:
  match t:
    case At{attempt, notes, waited, compacted}:
      attempt

def At.notes(t: At) -> Nat:
  match t:
    case At{attempt, notes, waited, compacted}:
      notes

def At.waited(t: At) -> Nat:
  match t:
    case At{attempt, notes, waited, compacted}:
      waited

def At.compacted(t: At) -> Bool:
  match t:
    case At{attempt, notes, waited, compacted}:
      compacted

# the limits as the model's Cfg
def Lim.cfg(l: Lim) -> RnState.Cfg:
  match l:
    case Lim{rounds, wait, retries, notes}:
      RnState.Cfg{rounds, wait, retries, notes}

# the compactions left: one until the generation compacted
def c.of(compacted: Bool) -> Nat:
  match compacted:
    case True{}:
      0n
    case False{}:
      1n

def At.c(t: At) -> Nat:
  c.of(At.compacted(t))

# the retries the generation spent: its retries that were not noted
def At.spent(+t: At) -> Nat:
  Nat.sub(Nat.sub(At.attempt(t), 1n), At.notes(t))

# the retries, the notes and the ms of the deferred job left
def At.a(+l: Lim, +t: At) -> Nat:
  Nat.sub(Lim.retries(l), At.spent(t))

def At.n(+l: Lim, +t: At) -> Nat:
  Nat.sub(Lim.notes(l), At.notes(t))

def At.p(+l: Lim, +t: At) -> Nat:
  Nat.sub(Lim.wait(l), At.waited(t))

# the rounds left after count rounds (init starts at rounds - 1)
def Lim.r(+l: Lim, count: Nat) -> Nat:
  Nat.sub(Nat.sub(Lim.rounds(l), 1n), count)

# What follows a reply (`Step`): an answer, the tools, a poll of the
# same job, a transient retry, a noted retry, a compaction, or the end of
# the run on the model (Fail) or at the job's deadline (Late)
type Then is Data:
  DoAnswer{}
  DoTools{}
  DoPoll{}
  DoRetry{}
  DoNote{}
  DoCompact{}
  DoFail{}
  DoLate{}

def Then.why(w: RnState.Why) -> Then:
  match w:
    case RnState.Model{}:
      DoFail{}
    case RnState.Polls{}:
      DoLate{}
    case RnState.Rounds{}:
      DoFail{}

def Then.prep(noted: Bool) -> Then:
  match noted:
    case True{}:
      DoNote{}
    case False{}:
      DoRetry{}

# the step a reply led to, read from the phase after it; a retry is a
# noted one when the reply was noted. A reply never aborts a run nor caps
# its rounds
def Then.ph(noted: Bool, ph: RnState.Ph) -> Then:
  match ph:
    case RnState.Prepare{}:
      Then.prep(noted)
    case RnState.Call{}:
      DoPoll{}
    case RnState.Compact{over}:
      DoCompact{}
    case RnState.Tools{}:
      DoTools{}
    case RnState.Answered{}:
      DoAnswer{}
    case RnState.Aborted{}:
      DoFail{}
    case RnState.Failed{why}:
      Then.why(why)

def Reply.noted(r: RnState.Reply) -> Bool:
  match r:
    case RnState.Plain{}:
      False{}
    case RnState.Calls{}:
      False{}
    case RnState.Deferred{}:
      False{}
    case RnState.Error{retryable, noted}:
      noted
    case RnState.Overflow{cut}:
      False{}

# the step after a reply to the request or poll that `t` counts
# (`after_reply`)
def decide.reply(+l: Lim, +t: At, +reply: RnState.Reply) -> Then:
  Then.ph(Reply.noted(reply), RnState.St.ph(RnStep.call(Lim.cfg(l), reply, 0n, At.c(t), At.a(l, t), At.n(l, t), At.p(l, t))))

# which threshold compaction the context is over, given a cut exists
# (`threshold_for`, then a cut): none, the background one, the blocking
# one
type Th is Data:
  Under{}
  Background{}
  Blocking{}

def Th.blocks(th: Th) -> Bool:
  match th:
    case Under{}:
      False{}
    case Background{}:
      False{}
    case Blocking{}:
      True{}

def Th.background(th: Th) -> Bool:
  match th:
    case Under{}:
      False{}
    case Background{}:
      True{}
    case Blocking{}:
      False{}

# what preparation does with its request (`Prepared`): it waits for a
# blocking threshold compaction, or sends the request, with a background
# compaction beside it when background
type Prepared is Data:
  Waits{}
  Sends{background: Bool}

def Prepared.ph(background: Bool, ph: RnState.Ph) -> Prepared:
  match ph:
    case RnState.Compact{over}:
      Waits{}
    case RnState.Prepare{}:
      Sends{background}
    case RnState.Call{}:
      Sends{background}
    case RnState.Tools{}:
      Sends{background}
    case RnState.Answered{}:
      Sends{background}
    case RnState.Aborted{}:
      Sends{background}
    case RnState.Failed{why}:
      Sends{background}

# what preparation does before a request of a generation that compacted
# or not, its context over th (`before_request`). A generation that
# compacted reads no threshold, so Rust need not measure its context
def decide.prepare(+compacted: Bool, +th: Th) -> Prepared:
  Prepared.ph(Bool.and(Bool.not(compacted), Th.background(th)), RnState.St.ph(RnStep.prepare(RnState.Cfg{0n, 0n, 0n, 0n}, RnState.Overflow{Th.blocks(th)}, 0n, c.of(compacted), 0n, 0n)))

def Ph.goes(ph: RnState.Ph) -> Bool:
  match ph:
    case RnState.Prepare{}:
      True{}
    case RnState.Call{}:
      False{}
    case RnState.Compact{over}:
      False{}
    case RnState.Tools{}:
      False{}
    case RnState.Answered{}:
      False{}
    case RnState.Aborted{}:
      False{}
    case RnState.Failed{why}:
      False{}

# whether preparation goes on after the compaction it waited for, an
# overflow's (over) or a blocking threshold one, that ended as got
# (`after_compaction`); else the run fails on the model
def decide.compact(over: Bool, got: RnState.Got) -> Bool:
  Ph.goes(RnState.St.ph(RnStep.compact(RnState.Cfg{0n, 0n, 0n, 0n}, over, got, 0n, 0n, 0n, 0n, 0n)))

# how a finished round ends (`RoundEnd`): a control stopped the run (it
# is answered), a queued reset ended it, the round cap failed it, or the
# next generation goes on after count rounds
type End is Data:
  EndStop{}
  EndReset{}
  EndCapped{}
  EndNext{count: Nat}

# a control (terminate, handoff) wins over a queued reset
def fin.of(stops: Bool, reset: Bool) -> RnState.Fin:
  match stops:
    case True{}:
      RnState.Stops{}
    case False{}:
      match reset:
        case True{}:
          RnState.Resets{}
        case False{}:
          RnState.Goes{}

def End.answered(fin: RnState.Fin) -> End:
  match fin:
    case RnState.Stops{}:
      EndStop{}
    case RnState.Resets{}:
      EndReset{}
    case RnState.Goes{}:
      EndStop{}

# the end a round led to, read from the phase after it: a round that goes
# on counts one more
def End.ph(fin: RnState.Fin, count: Nat, ph: RnState.Ph) -> End:
  match ph:
    case RnState.Answered{}:
      End.answered(fin)
    case RnState.Prepare{}:
      EndNext{1n+count}
    case RnState.Failed{why}:
      EndCapped{}
    case RnState.Call{}:
      EndCapped{}
    case RnState.Compact{over}:
      EndCapped{}
    case RnState.Tools{}:
      EndCapped{}
    case RnState.Aborted{}:
      EndCapped{}

# how the round after count rounds ends (`round_end`): stops, a control
# ends the run; reset, a queued reset applied at the round's boundary
def decide.round(+l: Lim, +count: Nat, stops: Bool, reset: Bool) -> End:
  +fin = fin.of(stops, reset)
  End.ph(fin, count, RnState.St.ph(RnStep.tools(Lim.cfg(l), fin, Lim.r(l, count), 0n, 0n, 0n, 0n)))

# a stuck reply as `recover` reads it (`Stuck`): a length stop with no
# answer, leaked calls that the harness could not rebuild, or calls that
# would make 1 + before rounds in a row with the same calls and results
type Stuck is Data:
  Truncated{}
  Leaked{}
  Repeats{before: Nat}

# what a recovery does with it (`Act`): the calls run, a retry with the
# row-th note of the recovery in a row, the reply answers as text, or the
# run fails on the model
type Help is Data:
  Runs{}
  Redoes{row: Nat}
  Stands{}
  Quits{}

def Rec.row(r: RnRecovery.Rec) -> Nat:
  match r:
    case RnRecovery.Rec{k, row, same, last}:
      row

def Help.act(a: RnRecovery.Act, row: Nat) -> Help:
  match a:
    case RnRecovery.Exec{}:
      Runs{}
    case RnRecovery.Redo{}:
      Redoes{row}
    case RnRecovery.Stand{}:
      Stands{}
    case RnRecovery.Quit{}:
      Quits{}
    case RnRecovery.Pass{}:
      Quits{}

def Help.of(d: RnRecovery.Dec) -> Help:
  match d:
    case RnRecovery.Dec{act, r}:
      Help.act(act, Rec.row(r))

# the reply the recoveries read: calls with the same results as the last
# round, which ran them `before` rounds in a row
def Stuck.out(s: Stuck) -> RnRecovery.Out:
  match s:
    case Truncated{}:
      RnRecovery.Long{}
    case Leaked{}:
      RnRecovery.Leak{False{}, 0n, False{}}
    case Repeats{before}:
      RnRecovery.Ran{0n, True{}}

def Stuck.same(s: Stuck) -> Nat:
  match s:
    case Truncated{}:
      0n
    case Leaked{}:
      0n
    case Repeats{before}:
      before

# what a recovery does with a stuck reply, after the request whose note
# counts row notes of the recovery k in a row (`recover`)
def decide.recover(+rc: RnRecovery.RCfg, +s: Stuck, k: RnRecovery.Rk, row: Nat) -> Help:
  Help.of(RnRecovery.rec.go(rc, Stuck.out(s), k, row, Stuck.same(s), 0n))

# a failed poll of a deferred job (`PollFailure::next`): it polls the same
# job again while the failure is retryable and fewer than `retries` polls
# failed in a row before it; else the job is cancelled. The deadline of
# the job still holds: the poll goes through decide.reply as a deferred
# reply. LAWS.bend proves both together are the job of bend/retry.bend
# section 4
def decide.poll(retryable: Bool, failures: Nat, retries: Nat) -> Bool:
  Bool.and(retryable, Nat.is_lt(failures, retries))
