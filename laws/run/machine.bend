# eukhe: the laws of area run, section machine: the run of
# bend/run/step.bend and the requests of bend/run/request.bend after any
# inputs, pinned whole to the machine of LAWS.bend H4 and the requests of
# H4.7, written here
#
# The laws of laws/run/model.bend read the run after inputs only through what
# they ask of it (it ended, it failed, the round cap or the job's deadline
# failed it), and the requests only through `fresh`: a run that fails on
# the model at once, or requests that log nothing, pass them. The laws
# below fix the whole state and the whole requests, for every
# configuration and every input, step by step. Every input is free: any
# model reply, any round end, any compaction result, an abort, in any
# order.

import Base
import ../../bend/run/request.bend as RnRequest
import ../../bend/run/state.bend as RnState
import ../../bend/run/step.bend as RnStep

# The machine (H4)
# ----------------
# A state is its phase and the limits left: r rounds in the run, c
# compactions, a retries and n notes in the generation, p ms of the
# deferred job's time (a poll spends 1 ms).

# the job's ms, the retries and the notes of a generation
def rm.polls(cfg: RnState.Cfg) -> Nat:
  match cfg:
    case RnState.Cfg{cap, polls, retries, notes}:
      polls

def rm.retries(cfg: RnState.Cfg) -> Nat:
  match cfg:
    case RnState.Cfg{cap, polls, retries, notes}:
      retries

def rm.notes(cfg: RnState.Cfg) -> Nat:
  match cfg:
    case RnState.Cfg{cap, polls, retries, notes}:
      notes

# a run starts preparing its first request, with max(cap, 1) - 1 rounds
# left after the one it makes, one compaction, and every retry, note and
# ms of a generation
def rm.init(cfg: RnState.Cfg) -> RnState.St:
  match cfg:
    case RnState.Cfg{cap, polls, retries, notes}:
      RnState.St{RnState.Prepare{}, Nat.sub(cap, 1n), 1n, retries, notes, polls}

# preparation: a context over the blocking threshold (an overflow) with a
# cut waits for a compaction while the generation has one left, and spends
# it; else the request goes out, with the job's whole time
def rm.prepare.over(+cfg: RnState.Cfg, cut: Bool, r: Nat, c: Nat, a: Nat, n: Nat) -> RnState.St:
  match cut:
    case True{}:
      match c:
        case 1n+d:
          RnState.St{RnState.Compact{False{}}, r, d, a, n, rm.polls(cfg)}
        case 0n:
          RnState.St{RnState.Call{}, r, 0n, a, n, rm.polls(cfg)}
    case False{}:
      RnState.St{RnState.Call{}, r, c, a, n, rm.polls(cfg)}

def rm.prepare(+cfg: RnState.Cfg, reply: RnState.Reply, r: Nat, c: Nat, a: Nat, n: Nat) -> RnState.St:
  match reply:
    case RnState.Overflow{cut}:
      rm.prepare.over(cfg, cut, r, c, a, n)
    case RnState.Plain{}:
      RnState.St{RnState.Call{}, r, c, a, n, rm.polls(cfg)}
    case RnState.Calls{}:
      RnState.St{RnState.Call{}, r, c, a, n, rm.polls(cfg)}
    case RnState.Deferred{}:
      RnState.St{RnState.Call{}, r, c, a, n, rm.polls(cfg)}
    case RnState.Error{retryable, noted}:
      RnState.St{RnState.Call{}, r, c, a, n, rm.polls(cfg)}

# an error: a noted one retries with a note while notes are left and
# spends one, retryable or not; one that is not noted retries while it is
# retryable and retries are left and spends one; a retry prepares the
# request again with the job's whole time; else the model fails the run
def rm.error(+cfg: RnState.Cfg, noted: Bool, retryable: Bool, r: Nat, c: Nat, a: Nat, n: Nat, p: Nat) -> RnState.St:
  match noted:
    case True{}:
      match n:
        case 1n+m:
          RnState.St{RnState.Prepare{}, r, c, a, m, rm.polls(cfg)}
        case 0n:
          RnState.St{RnState.Failed{RnState.Model{}}, r, c, a, 0n, p}
    case False{}:
      match retryable:
        case True{}:
          match a:
            case 1n+b:
              RnState.St{RnState.Prepare{}, r, c, b, n, rm.polls(cfg)}
            case 0n:
              RnState.St{RnState.Failed{RnState.Model{}}, r, c, 0n, n, p}
        case False{}:
          RnState.St{RnState.Failed{RnState.Model{}}, r, c, a, n, p}

# a reply to a request or a poll: text answers the run; calls go to the
# tools; a deferred reply polls again while the job has ms left (spending
# one), else the job's deadline fails the run; an error as rm.error; an
# overflow with a cut compacts while the generation has a compaction left
# (and spends it), else the model fails the run
def rm.call(+cfg: RnState.Cfg, reply: RnState.Reply, r: Nat, c: Nat, a: Nat, n: Nat, p: Nat) -> RnState.St:
  match reply:
    case RnState.Plain{}:
      RnState.St{RnState.Answered{}, r, c, a, n, p}
    case RnState.Calls{}:
      RnState.St{RnState.Tools{}, r, c, a, n, p}
    case RnState.Deferred{}:
      match p:
        case 1n+q:
          RnState.St{RnState.Call{}, r, c, a, n, q}
        case 0n:
          RnState.St{RnState.Failed{RnState.Polls{}}, r, c, a, n, 0n}
    case RnState.Error{retryable, noted}:
      rm.error(cfg, noted, retryable, r, c, a, n, p)
    case RnState.Overflow{cut}:
      match cut:
        case True{}:
          match c:
            case 1n+d:
              RnState.St{RnState.Compact{True{}}, r, d, a, n, p}
            case 0n:
              RnState.St{RnState.Failed{RnState.Model{}}, r, 0n, a, n, p}
        case False{}:
          RnState.St{RnState.Failed{RnState.Model{}}, r, c, a, n, p}

# a compaction ends: one that appended its entry prepares the request
# again with the job's whole time; one that found nothing does too after a
# threshold compaction, but fails the run after an overflow's (the request
# still overflows); a failed one fails the run
def rm.compact(+cfg: RnState.Cfg, got: RnState.Got, over: Bool, r: Nat, c: Nat, a: Nat, n: Nat, p: Nat) -> RnState.St:
  match got:
    case RnState.Built{}:
      RnState.St{RnState.Prepare{}, r, c, a, n, rm.polls(cfg)}
    case RnState.Kept{}:
      match over:
        case True{}:
          RnState.St{RnState.Failed{RnState.Model{}}, r, c, a, n, p}
        case False{}:
          RnState.St{RnState.Prepare{}, r, c, a, n, rm.polls(cfg)}
    case RnState.Broke{}:
      RnState.St{RnState.Failed{RnState.Model{}}, r, c, a, n, p}

# a round ends: a control stops the run, uncounted; else the round
# counts: with no round left the cap fails the run; else a queued reset
# ends it (answered) with one round less; else the next generation
# prepares with one round less, one compaction and every retry, note and
# ms of a generation
def rm.tools(+cfg: RnState.Cfg, fin: RnState.Fin, r: Nat, c: Nat, a: Nat, n: Nat, p: Nat) -> RnState.St:
  match fin:
    case RnState.Stops{}:
      RnState.St{RnState.Answered{}, r, c, a, n, p}
    case RnState.Goes{}:
      match r:
        case 0n:
          RnState.St{RnState.Failed{RnState.Rounds{}}, 0n, c, a, n, p}
        case 1n+s:
          RnState.St{RnState.Prepare{}, s, 1n, rm.retries(cfg), rm.notes(cfg), rm.polls(cfg)}
    case RnState.Resets{}:
      match r:
        case 0n:
          RnState.St{RnState.Failed{RnState.Rounds{}}, 0n, c, a, n, p}
        case 1n+s:
          RnState.St{RnState.Answered{}, s, c, a, n, p}

# one input: an ended run stays as it is; an abort ends a live run as
# aborted; else the phase reads the part of the input it needs
def rm.step(+cfg: RnState.Cfg, s: RnState.St, e: RnState.Ev) -> RnState.St:
  match s:
    case RnState.St{ph, r, c, a, n, p}:
      match ph:
        case RnState.Answered{}:
          RnState.St{RnState.Answered{}, r, c, a, n, p}
        case RnState.Aborted{}:
          RnState.St{RnState.Aborted{}, r, c, a, n, p}
        case RnState.Failed{why}:
          RnState.St{RnState.Failed{why}, r, c, a, n, p}
        case RnState.Prepare{}:
          match e:
            case RnState.Abort{}:
              RnState.St{RnState.Aborted{}, r, c, a, n, p}
            case RnState.Go{reply, fin, got}:
              rm.prepare(cfg, reply, r, c, a, n)
        case RnState.Call{}:
          match e:
            case RnState.Abort{}:
              RnState.St{RnState.Aborted{}, r, c, a, n, p}
            case RnState.Go{reply, fin, got}:
              rm.call(cfg, reply, r, c, a, n, p)
        case RnState.Compact{over}:
          match e:
            case RnState.Abort{}:
              RnState.St{RnState.Aborted{}, r, c, a, n, p}
            case RnState.Go{reply, fin, got}:
              rm.compact(cfg, got, over, r, c, a, n, p)
        case RnState.Tools{}:
          match e:
            case RnState.Abort{}:
              RnState.St{RnState.Aborted{}, r, c, a, n, p}
            case RnState.Go{reply, fin, got}:
              rm.tools(cfg, fin, r, c, a, n, p)

# the run after evs: each input a step, in order, from the start
def rm.run.go(evs: List<&2, RnState.Ev>, +cfg: RnState.Cfg, s: RnState.St) -> RnState.St:
  match evs:
    case Nil{}:
      s
    case e <> rest:
      rm.run.go(rest, cfg, rm.step(cfg, s, e))

def rm.run(+cfg: RnState.Cfg, evs: List<&2, RnState.Ev>) -> RnState.St:
  rm.run.go(evs, cfg, rm.init(cfg))

# The requests (H4.7)
# -------------------
# The requests of a run: the version of its logged context, the attempt of
# its generation, the note its next request carries (0: none), and what it
# sent and cut, newest first.

def rm.ph(s: RnState.St) -> RnState.Ph:
  match s:
    case RnState.St{ph, r, c, a, n, p}:
      ph

# the requests t after input e takes the run from phase pb to phase pa:
# preparation that ends in a call sends the request (its context and its
# note); an error to a request counts an attempt, and a noted one cuts the
# request and its retry carries the note of that attempt; a compaction
# that appended its entry grows the context; a round that goes on to the
# next generation grows the context and starts it at attempt 1 with no
# note; nothing else changes them
def rm.reqs.step(t: RnRequest.Reqs, pb: RnState.Ph, e: RnState.Ev, pa: RnState.Ph) -> RnRequest.Reqs:
  match t:
    case RnRequest.Reqs{+ctx, +n, +note, log}:
      match pb:
        case RnState.Prepare{}:
          match pa:
            case RnState.Call{}:
              RnRequest.Reqs{ctx, n, note, RnRequest.Sent{RnRequest.Req{ctx, note}} <> log}
            case RnState.Prepare{}:
              RnRequest.Reqs{ctx, n, note, log}
            case RnState.Compact{over}:
              RnRequest.Reqs{ctx, n, note, log}
            case RnState.Tools{}:
              RnRequest.Reqs{ctx, n, note, log}
            case RnState.Answered{}:
              RnRequest.Reqs{ctx, n, note, log}
            case RnState.Aborted{}:
              RnRequest.Reqs{ctx, n, note, log}
            case RnState.Failed{why}:
              RnRequest.Reqs{ctx, n, note, log}
        case RnState.Call{}:
          match e:
            case RnState.Abort{}:
              RnRequest.Reqs{ctx, n, note, log}
            case RnState.Go{reply, fin, got}:
              match reply:
                case RnState.Error{retryable, noted}:
                  match noted:
                    case True{}:
                      RnRequest.Reqs{ctx, 1n+n, 1n+n, RnRequest.Cut{RnRequest.Req{ctx, note}} <> log}
                    case False{}:
                      RnRequest.Reqs{ctx, 1n+n, note, log}
                case RnState.Plain{}:
                  RnRequest.Reqs{ctx, n, note, log}
                case RnState.Calls{}:
                  RnRequest.Reqs{ctx, n, note, log}
                case RnState.Deferred{}:
                  RnRequest.Reqs{ctx, n, note, log}
                case RnState.Overflow{cut}:
                  RnRequest.Reqs{ctx, n, note, log}
        case RnState.Compact{over}:
          match e:
            case RnState.Abort{}:
              RnRequest.Reqs{ctx, n, note, log}
            case RnState.Go{reply, fin, got}:
              match got:
                case RnState.Built{}:
                  RnRequest.Reqs{1n+ctx, n, note, log}
                case RnState.Kept{}:
                  RnRequest.Reqs{ctx, n, note, log}
                case RnState.Broke{}:
                  RnRequest.Reqs{ctx, n, note, log}
        case RnState.Tools{}:
          match pa:
            case RnState.Prepare{}:
              RnRequest.Reqs{1n+ctx, 1n, 0n, log}
            case RnState.Call{}:
              RnRequest.Reqs{ctx, n, note, log}
            case RnState.Compact{over}:
              RnRequest.Reqs{ctx, n, note, log}
            case RnState.Tools{}:
              RnRequest.Reqs{ctx, n, note, log}
            case RnState.Answered{}:
              RnRequest.Reqs{ctx, n, note, log}
            case RnState.Aborted{}:
              RnRequest.Reqs{ctx, n, note, log}
            case RnState.Failed{why}:
              RnRequest.Reqs{ctx, n, note, log}
        case RnState.Answered{}:
          RnRequest.Reqs{ctx, n, note, log}
        case RnState.Aborted{}:
          RnRequest.Reqs{ctx, n, note, log}
        case RnState.Failed{why}:
          RnRequest.Reqs{ctx, n, note, log}

# the requests after evs: each input moves the run a step (rm.step) and
# the requests with it, from context 0, attempt 1, no note, nothing sent
def rm.reqs.go(evs: List<&2, RnState.Ev>, +cfg: RnState.Cfg, +s: RnState.St, t: RnRequest.Reqs) -> RnRequest.Reqs:
  match evs:
    case Nil{}:
      t
    case +e <> rest:
      +s2 = rm.step(cfg, s, e)
      rm.reqs.go(rest, cfg, s2, rm.reqs.step(t, rm.ph(s), e, rm.ph(s2)))

def rm.reqs(+cfg: RnState.Cfg, evs: List<&2, RnState.Ev>) -> RnRequest.Reqs:
  rm.reqs.go(evs, cfg, rm.init(cfg), RnRequest.Reqs{0n, 1n, 0n, Nil{}})

# Laws
# ----

# LAW run_step_exact (H4): one input to any state, under any configuration, is the machine's step: an ended run stays; an abort ends a live run; preparation, a reply, a compaction's end and a round's end each move the phase and spend or renew the limits as rm.step says
# EXCLUDES: a step that fails on the model whatever the input, a limit
#   spent twice or not at all, the job's time not renewed by a retry, a
#   round that renews the limits without counting itself, a reply read
#   in a phase that does not read it
law run_step_exact:
  for +cfg: RnState.Cfg
  for +s: RnState.St
  for +e: RnState.Ev
  {RnStep.step(cfg, s, e) == rm.step(cfg, s, e) : RnState.St}

# LAW run_fold_exact (H4): the run after any inputs, under any configuration, is the machine's: rm.step on each input, in order, from the start rm.init
# EXCLUDES: a run that answers St{Failed{Model{}}, ...} for every input
#   (run_ends, run_rounds_capped, run_rounds_fail_at_cap and
#   run_polls_need_defers all pass it), a run that skips, reorders or
#   repeats an input, or starts from other limits
law run_fold_exact:
  for +cfg: RnState.Cfg
  for evs: List<&2, RnState.Ev>
  {RnStep.run(cfg, evs) == rm.run(cfg, evs) : RnState.St}

# LAW run_reqs_exact (H4.7): the requests of the run after any inputs, under any configuration, are exactly the ones its steps make: each request sent when preparation ends in a call, each request cut by a noted error, the attempt and note of the next request, the context version
# EXCLUDES: requests that log nothing (an empty log passes
#   run_retry_sends_a_new_request), a sent request left out of the log, a
#   cut that names another request, an attempt or a context that does not
#   move, requests read from a run other than the machine's
law run_reqs_exact:
  for +cfg: RnState.Cfg
  for evs: List<&2, RnState.Ev>
  {RnRequest.reqs(cfg, evs) == rm.reqs(cfg, evs) : RnRequest.Reqs}
