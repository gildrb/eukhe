# run: what the laws read of a run: its counted rounds, its deferred replies in a row and the input bound

import Base
import ./state.bend as RnState
import ./step.bend as RnStep

# What the laws read
# ------------------

# the counted rounds after input e, from k before it: one more if s is
# in its tools phase and the round counts (no control stopped it)
def counted.go(fin: RnState.Fin, k: Nat) -> Nat:
  match fin:
    case RnState.Stops{}:
      k
    case RnState.Goes{}:
      1n+k
    case RnState.Resets{}:
      1n+k

def counted(ph: RnState.Ph, e: RnState.Ev, k: Nat) -> Nat:
  match ph e:
    case RnState.Tools{} RnState.Go{reply, fin, got}:
      counted.go(fin, k)
    case RnState.Tools{} RnState.Abort{}:
      k
    case RnState.Prepare{} e:
      k
    case RnState.Call{} e:
      k
    case RnState.Compact{over} e:
      k
    case RnState.Answered{} e:
      k
    case RnState.Aborted{} e:
      k
    case RnState.Failed{why} e:
      k

def rounds.go(evs: List<&2, RnState.Ev>, +cfg: RnState.Cfg, +s: RnState.St, k: Nat) -> Nat:
  match evs:
    case Nil{}:
      k
    case +e <> rest:
      rounds.go(rest, cfg, RnStep.step(cfg, s, e), counted(RnState.St.ph(s), e, k))

# the counted rounds the run made
def rounds(+cfg: RnState.Cfg, evs: List<&2, RnState.Ev>) -> Nat:
  rounds.go(evs, cfg, RnState.init(cfg), 0n)

# the deferred replies in a row that the run's request has had, after
# input e at phase ph, from k before it; an ended run keeps its count
def defers.reply(reply: RnState.Reply, k: Nat) -> Nat:
  match reply:
    case RnState.Deferred{}:
      1n+k
    case RnState.Plain{}:
      0n
    case RnState.Calls{}:
      0n
    case RnState.Error{retryable, noted}:
      0n
    case RnState.Overflow{cut}:
      0n

def defers.at(ph: RnState.Ph, e: RnState.Ev, k: Nat) -> Nat:
  match ph e:
    case RnState.Call{} RnState.Go{reply, fin, got}:
      defers.reply(reply, k)
    case RnState.Call{} RnState.Abort{}:
      0n
    case RnState.Prepare{} e:
      0n
    case RnState.Compact{over} e:
      0n
    case RnState.Tools{} e:
      0n
    case RnState.Answered{} e:
      k
    case RnState.Aborted{} e:
      k
    case RnState.Failed{why} e:
      k

def defers.go(evs: List<&2, RnState.Ev>, +cfg: RnState.Cfg, +s: RnState.St, k: Nat) -> Nat:
  match evs:
    case Nil{}:
      k
    case +e <> rest:
      defers.go(rest, cfg, RnStep.step(cfg, s, e), defers.at(RnState.St.ph(s), e, k))

# the deferred replies in a row the run's last request had
def defers(+cfg: RnState.Cfg, evs: List<&2, RnState.Ev>) -> Nat:
  defers.go(evs, cfg, RnState.init(cfg), 0n)

# every run has ended after this many inputs: cap generations (at least
# one), each with (retries + notes + 2) requests (the retries, the noted
# retries, the first one and the one after its compaction) of 2 + polls
# inputs (its preparation, its reply and its polls), the compaction and
# the round's end
def bound(+cfg: RnState.Cfg) -> Nat:
  Nat.mul(Nat.max(RnState.Cfg.cap(cfg), 1n), 2n+Nat.mul(2n+Nat.add(RnState.Cfg.retries(cfg), RnState.Cfg.notes(cfg)), 2n+RnState.Cfg.polls(cfg)))
