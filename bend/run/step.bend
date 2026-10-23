# run: the steps of the machine: prepare, call, retry/note, compaction, round and tools, one input (step) and a whole run

import Base
import ./state.bend as RnState

# Steps
# -----

# prepare (before_request): a blocking threshold compaction when the
# context is over it, a cut exists and the generation has not compacted;
# else the request goes out
def prepare.cut(+cfg: RnState.Cfg, cut: Bool, r: Nat, c: Nat, a: Nat, n: Nat) -> RnState.St:
  match cut c:
    case True{} 1n+d:
      RnState.St{RnState.Compact{False{}}, r, d, a, n, RnState.Cfg.polls(cfg)}
    case True{} 0n:
      RnState.St{RnState.Call{}, r, 0n, a, n, RnState.Cfg.polls(cfg)}
    case False{} c:
      RnState.St{RnState.Call{}, r, c, a, n, RnState.Cfg.polls(cfg)}

def prepare(+cfg: RnState.Cfg, reply: RnState.Reply, r: Nat, c: Nat, a: Nat, n: Nat) -> RnState.St:
  match reply:
    case RnState.Overflow{cut}:
      prepare.cut(cfg, cut, r, c, a, n)
    case RnState.Plain{}:
      RnState.St{RnState.Call{}, r, c, a, n, RnState.Cfg.polls(cfg)}
    case RnState.Calls{}:
      RnState.St{RnState.Call{}, r, c, a, n, RnState.Cfg.polls(cfg)}
    case RnState.Deferred{}:
      RnState.St{RnState.Call{}, r, c, a, n, RnState.Cfg.polls(cfg)}
    case RnState.Error{retryable, noted}:
      RnState.St{RnState.Call{}, r, c, a, n, RnState.Cfg.polls(cfg)}

# an error that is not noted (after_reply) retries when it is retryable
# and retries are left; it spends a retry, never a note
def retry(+cfg: RnState.Cfg, retryable: Bool, r: Nat, c: Nat, a: Nat, n: Nat, p: Nat) -> RnState.St:
  match retryable a:
    case True{} 1n+b:
      RnState.St{RnState.Prepare{}, r, c, b, n, RnState.Cfg.polls(cfg)}
    case True{} 0n:
      RnState.St{RnState.Failed{RnState.Model{}}, r, c, 0n, n, p}
    case False{} a:
      RnState.St{RnState.Failed{RnState.Model{}}, r, c, a, n, p}

# a noted reply (after_reply, retry_note) retries with a note while notes
# are left, retryable or not; it spends a note, never a retry
def note(+cfg: RnState.Cfg, r: Nat, c: Nat, a: Nat, n: Nat, p: Nat) -> RnState.St:
  match n:
    case 1n+m:
      RnState.St{RnState.Prepare{}, r, c, a, m, RnState.Cfg.polls(cfg)}
    case 0n:
      RnState.St{RnState.Failed{RnState.Model{}}, r, c, a, 0n, p}

def error(+cfg: RnState.Cfg, retryable: Bool, noted: Bool, r: Nat, c: Nat, a: Nat, n: Nat, p: Nat) -> RnState.St:
  match noted:
    case True{}:
      note(cfg, r, c, a, n, p)
    case False{}:
      retry(cfg, retryable, r, c, a, n, p)

# an overflow (after_reply) compacts once a generation, when a cut exists
def overflow(cut: Bool, r: Nat, c: Nat, a: Nat, n: Nat, p: Nat) -> RnState.St:
  match cut c:
    case True{} 1n+d:
      RnState.St{RnState.Compact{True{}}, r, d, a, n, p}
    case True{} 0n:
      RnState.St{RnState.Failed{RnState.Model{}}, r, 0n, a, n, p}
    case False{} c:
      RnState.St{RnState.Failed{RnState.Model{}}, r, c, a, n, p}

# a reply to a request or a poll (after_reply)
def call(+cfg: RnState.Cfg, reply: RnState.Reply, r: Nat, c: Nat, a: Nat, n: Nat, p: Nat) -> RnState.St:
  match reply:
    case RnState.Plain{}:
      RnState.St{RnState.Answered{}, r, c, a, n, p}
    case RnState.Calls{}:
      RnState.St{RnState.Tools{}, r, c, a, n, p}
    case RnState.Deferred{}:
      match p:
        case 0n:
          RnState.St{RnState.Failed{RnState.Polls{}}, r, c, a, n, 0n}
        case 1n+q:
          RnState.St{RnState.Call{}, r, c, a, n, q}
    case RnState.Error{retryable, noted}:
      error(cfg, retryable, noted, r, c, a, n, p)
    case RnState.Overflow{cut}:
      overflow(cut, r, c, a, n, p)

# a compaction ends (after_compaction): the request is prepared again, or
# the run fails. An overflow's compaction must append its entry, else the
# request still overflows; a threshold one that found nothing leaves a
# request that may still fit, one that failed a context it judged too large
def compact(+cfg: RnState.Cfg, over: Bool, got: RnState.Got, r: Nat, c: Nat, a: Nat, n: Nat, p: Nat) -> RnState.St:
  match over got:
    case over RnState.Built{}:
      RnState.St{RnState.Prepare{}, r, c, a, n, RnState.Cfg.polls(cfg)}
    case True{} RnState.Kept{}:
      RnState.St{RnState.Failed{RnState.Model{}}, r, c, a, n, p}
    case False{} RnState.Kept{}:
      RnState.St{RnState.Prepare{}, r, c, a, n, RnState.Cfg.polls(cfg)}
    case over RnState.Broke{}:
      RnState.St{RnState.Failed{RnState.Model{}}, r, c, a, n, p}

# a counted round (decide.round; Rust's `round_end`): the cap fails
# it, else a queued reset ends the run, else the next generation prepares
# with fresh limits
def round(+cfg: RnState.Cfg, reset: Bool, r: Nat, c: Nat, a: Nat, n: Nat, p: Nat) -> RnState.St:
  match reset r:
    case reset 0n:
      RnState.St{RnState.Failed{RnState.Rounds{}}, 0n, c, a, n, p}
    case True{} 1n+s:
      RnState.St{RnState.Answered{}, s, c, a, n, p}
    case False{} 1n+s:
      RnState.St{RnState.Prepare{}, s, 1n, RnState.Cfg.retries(cfg), RnState.Cfg.notes(cfg), RnState.Cfg.polls(cfg)}

# a round ends (RoundEnd::Stop): a control stops the run uncounted, else the
# round counts
def tools(+cfg: RnState.Cfg, fin: RnState.Fin, r: Nat, c: Nat, a: Nat, n: Nat, p: Nat) -> RnState.St:
  match fin:
    case RnState.Stops{}:
      RnState.St{RnState.Answered{}, r, c, a, n, p}
    case RnState.Goes{}:
      round(cfg, False{}, r, c, a, n, p)
    case RnState.Resets{}:
      round(cfg, True{}, r, c, a, n, p)

# one input; an abort ends a live run, an ended run stays as it is
def step.ph(+cfg: RnState.Cfg, ph: RnState.Ph, e: RnState.Ev, r: Nat, c: Nat, a: Nat, n: Nat, p: Nat) -> RnState.St:
  match ph e:
    case RnState.Answered{} e:
      RnState.St{RnState.Answered{}, r, c, a, n, p}
    case RnState.Aborted{} e:
      RnState.St{RnState.Aborted{}, r, c, a, n, p}
    case RnState.Failed{why} e:
      RnState.St{RnState.Failed{why}, r, c, a, n, p}
    case RnState.Prepare{} RnState.Abort{}:
      RnState.St{RnState.Aborted{}, r, c, a, n, p}
    case RnState.Call{} RnState.Abort{}:
      RnState.St{RnState.Aborted{}, r, c, a, n, p}
    case RnState.Compact{over} RnState.Abort{}:
      RnState.St{RnState.Aborted{}, r, c, a, n, p}
    case RnState.Tools{} RnState.Abort{}:
      RnState.St{RnState.Aborted{}, r, c, a, n, p}
    case RnState.Prepare{} RnState.Go{reply, fin, got}:
      prepare(cfg, reply, r, c, a, n)
    case RnState.Call{} RnState.Go{reply, fin, got}:
      call(cfg, reply, r, c, a, n, p)
    case RnState.Compact{over} RnState.Go{reply, fin, got}:
      compact(cfg, over, got, r, c, a, n, p)
    case RnState.Tools{} RnState.Go{reply, fin, got}:
      tools(cfg, fin, r, c, a, n, p)

def step(+cfg: RnState.Cfg, s: RnState.St, e: RnState.Ev) -> RnState.St:
  match s:
    case RnState.St{ph, r, c, a, n, p}:
      step.ph(cfg, ph, e, r, c, a, n, p)

def run.go(evs: List<&2, RnState.Ev>, +cfg: RnState.Cfg, s: RnState.St) -> RnState.St:
  match evs:
    case Nil{}:
      s
    case e <> rest:
      run.go(rest, cfg, step(cfg, s, e))

# the run after evs
def run(+cfg: RnState.Cfg, evs: List<&2, RnState.Ev>) -> RnState.St:
  run.go(evs, cfg, RnState.init(cfg))
