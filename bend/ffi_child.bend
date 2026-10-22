import Base
import ./wire.bend as W
import ./child.bend as M

# ffi_child: the child task's three decisions (bend/child.bend) as one
# entry of the compiled Bend core. The request is a constructor:
#   0 verdict: Cfg (stall, fails), W (tok: Maybe<Nat>, left, tries), e,
#     Obs (Busy 0 (Maybe<Nat>) | Lost 1 | Answered 2 (Bool) | Broke 3 |
#     Gone 4), Mode (Inbox 0 | Silent 1); reply: the Call (Watches 0 (W) |
#     Reports 1 (Report) | Settles 2 (Maybe<Report>))
#   1 move: the fate (Maybe of Queued 0 | Withdrawn 1 | Placed 2), the id
#     n; reply: the Move (Submit 0 (n) | Await 1 | Resubmit 2 (n) |
#     Delivered 3)
#   2 abort: the Ph (Watching 0 (W) | Owing 1 (Report, n) | Ended 2), the
#     delete flag; reply: the Ph
# Report: Completed 0 | Failed 1 | Cancelled 2 | Stalled 3 | Unreachable 4.

# Encoders
# --------

def put_maybe_nat(m: Maybe<&2, Nat>, rest: String) -> String:
  match m:
    case None{}:
      W.put_nat(0n, rest)
    case Some{x}:
      W.put_nat(1n, W.put_nat(x, rest))

def put_w(w: M.W, rest: String) -> String:
  match w:
    case M.W{t, l, n}:
      put_maybe_nat(t, W.put_nat(l, W.put_nat(n, rest)))

def put_cfg(c: M.Cfg, rest: String) -> String:
  match c:
    case M.Cfg{s, f}:
      W.put_nat(s, W.put_nat(f, rest))

def put_obs(o: M.Obs, rest: String) -> String:
  match o:
    case M.Busy{t}:
      W.put_nat(0n, put_maybe_nat(t, rest))
    case M.Lost{}:
      W.put_nat(1n, rest)
    case M.Answered{r}:
      W.put_nat(2n, W.put_bool(r, rest))
    case M.Broke{}:
      W.put_nat(3n, rest)
    case M.Gone{}:
      W.put_nat(4n, rest)

def put_mode(m: M.Mode, rest: String) -> String:
  match m:
    case M.Inbox{}:
      W.put_nat(0n, rest)
    case M.Silent{}:
      W.put_nat(1n, rest)

def put_report(k: M.Report, rest: String) -> String:
  match k:
    case M.Completed{}:
      W.put_nat(0n, rest)
    case M.Failed{}:
      W.put_nat(1n, rest)
    case M.Cancelled{}:
      W.put_nat(2n, rest)
    case M.Stalled{}:
      W.put_nat(3n, rest)
    case M.Unreachable{}:
      W.put_nat(4n, rest)

def put_call(c: M.Call, rest: String) -> String:
  match c:
    case M.Watches{w}:
      W.put_nat(0n, put_w(w, rest))
    case M.Reports{k}:
      W.put_nat(1n, put_report(k, rest))
    case M.Settles{why}:
      match why:
        case None{}:
          W.put_nat(2n, W.put_nat(0n, rest))
        case Some{k}:
          W.put_nat(2n, W.put_nat(1n, put_report(k, rest)))

def put_fate(f: M.Fate, rest: String) -> String:
  match f:
    case M.Queued{}:
      W.put_nat(0n, rest)
    case M.Withdrawn{}:
      W.put_nat(1n, rest)
    case M.Placed{}:
      W.put_nat(2n, rest)

def put_mfate(f: Maybe<&2, M.Fate>, rest: String) -> String:
  match f:
    case None{}:
      W.put_nat(0n, rest)
    case Some{x}:
      W.put_nat(1n, put_fate(x, rest))

def put_move(m: M.Move, rest: String) -> String:
  match m:
    case M.Submit{n}:
      W.put_nat(0n, W.put_nat(n, rest))
    case M.Await{}:
      W.put_nat(1n, rest)
    case M.Resubmit{n}:
      W.put_nat(2n, W.put_nat(n, rest))
    case M.Delivered{}:
      W.put_nat(3n, rest)

def put_ph(p: M.Ph, rest: String) -> String:
  match p:
    case M.Watching{w}:
      W.put_nat(0n, put_w(w, rest))
    case M.Owing{k, n}:
      W.put_nat(1n, put_report(k, W.put_nat(n, rest)))
    case M.Ended{}:
      W.put_nat(2n, rest)

# The requests, as Rust writes them
type Req is Data:
  AskVerdict{cfg: M.Cfg, w: M.W, e: Nat, o: M.Obs, m: M.Mode}
  AskMove{f: Maybe<&2, M.Fate>, n: Nat}
  AskAbort{ph: M.Ph, del: Bool}

def put_req(r: Req) -> String:
  match r:
    case AskVerdict{c, w, e, o, m}:
      W.put_nat(0n, put_cfg(c, put_w(w, W.put_nat(e, put_obs(o, put_mode(m, ""))))))
    case AskMove{f, n}:
      W.put_nat(1n, put_mfate(f, W.put_nat(n, "")))
    case AskAbort{p, d}:
      W.put_nat(2n, put_ph(p, W.put_bool(d, "")))

# Decoders
# --------
# A small tag (below 5) from a Nat's decoder.

type Tag is Data:
  T0{}
  T1{}
  T2{}
  T3{}
  T4{}
  TBad{}

def tag.of(n: Nat) -> Tag:
  match n:
    case 0n:
      T0{}
    case 1n+a:
      match a:
        case 0n:
          T1{}
        case 1n+b:
          match b:
            case 0n:
              T2{}
            case 1n+c:
              match c:
                case 0n:
                  T3{}
                case 1n+d:
                  match d:
                    case 0n:
                      T4{}
                    case 1n+e:
                      TBad{}

def get_maybe_nat.some(r: W.Dec<Nat>) -> W.Dec<Maybe<&2, Nat>>:
  match r:
    case W.Got{x, s}:
      W.Got{Some{x}, s}
    case W.Bad{}:
      W.Bad{}

def get_maybe_nat.tag(t: Tag, s: String) -> W.Dec<Maybe<&2, Nat>>:
  match t:
    case T0{}:
      W.Got{None{}, s}
    case T1{}:
      get_maybe_nat.some(W.get_nat(s))
    case T2{}:
      W.Bad{}
    case T3{}:
      W.Bad{}
    case T4{}:
      W.Bad{}
    case TBad{}:
      W.Bad{}

def get_maybe_nat.go(r: W.Dec<Nat>) -> W.Dec<Maybe<&2, Nat>>:
  match r:
    case W.Got{t, s}:
      get_maybe_nat.tag(tag.of(t), s)
    case W.Bad{}:
      W.Bad{}

def get_maybe_nat(s: String) -> W.Dec<Maybe<&2, Nat>>:
  get_maybe_nat.go(W.get_nat(s))

def get_w.n(t: Maybe<&2, Nat>, +l: Nat, r: W.Dec<Nat>) -> W.Dec<M.W>:
  match r:
    case W.Got{n, s}:
      W.Got{M.W{t, l, n}, s}
    case W.Bad{}:
      W.Bad{}

def get_w.l(t: Maybe<&2, Nat>, r: W.Dec<Nat>) -> W.Dec<M.W>:
  match r:
    case W.Got{+l, s}:
      get_w.n(t, l, W.get_nat(s))
    case W.Bad{}:
      W.Bad{}

def get_w.t(r: W.Dec<Maybe<&2, Nat>>) -> W.Dec<M.W>:
  match r:
    case W.Got{t, s}:
      get_w.l(t, W.get_nat(s))
    case W.Bad{}:
      W.Bad{}

def get_w(s: String) -> W.Dec<M.W>:
  get_w.t(get_maybe_nat(s))

def get_cfg.f(+st: Nat, r: W.Dec<Nat>) -> W.Dec<M.Cfg>:
  match r:
    case W.Got{f, s}:
      W.Got{M.Cfg{st, f}, s}
    case W.Bad{}:
      W.Bad{}

def get_cfg.s(r: W.Dec<Nat>) -> W.Dec<M.Cfg>:
  match r:
    case W.Got{+st, s}:
      get_cfg.f(st, W.get_nat(s))
    case W.Bad{}:
      W.Bad{}

def get_cfg(s: String) -> W.Dec<M.Cfg>:
  get_cfg.s(W.get_nat(s))

def get_obs.busy(r: W.Dec<Maybe<&2, Nat>>) -> W.Dec<M.Obs>:
  match r:
    case W.Got{t, s}:
      W.Got{M.Busy{t}, s}
    case W.Bad{}:
      W.Bad{}

def get_obs.answered(r: W.Dec<Bool>) -> W.Dec<M.Obs>:
  match r:
    case W.Got{b, s}:
      W.Got{M.Answered{b}, s}
    case W.Bad{}:
      W.Bad{}

def get_obs.tag(t: Tag, s: String) -> W.Dec<M.Obs>:
  match t:
    case T0{}:
      get_obs.busy(get_maybe_nat(s))
    case T1{}:
      W.Got{M.Lost{}, s}
    case T2{}:
      get_obs.answered(W.get_bool(s))
    case T3{}:
      W.Got{M.Broke{}, s}
    case T4{}:
      W.Got{M.Gone{}, s}
    case TBad{}:
      W.Bad{}

def get_obs.go(r: W.Dec<Nat>) -> W.Dec<M.Obs>:
  match r:
    case W.Got{t, s}:
      get_obs.tag(tag.of(t), s)
    case W.Bad{}:
      W.Bad{}

def get_obs(s: String) -> W.Dec<M.Obs>:
  get_obs.go(W.get_nat(s))

def get_mode.tag(t: Tag, s: String) -> W.Dec<M.Mode>:
  match t:
    case T0{}:
      W.Got{M.Inbox{}, s}
    case T1{}:
      W.Got{M.Silent{}, s}
    case T2{}:
      W.Bad{}
    case T3{}:
      W.Bad{}
    case T4{}:
      W.Bad{}
    case TBad{}:
      W.Bad{}

def get_mode.go(r: W.Dec<Nat>) -> W.Dec<M.Mode>:
  match r:
    case W.Got{t, s}:
      get_mode.tag(tag.of(t), s)
    case W.Bad{}:
      W.Bad{}

def get_mode(s: String) -> W.Dec<M.Mode>:
  get_mode.go(W.get_nat(s))

def get_report.tag(t: Tag, s: String) -> W.Dec<M.Report>:
  match t:
    case T0{}:
      W.Got{M.Completed{}, s}
    case T1{}:
      W.Got{M.Failed{}, s}
    case T2{}:
      W.Got{M.Cancelled{}, s}
    case T3{}:
      W.Got{M.Stalled{}, s}
    case T4{}:
      W.Got{M.Unreachable{}, s}
    case TBad{}:
      W.Bad{}

def get_report.go(r: W.Dec<Nat>) -> W.Dec<M.Report>:
  match r:
    case W.Got{t, s}:
      get_report.tag(tag.of(t), s)
    case W.Bad{}:
      W.Bad{}

def get_report(s: String) -> W.Dec<M.Report>:
  get_report.go(W.get_nat(s))

def get_fate.tag(t: Tag, s: String) -> W.Dec<M.Fate>:
  match t:
    case T0{}:
      W.Got{M.Queued{}, s}
    case T1{}:
      W.Got{M.Withdrawn{}, s}
    case T2{}:
      W.Got{M.Placed{}, s}
    case T3{}:
      W.Bad{}
    case T4{}:
      W.Bad{}
    case TBad{}:
      W.Bad{}

def get_fate.go(r: W.Dec<Nat>) -> W.Dec<M.Fate>:
  match r:
    case W.Got{t, s}:
      get_fate.tag(tag.of(t), s)
    case W.Bad{}:
      W.Bad{}

def get_fate(s: String) -> W.Dec<M.Fate>:
  get_fate.go(W.get_nat(s))

def get_mfate.some(r: W.Dec<M.Fate>) -> W.Dec<Maybe<&2, M.Fate>>:
  match r:
    case W.Got{x, s}:
      W.Got{Some{x}, s}
    case W.Bad{}:
      W.Bad{}

def get_mfate.tag(t: Tag, s: String) -> W.Dec<Maybe<&2, M.Fate>>:
  match t:
    case T0{}:
      W.Got{None{}, s}
    case T1{}:
      get_mfate.some(get_fate(s))
    case T2{}:
      W.Bad{}
    case T3{}:
      W.Bad{}
    case T4{}:
      W.Bad{}
    case TBad{}:
      W.Bad{}

def get_mfate.go(r: W.Dec<Nat>) -> W.Dec<Maybe<&2, M.Fate>>:
  match r:
    case W.Got{t, s}:
      get_mfate.tag(tag.of(t), s)
    case W.Bad{}:
      W.Bad{}

def get_mfate(s: String) -> W.Dec<Maybe<&2, M.Fate>>:
  get_mfate.go(W.get_nat(s))

def get_ph.watching(r: W.Dec<M.W>) -> W.Dec<M.Ph>:
  match r:
    case W.Got{w, s}:
      W.Got{M.Watching{w}, s}
    case W.Bad{}:
      W.Bad{}

def get_ph.n(k: M.Report, r: W.Dec<Nat>) -> W.Dec<M.Ph>:
  match r:
    case W.Got{n, s}:
      W.Got{M.Owing{k, n}, s}
    case W.Bad{}:
      W.Bad{}

def get_ph.owing(r: W.Dec<M.Report>) -> W.Dec<M.Ph>:
  match r:
    case W.Got{k, s}:
      get_ph.n(k, W.get_nat(s))
    case W.Bad{}:
      W.Bad{}

def get_ph.tag(t: Tag, s: String) -> W.Dec<M.Ph>:
  match t:
    case T0{}:
      get_ph.watching(get_w(s))
    case T1{}:
      get_ph.owing(get_report(s))
    case T2{}:
      W.Got{M.Ended{}, s}
    case T3{}:
      W.Bad{}
    case T4{}:
      W.Bad{}
    case TBad{}:
      W.Bad{}

def get_ph.go(r: W.Dec<Nat>) -> W.Dec<M.Ph>:
  match r:
    case W.Got{t, s}:
      get_ph.tag(tag.of(t), s)
    case W.Bad{}:
      W.Bad{}

def get_ph(s: String) -> W.Dec<M.Ph>:
  get_ph.go(W.get_nat(s))

# A request: each decoder answers the request's next field, then calls the
# next; the last checks that nothing is left.

def verdict.fin(left: Bool, +c: M.Cfg, +w: M.W, +e: Nat, o: M.Obs, m: M.Mode) -> String:
  match left:
    case True{}:
      put_call(M.verdict(c, w, e, o, m), "")
    case False{}:
      W.err("child: input left over")

def verdict.m(+c: M.Cfg, +w: M.W, +e: Nat, +o: M.Obs, r: W.Dec<M.Mode>) -> String:
  match r:
    case W.Got{m, s}:
      verdict.fin(W.end(s), c, w, e, o, m)
    case W.Bad{}:
      W.err("child: bad mode")

def verdict.o(+c: M.Cfg, +w: M.W, +e: Nat, r: W.Dec<M.Obs>) -> String:
  match r:
    case W.Got{+o, s}:
      verdict.m(c, w, e, o, get_mode(s))
    case W.Bad{}:
      W.err("child: bad poll")

def verdict.e(+c: M.Cfg, +w: M.W, r: W.Dec<Nat>) -> String:
  match r:
    case W.Got{+e, s}:
      verdict.o(c, w, e, get_obs(s))
    case W.Bad{}:
      W.err("child: bad elapsed ms")

def verdict.w(+c: M.Cfg, r: W.Dec<M.W>) -> String:
  match r:
    case W.Got{+w, s}:
      verdict.e(c, w, W.get_nat(s))
    case W.Bad{}:
      W.err("child: bad clock")

def verdict.c(r: W.Dec<M.Cfg>) -> String:
  match r:
    case W.Got{+c, s}:
      verdict.w(c, get_w(s))
    case W.Bad{}:
      W.err("child: bad settings")

def move.fin(left: Bool, f: Maybe<&2, M.Fate>, +n: Nat) -> String:
  match left:
    case True{}:
      put_move(M.owe.next(f, n), "")
    case False{}:
      W.err("child: input left over")

def move.n(f: Maybe<&2, M.Fate>, r: W.Dec<Nat>) -> String:
  match r:
    case W.Got{+n, s}:
      move.fin(W.end(s), f, n)
    case W.Bad{}:
      W.err("child: bad id")

def move.f(r: W.Dec<Maybe<&2, M.Fate>>) -> String:
  match r:
    case W.Got{f, s}:
      move.n(f, W.get_nat(s))
    case W.Bad{}:
      W.err("child: bad fate")

def abort.fin(left: Bool, ph: M.Ph, d: Bool) -> String:
  match left:
    case True{}:
      put_ph(M.cut.ph(ph, d), "")
    case False{}:
      W.err("child: input left over")

def abort.d(ph: M.Ph, r: W.Dec<Bool>) -> String:
  match r:
    case W.Got{d, s}:
      abort.fin(W.end(s), ph, d)
    case W.Bad{}:
      W.err("child: bad delete flag")

def abort.ph(r: W.Dec<M.Ph>) -> String:
  match r:
    case W.Got{ph, s}:
      abort.d(ph, W.get_bool(s))
    case W.Bad{}:
      W.err("child: bad phase")

def run.tag(t: Tag, s: String) -> String:
  match t:
    case T0{}:
      verdict.c(get_cfg(s))
    case T1{}:
      move.f(get_mfate(s))
    case T2{}:
      abort.ph(get_ph(s))
    case T3{}:
      W.err("child: unknown request")
    case T4{}:
      W.err("child: unknown request")
    case TBad{}:
      W.err("child: unknown request")

def run(r: W.Dec<Nat>) -> String:
  match r:
    case W.Got{t, s}:
      run.tag(tag.of(t), s)
    case W.Bad{}:
      W.err("child: bad request")

# the entry
def ffi(input: String) -> String:
  run(W.get_nat(input))
