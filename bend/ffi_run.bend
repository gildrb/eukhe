# ffi_run: the run's decisions (bend/run.bend, "The decisions Rust
# calls") as one entry of the compiled core. Rust
# (crates/eukhe-durable/src/harness/generation/decide.rs, deferred.rs)
# encodes a request with eukhe_bend::wire::Writer: the tag of the
# decision, then its inputs; ffi answers the decision's value, or the
# wire's error form for a malformed request (never a default). The codec
# composes the primitives of bend/wire.bend; LAWS.bend section run proves
# that every request and every answer decodes to itself.

import Base
import ./wire.bend as W
import ./run.bend as M

# A request: the decision Rust asks for and its inputs (the tag is the
# index of the constructor)
type Ask is Data:
  AskReply{l: M.Lim, t: M.At, reply: M.Reply}
  AskEnded{m: M.Ended}
  AskPrepare{compacted: Bool, th: M.Th}
  AskCompact{over: Bool, got: M.Got}
  AskRound{l: M.Lim, count: Nat, stops: Bool, reset: Bool}
  AskRecover{rc: M.RCfg, s: M.Stuck, k: M.Rk, row: Nat}
  AskPoll{retryable: Bool, failures: Nat, retries: Nat}

# Codecs
# ------

def put_lim(x: M.Lim, rest: String) -> String:
  match x:
    case M.Lim{rounds, wait, retries, notes}:
      W.put_nat(rounds, W.put_nat(wait, W.put_nat(retries, W.put_nat(notes, rest))))

def get_lim.f3(rounds: Nat, wait: Nat, retries: Nat, d: W.Dec<Nat>) -> W.Dec<M.Lim>:
  match d:
    case W.Got{notes, r}:
      W.Got{M.Lim{rounds, wait, retries, notes}, r}
    case W.Bad{}:
      W.Bad{}

def get_lim.f2(rounds: Nat, wait: Nat, d: W.Dec<Nat>) -> W.Dec<M.Lim>:
  match d:
    case W.Got{retries, r}:
      get_lim.f3(rounds, wait, retries, W.get_nat(r))
    case W.Bad{}:
      W.Bad{}

def get_lim.f1(rounds: Nat, d: W.Dec<Nat>) -> W.Dec<M.Lim>:
  match d:
    case W.Got{wait, r}:
      get_lim.f2(rounds, wait, W.get_nat(r))
    case W.Bad{}:
      W.Bad{}

def get_lim.f0(d: W.Dec<Nat>) -> W.Dec<M.Lim>:
  match d:
    case W.Got{rounds, r}:
      get_lim.f1(rounds, W.get_nat(r))
    case W.Bad{}:
      W.Bad{}

def get_lim(s: String) -> W.Dec<M.Lim>:
  get_lim.f0(W.get_nat(s))

def put_at(x: M.At, rest: String) -> String:
  match x:
    case M.At{attempt, notes, waited, compacted}:
      W.put_nat(attempt, W.put_nat(notes, W.put_nat(waited, W.put_bool(compacted, rest))))

def get_at.f3(attempt: Nat, notes: Nat, waited: Nat, d: W.Dec<Bool>) -> W.Dec<M.At>:
  match d:
    case W.Got{compacted, r}:
      W.Got{M.At{attempt, notes, waited, compacted}, r}
    case W.Bad{}:
      W.Bad{}

def get_at.f2(attempt: Nat, notes: Nat, d: W.Dec<Nat>) -> W.Dec<M.At>:
  match d:
    case W.Got{waited, r}:
      get_at.f3(attempt, notes, waited, W.get_bool(r))
    case W.Bad{}:
      W.Bad{}

def get_at.f1(attempt: Nat, d: W.Dec<Nat>) -> W.Dec<M.At>:
  match d:
    case W.Got{notes, r}:
      get_at.f2(attempt, notes, W.get_nat(r))
    case W.Bad{}:
      W.Bad{}

def get_at.f0(d: W.Dec<Nat>) -> W.Dec<M.At>:
  match d:
    case W.Got{attempt, r}:
      get_at.f1(attempt, W.get_nat(r))
    case W.Bad{}:
      W.Bad{}

def get_at(s: String) -> W.Dec<M.At>:
  get_at.f0(W.get_nat(s))

def put_reply(x: M.Reply, rest: String) -> String:
  match x:
    case M.Plain{}:
      W.put_nat(0n, rest)
    case M.Calls{}:
      W.put_nat(1n, rest)
    case M.Deferred{}:
      W.put_nat(2n, rest)
    case M.Error{retryable, noted}:
      W.put_nat(3n, W.put_bool(retryable, W.put_bool(noted, rest)))
    case M.Overflow{cut}:
      W.put_nat(4n, W.put_bool(cut, rest))

def get_reply.c3.f1(retryable: Bool, d: W.Dec<Bool>) -> W.Dec<M.Reply>:
  match d:
    case W.Got{noted, r}:
      W.Got{M.Error{retryable, noted}, r}
    case W.Bad{}:
      W.Bad{}

def get_reply.c3.f0(d: W.Dec<Bool>) -> W.Dec<M.Reply>:
  match d:
    case W.Got{retryable, r}:
      get_reply.c3.f1(retryable, W.get_bool(r))
    case W.Bad{}:
      W.Bad{}

def get_reply.c4.f0(d: W.Dec<Bool>) -> W.Dec<M.Reply>:
  match d:
    case W.Got{cut, r}:
      W.Got{M.Overflow{cut}, r}
    case W.Bad{}:
      W.Bad{}

def get_reply.tag(d: W.Dec<Nat>) -> W.Dec<M.Reply>:
  match d:
    case W.Got{n, r}:
      match n:
        case 0n:
          W.Got{M.Plain{}, r}
        case 1n+p0:
          match p0:
            case 0n:
              W.Got{M.Calls{}, r}
            case 1n+p1:
              match p1:
                case 0n:
                  W.Got{M.Deferred{}, r}
                case 1n+p2:
                  match p2:
                    case 0n:
                      get_reply.c3.f0(W.get_bool(r))
                    case 1n+p3:
                      match p3:
                        case 0n:
                          get_reply.c4.f0(W.get_bool(r))
                        case 1n+p4:
                          W.Bad{}
    case W.Bad{}:
      W.Bad{}

def get_reply(s: String) -> W.Dec<M.Reply>:
  get_reply.tag(W.get_nat(s))

def put_ended(x: M.Ended, rest: String) -> String:
  match x:
    case M.Ended{text, calls}:
      W.put_bool(text, W.put_bool(calls, rest))

def get_ended.f1(text: Bool, d: W.Dec<Bool>) -> W.Dec<M.Ended>:
  match d:
    case W.Got{calls, r}:
      W.Got{M.Ended{text, calls}, r}
    case W.Bad{}:
      W.Bad{}

def get_ended.f0(d: W.Dec<Bool>) -> W.Dec<M.Ended>:
  match d:
    case W.Got{text, r}:
      get_ended.f1(text, W.get_bool(r))
    case W.Bad{}:
      W.Bad{}

def get_ended(s: String) -> W.Dec<M.Ended>:
  get_ended.f0(W.get_bool(s))

def put_th(x: M.Th, rest: String) -> String:
  match x:
    case M.Under{}:
      W.put_nat(0n, rest)
    case M.Background{}:
      W.put_nat(1n, rest)
    case M.Blocking{}:
      W.put_nat(2n, rest)

def get_th.tag(d: W.Dec<Nat>) -> W.Dec<M.Th>:
  match d:
    case W.Got{n, r}:
      match n:
        case 0n:
          W.Got{M.Under{}, r}
        case 1n+p0:
          match p0:
            case 0n:
              W.Got{M.Background{}, r}
            case 1n+p1:
              match p1:
                case 0n:
                  W.Got{M.Blocking{}, r}
                case 1n+p2:
                  W.Bad{}
    case W.Bad{}:
      W.Bad{}

def get_th(s: String) -> W.Dec<M.Th>:
  get_th.tag(W.get_nat(s))

def put_got(x: M.Got, rest: String) -> String:
  match x:
    case M.Built{}:
      W.put_nat(0n, rest)
    case M.Kept{}:
      W.put_nat(1n, rest)
    case M.Broke{}:
      W.put_nat(2n, rest)

def get_got.tag(d: W.Dec<Nat>) -> W.Dec<M.Got>:
  match d:
    case W.Got{n, r}:
      match n:
        case 0n:
          W.Got{M.Built{}, r}
        case 1n+p0:
          match p0:
            case 0n:
              W.Got{M.Kept{}, r}
            case 1n+p1:
              match p1:
                case 0n:
                  W.Got{M.Broke{}, r}
                case 1n+p2:
                  W.Bad{}
    case W.Bad{}:
      W.Bad{}

def get_got(s: String) -> W.Dec<M.Got>:
  get_got.tag(W.get_nat(s))

def put_rcfg(x: M.RCfg, rest: String) -> String:
  match x:
    case M.RCfg{long, leak, redirect, repeat}:
      W.put_nat(long, W.put_nat(leak, W.put_nat(redirect, W.put_nat(repeat, rest))))

def get_rcfg.f3(long: Nat, leak: Nat, redirect: Nat, d: W.Dec<Nat>) -> W.Dec<M.RCfg>:
  match d:
    case W.Got{repeat, r}:
      W.Got{M.RCfg{long, leak, redirect, repeat}, r}
    case W.Bad{}:
      W.Bad{}

def get_rcfg.f2(long: Nat, leak: Nat, d: W.Dec<Nat>) -> W.Dec<M.RCfg>:
  match d:
    case W.Got{redirect, r}:
      get_rcfg.f3(long, leak, redirect, W.get_nat(r))
    case W.Bad{}:
      W.Bad{}

def get_rcfg.f1(long: Nat, d: W.Dec<Nat>) -> W.Dec<M.RCfg>:
  match d:
    case W.Got{leak, r}:
      get_rcfg.f2(long, leak, W.get_nat(r))
    case W.Bad{}:
      W.Bad{}

def get_rcfg.f0(d: W.Dec<Nat>) -> W.Dec<M.RCfg>:
  match d:
    case W.Got{long, r}:
      get_rcfg.f1(long, W.get_nat(r))
    case W.Bad{}:
      W.Bad{}

def get_rcfg(s: String) -> W.Dec<M.RCfg>:
  get_rcfg.f0(W.get_nat(s))

def put_stuck(x: M.Stuck, rest: String) -> String:
  match x:
    case M.Truncated{}:
      W.put_nat(0n, rest)
    case M.Leaked{}:
      W.put_nat(1n, rest)
    case M.Repeats{before}:
      W.put_nat(2n, W.put_nat(before, rest))

def get_stuck.c2.f0(d: W.Dec<Nat>) -> W.Dec<M.Stuck>:
  match d:
    case W.Got{before, r}:
      W.Got{M.Repeats{before}, r}
    case W.Bad{}:
      W.Bad{}

def get_stuck.tag(d: W.Dec<Nat>) -> W.Dec<M.Stuck>:
  match d:
    case W.Got{n, r}:
      match n:
        case 0n:
          W.Got{M.Truncated{}, r}
        case 1n+p0:
          match p0:
            case 0n:
              W.Got{M.Leaked{}, r}
            case 1n+p1:
              match p1:
                case 0n:
                  get_stuck.c2.f0(W.get_nat(r))
                case 1n+p2:
                  W.Bad{}
    case W.Bad{}:
      W.Bad{}

def get_stuck(s: String) -> W.Dec<M.Stuck>:
  get_stuck.tag(W.get_nat(s))

def put_rk(x: M.Rk, rest: String) -> String:
  match x:
    case M.Free{}:
      W.put_nat(0n, rest)
    case M.Longs{}:
      W.put_nat(1n, rest)
    case M.Leaks{}:
      W.put_nat(2n, rest)
    case M.Loops{}:
      W.put_nat(3n, rest)

def get_rk.tag(d: W.Dec<Nat>) -> W.Dec<M.Rk>:
  match d:
    case W.Got{n, r}:
      match n:
        case 0n:
          W.Got{M.Free{}, r}
        case 1n+p0:
          match p0:
            case 0n:
              W.Got{M.Longs{}, r}
            case 1n+p1:
              match p1:
                case 0n:
                  W.Got{M.Leaks{}, r}
                case 1n+p2:
                  match p2:
                    case 0n:
                      W.Got{M.Loops{}, r}
                    case 1n+p3:
                      W.Bad{}
    case W.Bad{}:
      W.Bad{}

def get_rk(s: String) -> W.Dec<M.Rk>:
  get_rk.tag(W.get_nat(s))

def put_ask(x: Ask, rest: String) -> String:
  match x:
    case AskReply{l, t, reply}:
      W.put_nat(0n, put_lim(l, put_at(t, put_reply(reply, rest))))
    case AskEnded{m}:
      W.put_nat(1n, put_ended(m, rest))
    case AskPrepare{compacted, th}:
      W.put_nat(2n, W.put_bool(compacted, put_th(th, rest)))
    case AskCompact{over, got}:
      W.put_nat(3n, W.put_bool(over, put_got(got, rest)))
    case AskRound{l, count, stops, reset}:
      W.put_nat(4n, put_lim(l, W.put_nat(count, W.put_bool(stops, W.put_bool(reset, rest)))))
    case AskRecover{rc, s, k, row}:
      W.put_nat(5n, put_rcfg(rc, put_stuck(s, put_rk(k, W.put_nat(row, rest)))))
    case AskPoll{retryable, failures, retries}:
      W.put_nat(6n, W.put_bool(retryable, W.put_nat(failures, W.put_nat(retries, rest))))

def get_ask.c0.f2(l: M.Lim, t: M.At, d: W.Dec<M.Reply>) -> W.Dec<Ask>:
  match d:
    case W.Got{reply, r}:
      W.Got{AskReply{l, t, reply}, r}
    case W.Bad{}:
      W.Bad{}

def get_ask.c0.f1(l: M.Lim, d: W.Dec<M.At>) -> W.Dec<Ask>:
  match d:
    case W.Got{t, r}:
      get_ask.c0.f2(l, t, get_reply(r))
    case W.Bad{}:
      W.Bad{}

def get_ask.c0.f0(d: W.Dec<M.Lim>) -> W.Dec<Ask>:
  match d:
    case W.Got{l, r}:
      get_ask.c0.f1(l, get_at(r))
    case W.Bad{}:
      W.Bad{}

def get_ask.c1.f0(d: W.Dec<M.Ended>) -> W.Dec<Ask>:
  match d:
    case W.Got{m, r}:
      W.Got{AskEnded{m}, r}
    case W.Bad{}:
      W.Bad{}

def get_ask.c2.f1(compacted: Bool, d: W.Dec<M.Th>) -> W.Dec<Ask>:
  match d:
    case W.Got{th, r}:
      W.Got{AskPrepare{compacted, th}, r}
    case W.Bad{}:
      W.Bad{}

def get_ask.c2.f0(d: W.Dec<Bool>) -> W.Dec<Ask>:
  match d:
    case W.Got{compacted, r}:
      get_ask.c2.f1(compacted, get_th(r))
    case W.Bad{}:
      W.Bad{}

def get_ask.c3.f1(over: Bool, d: W.Dec<M.Got>) -> W.Dec<Ask>:
  match d:
    case W.Got{got, r}:
      W.Got{AskCompact{over, got}, r}
    case W.Bad{}:
      W.Bad{}

def get_ask.c3.f0(d: W.Dec<Bool>) -> W.Dec<Ask>:
  match d:
    case W.Got{over, r}:
      get_ask.c3.f1(over, get_got(r))
    case W.Bad{}:
      W.Bad{}

def get_ask.c4.f3(l: M.Lim, count: Nat, stops: Bool, d: W.Dec<Bool>) -> W.Dec<Ask>:
  match d:
    case W.Got{reset, r}:
      W.Got{AskRound{l, count, stops, reset}, r}
    case W.Bad{}:
      W.Bad{}

def get_ask.c4.f2(l: M.Lim, count: Nat, d: W.Dec<Bool>) -> W.Dec<Ask>:
  match d:
    case W.Got{stops, r}:
      get_ask.c4.f3(l, count, stops, W.get_bool(r))
    case W.Bad{}:
      W.Bad{}

def get_ask.c4.f1(l: M.Lim, d: W.Dec<Nat>) -> W.Dec<Ask>:
  match d:
    case W.Got{count, r}:
      get_ask.c4.f2(l, count, W.get_bool(r))
    case W.Bad{}:
      W.Bad{}

def get_ask.c4.f0(d: W.Dec<M.Lim>) -> W.Dec<Ask>:
  match d:
    case W.Got{l, r}:
      get_ask.c4.f1(l, W.get_nat(r))
    case W.Bad{}:
      W.Bad{}

def get_ask.c5.f3(rc: M.RCfg, s: M.Stuck, k: M.Rk, d: W.Dec<Nat>) -> W.Dec<Ask>:
  match d:
    case W.Got{row, r}:
      W.Got{AskRecover{rc, s, k, row}, r}
    case W.Bad{}:
      W.Bad{}

def get_ask.c5.f2(rc: M.RCfg, s: M.Stuck, d: W.Dec<M.Rk>) -> W.Dec<Ask>:
  match d:
    case W.Got{k, r}:
      get_ask.c5.f3(rc, s, k, W.get_nat(r))
    case W.Bad{}:
      W.Bad{}

def get_ask.c5.f1(rc: M.RCfg, d: W.Dec<M.Stuck>) -> W.Dec<Ask>:
  match d:
    case W.Got{s, r}:
      get_ask.c5.f2(rc, s, get_rk(r))
    case W.Bad{}:
      W.Bad{}

def get_ask.c5.f0(d: W.Dec<M.RCfg>) -> W.Dec<Ask>:
  match d:
    case W.Got{rc, r}:
      get_ask.c5.f1(rc, get_stuck(r))
    case W.Bad{}:
      W.Bad{}

def get_ask.c6.f2(retryable: Bool, failures: Nat, d: W.Dec<Nat>) -> W.Dec<Ask>:
  match d:
    case W.Got{retries, r}:
      W.Got{AskPoll{retryable, failures, retries}, r}
    case W.Bad{}:
      W.Bad{}

def get_ask.c6.f1(retryable: Bool, d: W.Dec<Nat>) -> W.Dec<Ask>:
  match d:
    case W.Got{failures, r}:
      get_ask.c6.f2(retryable, failures, W.get_nat(r))
    case W.Bad{}:
      W.Bad{}

def get_ask.c6.f0(d: W.Dec<Bool>) -> W.Dec<Ask>:
  match d:
    case W.Got{retryable, r}:
      get_ask.c6.f1(retryable, W.get_nat(r))
    case W.Bad{}:
      W.Bad{}

def get_ask.tag(d: W.Dec<Nat>) -> W.Dec<Ask>:
  match d:
    case W.Got{n, r}:
      match n:
        case 0n:
          get_ask.c0.f0(get_lim(r))
        case 1n+p0:
          match p0:
            case 0n:
              get_ask.c1.f0(get_ended(r))
            case 1n+p1:
              match p1:
                case 0n:
                  get_ask.c2.f0(W.get_bool(r))
                case 1n+p2:
                  match p2:
                    case 0n:
                      get_ask.c3.f0(W.get_bool(r))
                    case 1n+p3:
                      match p3:
                        case 0n:
                          get_ask.c4.f0(get_lim(r))
                        case 1n+p4:
                          match p4:
                            case 0n:
                              get_ask.c5.f0(get_rcfg(r))
                            case 1n+p5:
                              match p5:
                                case 0n:
                                  get_ask.c6.f0(W.get_bool(r))
                                case 1n+p6:
                                  W.Bad{}
    case W.Bad{}:
      W.Bad{}

def get_ask(s: String) -> W.Dec<Ask>:
  get_ask.tag(W.get_nat(s))

def put_then(x: M.Then, rest: String) -> String:
  match x:
    case M.DoAnswer{}:
      W.put_nat(0n, rest)
    case M.DoTools{}:
      W.put_nat(1n, rest)
    case M.DoPoll{}:
      W.put_nat(2n, rest)
    case M.DoRetry{}:
      W.put_nat(3n, rest)
    case M.DoNote{}:
      W.put_nat(4n, rest)
    case M.DoCompact{}:
      W.put_nat(5n, rest)
    case M.DoFail{}:
      W.put_nat(6n, rest)
    case M.DoLate{}:
      W.put_nat(7n, rest)

def get_then.tag(d: W.Dec<Nat>) -> W.Dec<M.Then>:
  match d:
    case W.Got{n, r}:
      match n:
        case 0n:
          W.Got{M.DoAnswer{}, r}
        case 1n+p0:
          match p0:
            case 0n:
              W.Got{M.DoTools{}, r}
            case 1n+p1:
              match p1:
                case 0n:
                  W.Got{M.DoPoll{}, r}
                case 1n+p2:
                  match p2:
                    case 0n:
                      W.Got{M.DoRetry{}, r}
                    case 1n+p3:
                      match p3:
                        case 0n:
                          W.Got{M.DoNote{}, r}
                        case 1n+p4:
                          match p4:
                            case 0n:
                              W.Got{M.DoCompact{}, r}
                            case 1n+p5:
                              match p5:
                                case 0n:
                                  W.Got{M.DoFail{}, r}
                                case 1n+p6:
                                  match p6:
                                    case 0n:
                                      W.Got{M.DoLate{}, r}
                                    case 1n+p7:
                                      W.Bad{}
    case W.Bad{}:
      W.Bad{}

def get_then(s: String) -> W.Dec<M.Then>:
  get_then.tag(W.get_nat(s))

def put_prepared(x: M.Prepared, rest: String) -> String:
  match x:
    case M.Waits{}:
      W.put_nat(0n, rest)
    case M.Sends{background}:
      W.put_nat(1n, W.put_bool(background, rest))

def get_prepared.c1.f0(d: W.Dec<Bool>) -> W.Dec<M.Prepared>:
  match d:
    case W.Got{background, r}:
      W.Got{M.Sends{background}, r}
    case W.Bad{}:
      W.Bad{}

def get_prepared.tag(d: W.Dec<Nat>) -> W.Dec<M.Prepared>:
  match d:
    case W.Got{n, r}:
      match n:
        case 0n:
          W.Got{M.Waits{}, r}
        case 1n+p0:
          match p0:
            case 0n:
              get_prepared.c1.f0(W.get_bool(r))
            case 1n+p1:
              W.Bad{}
    case W.Bad{}:
      W.Bad{}

def get_prepared(s: String) -> W.Dec<M.Prepared>:
  get_prepared.tag(W.get_nat(s))

def put_end(x: M.End, rest: String) -> String:
  match x:
    case M.EndStop{}:
      W.put_nat(0n, rest)
    case M.EndReset{}:
      W.put_nat(1n, rest)
    case M.EndCapped{}:
      W.put_nat(2n, rest)
    case M.EndNext{count}:
      W.put_nat(3n, W.put_nat(count, rest))

def get_end.c3.f0(d: W.Dec<Nat>) -> W.Dec<M.End>:
  match d:
    case W.Got{count, r}:
      W.Got{M.EndNext{count}, r}
    case W.Bad{}:
      W.Bad{}

def get_end.tag(d: W.Dec<Nat>) -> W.Dec<M.End>:
  match d:
    case W.Got{n, r}:
      match n:
        case 0n:
          W.Got{M.EndStop{}, r}
        case 1n+p0:
          match p0:
            case 0n:
              W.Got{M.EndReset{}, r}
            case 1n+p1:
              match p1:
                case 0n:
                  W.Got{M.EndCapped{}, r}
                case 1n+p2:
                  match p2:
                    case 0n:
                      get_end.c3.f0(W.get_nat(r))
                    case 1n+p3:
                      W.Bad{}
    case W.Bad{}:
      W.Bad{}

def get_end(s: String) -> W.Dec<M.End>:
  get_end.tag(W.get_nat(s))

def put_help(x: M.Help, rest: String) -> String:
  match x:
    case M.Runs{}:
      W.put_nat(0n, rest)
    case M.Redoes{row}:
      W.put_nat(1n, W.put_nat(row, rest))
    case M.Stands{}:
      W.put_nat(2n, rest)
    case M.Quits{}:
      W.put_nat(3n, rest)

def get_help.c1.f0(d: W.Dec<Nat>) -> W.Dec<M.Help>:
  match d:
    case W.Got{row, r}:
      W.Got{M.Redoes{row}, r}
    case W.Bad{}:
      W.Bad{}

def get_help.tag(d: W.Dec<Nat>) -> W.Dec<M.Help>:
  match d:
    case W.Got{n, r}:
      match n:
        case 0n:
          W.Got{M.Runs{}, r}
        case 1n+p0:
          match p0:
            case 0n:
              get_help.c1.f0(W.get_nat(r))
            case 1n+p1:
              match p1:
                case 0n:
                  W.Got{M.Stands{}, r}
                case 1n+p2:
                  match p2:
                    case 0n:
                      W.Got{M.Quits{}, r}
                    case 1n+p3:
                      W.Bad{}
    case W.Bad{}:
      W.Bad{}

def get_help(s: String) -> W.Dec<M.Help>:
  get_help.tag(W.get_nat(s))

# The answer to a request: the value of its decision
def answer(a: Ask) -> String:
  match a:
    case AskReply{l, t, reply}:
      put_then(M.decide.reply(l, t, reply), "")
    case AskEnded{m}:
      put_reply(M.Ended.reply(m), "")
    case AskPrepare{compacted, th}:
      put_prepared(M.decide.prepare(compacted, th), "")
    case AskCompact{over, got}:
      W.put_bool(M.decide.compact(over, got), "")
    case AskRound{l, count, stops, reset}:
      put_end(M.decide.round(l, count, stops, reset), "")
    case AskRecover{rc, s, k, row}:
      put_help(M.decide.recover(rc, s, k, row), "")
    case AskPoll{retryable, failures, retries}:
      W.put_bool(M.decide.poll(retryable, failures, retries), "")

def ffi.end(whole: Bool, a: Ask) -> String:
  match whole:
    case True{}:
      answer(a)
    case False{}:
      W.err("run: input left over after the request")

def ffi.go(d: W.Dec<Ask>) -> String:
  match d:
    case W.Got{a, rest}:
      ffi.end(W.end(rest), a)
    case W.Bad{}:
      W.err("run: malformed request")

# The entry: the request is the whole input
def ffi(input: String) -> String:
  ffi.go(get_ask(input))
