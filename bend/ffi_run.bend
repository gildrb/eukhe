# ffi_run: the run's decisions (bend/run/decision.bend, "The decisions Rust
# calls") as one entry of the compiled core. Rust
# (crates/eukhe-durable/src/harness/generation/decide.rs, deferred.rs)
# encodes a request with eukhe_bend::wire::Writer: the tag of the
# decision, then its inputs; ffi answers the decision's value, or the
# wire's error form for a malformed request (never a default). The codec
# composes the primitives of bend/wire.bend; LAWS.bend section run proves
# that every request and every answer decodes to itself.

import Base
import ./wire.bend as W
import ./run/state.bend as MState
import ./run/recovery.bend as MRecovery
import ./run/decision.bend as MDecision

# A request: the decision Rust asks for and its inputs (the tag is the
# index of the constructor)
type Ask is Data:
  AskReply{l: MDecision.Lim, t: MDecision.At, reply: MState.Reply}
  AskEnded{m: MState.Ended}
  AskPrepare{compacted: Bool, th: MDecision.Th}
  AskCompact{over: Bool, got: MState.Got}
  AskRound{l: MDecision.Lim, count: Nat, stops: Bool, reset: Bool}
  AskRecover{rc: MRecovery.RCfg, s: MDecision.Stuck, k: MRecovery.Rk, row: Nat}
  AskPoll{retryable: Bool, failures: Nat, retries: Nat}

# Codecs
# ------

def put_lim(x: MDecision.Lim, rest: String) -> String:
  match x:
    case MDecision.Lim{rounds, wait, retries, notes}:
      W.put_nat(rounds, W.put_nat(wait, W.put_nat(retries, W.put_nat(notes, rest))))

def get_lim.f3(rounds: Nat, wait: Nat, retries: Nat, d: W.Dec<Nat>) -> W.Dec<MDecision.Lim>:
  match d:
    case W.Got{notes, r}:
      W.Got{MDecision.Lim{rounds, wait, retries, notes}, r}
    case W.Bad{}:
      W.Bad{}

def get_lim.f2(rounds: Nat, wait: Nat, d: W.Dec<Nat>) -> W.Dec<MDecision.Lim>:
  match d:
    case W.Got{retries, r}:
      get_lim.f3(rounds, wait, retries, W.get_nat(r))
    case W.Bad{}:
      W.Bad{}

def get_lim.f1(rounds: Nat, d: W.Dec<Nat>) -> W.Dec<MDecision.Lim>:
  match d:
    case W.Got{wait, r}:
      get_lim.f2(rounds, wait, W.get_nat(r))
    case W.Bad{}:
      W.Bad{}

def get_lim.f0(d: W.Dec<Nat>) -> W.Dec<MDecision.Lim>:
  match d:
    case W.Got{rounds, r}:
      get_lim.f1(rounds, W.get_nat(r))
    case W.Bad{}:
      W.Bad{}

def get_lim(s: String) -> W.Dec<MDecision.Lim>:
  get_lim.f0(W.get_nat(s))

def put_at(x: MDecision.At, rest: String) -> String:
  match x:
    case MDecision.At{attempt, notes, waited, compacted}:
      W.put_nat(attempt, W.put_nat(notes, W.put_nat(waited, W.put_bool(compacted, rest))))

def get_at.f3(attempt: Nat, notes: Nat, waited: Nat, d: W.Dec<Bool>) -> W.Dec<MDecision.At>:
  match d:
    case W.Got{compacted, r}:
      W.Got{MDecision.At{attempt, notes, waited, compacted}, r}
    case W.Bad{}:
      W.Bad{}

def get_at.f2(attempt: Nat, notes: Nat, d: W.Dec<Nat>) -> W.Dec<MDecision.At>:
  match d:
    case W.Got{waited, r}:
      get_at.f3(attempt, notes, waited, W.get_bool(r))
    case W.Bad{}:
      W.Bad{}

def get_at.f1(attempt: Nat, d: W.Dec<Nat>) -> W.Dec<MDecision.At>:
  match d:
    case W.Got{notes, r}:
      get_at.f2(attempt, notes, W.get_nat(r))
    case W.Bad{}:
      W.Bad{}

def get_at.f0(d: W.Dec<Nat>) -> W.Dec<MDecision.At>:
  match d:
    case W.Got{attempt, r}:
      get_at.f1(attempt, W.get_nat(r))
    case W.Bad{}:
      W.Bad{}

def get_at(s: String) -> W.Dec<MDecision.At>:
  get_at.f0(W.get_nat(s))

def put_reply(x: MState.Reply, rest: String) -> String:
  match x:
    case MState.Plain{}:
      W.put_nat(0n, rest)
    case MState.Calls{}:
      W.put_nat(1n, rest)
    case MState.Deferred{}:
      W.put_nat(2n, rest)
    case MState.Error{retryable, noted}:
      W.put_nat(3n, W.put_bool(retryable, W.put_bool(noted, rest)))
    case MState.Overflow{cut}:
      W.put_nat(4n, W.put_bool(cut, rest))

def get_reply.c3.f1(retryable: Bool, d: W.Dec<Bool>) -> W.Dec<MState.Reply>:
  match d:
    case W.Got{noted, r}:
      W.Got{MState.Error{retryable, noted}, r}
    case W.Bad{}:
      W.Bad{}

def get_reply.c3.f0(d: W.Dec<Bool>) -> W.Dec<MState.Reply>:
  match d:
    case W.Got{retryable, r}:
      get_reply.c3.f1(retryable, W.get_bool(r))
    case W.Bad{}:
      W.Bad{}

def get_reply.c4.f0(d: W.Dec<Bool>) -> W.Dec<MState.Reply>:
  match d:
    case W.Got{cut, r}:
      W.Got{MState.Overflow{cut}, r}
    case W.Bad{}:
      W.Bad{}

def get_reply.tag(d: W.Dec<Nat>) -> W.Dec<MState.Reply>:
  match d:
    case W.Got{n, r}:
      match n:
        case 0n:
          W.Got{MState.Plain{}, r}
        case 1n+p0:
          match p0:
            case 0n:
              W.Got{MState.Calls{}, r}
            case 1n+p1:
              match p1:
                case 0n:
                  W.Got{MState.Deferred{}, r}
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

def get_reply(s: String) -> W.Dec<MState.Reply>:
  get_reply.tag(W.get_nat(s))

def put_ended(x: MState.Ended, rest: String) -> String:
  match x:
    case MState.Ended{text, calls}:
      W.put_bool(text, W.put_bool(calls, rest))

def get_ended.f1(text: Bool, d: W.Dec<Bool>) -> W.Dec<MState.Ended>:
  match d:
    case W.Got{calls, r}:
      W.Got{MState.Ended{text, calls}, r}
    case W.Bad{}:
      W.Bad{}

def get_ended.f0(d: W.Dec<Bool>) -> W.Dec<MState.Ended>:
  match d:
    case W.Got{text, r}:
      get_ended.f1(text, W.get_bool(r))
    case W.Bad{}:
      W.Bad{}

def get_ended(s: String) -> W.Dec<MState.Ended>:
  get_ended.f0(W.get_bool(s))

def put_th(x: MDecision.Th, rest: String) -> String:
  match x:
    case MDecision.Under{}:
      W.put_nat(0n, rest)
    case MDecision.Background{}:
      W.put_nat(1n, rest)
    case MDecision.Blocking{}:
      W.put_nat(2n, rest)

def get_th.tag(d: W.Dec<Nat>) -> W.Dec<MDecision.Th>:
  match d:
    case W.Got{n, r}:
      match n:
        case 0n:
          W.Got{MDecision.Under{}, r}
        case 1n+p0:
          match p0:
            case 0n:
              W.Got{MDecision.Background{}, r}
            case 1n+p1:
              match p1:
                case 0n:
                  W.Got{MDecision.Blocking{}, r}
                case 1n+p2:
                  W.Bad{}
    case W.Bad{}:
      W.Bad{}

def get_th(s: String) -> W.Dec<MDecision.Th>:
  get_th.tag(W.get_nat(s))

def put_got(x: MState.Got, rest: String) -> String:
  match x:
    case MState.Built{}:
      W.put_nat(0n, rest)
    case MState.Kept{}:
      W.put_nat(1n, rest)
    case MState.Broke{}:
      W.put_nat(2n, rest)

def get_got.tag(d: W.Dec<Nat>) -> W.Dec<MState.Got>:
  match d:
    case W.Got{n, r}:
      match n:
        case 0n:
          W.Got{MState.Built{}, r}
        case 1n+p0:
          match p0:
            case 0n:
              W.Got{MState.Kept{}, r}
            case 1n+p1:
              match p1:
                case 0n:
                  W.Got{MState.Broke{}, r}
                case 1n+p2:
                  W.Bad{}
    case W.Bad{}:
      W.Bad{}

def get_got(s: String) -> W.Dec<MState.Got>:
  get_got.tag(W.get_nat(s))

def put_rcfg(x: MRecovery.RCfg, rest: String) -> String:
  match x:
    case MRecovery.RCfg{long, leak, redirect, repeat}:
      W.put_nat(long, W.put_nat(leak, W.put_nat(redirect, W.put_nat(repeat, rest))))

def get_rcfg.f3(long: Nat, leak: Nat, redirect: Nat, d: W.Dec<Nat>) -> W.Dec<MRecovery.RCfg>:
  match d:
    case W.Got{repeat, r}:
      W.Got{MRecovery.RCfg{long, leak, redirect, repeat}, r}
    case W.Bad{}:
      W.Bad{}

def get_rcfg.f2(long: Nat, leak: Nat, d: W.Dec<Nat>) -> W.Dec<MRecovery.RCfg>:
  match d:
    case W.Got{redirect, r}:
      get_rcfg.f3(long, leak, redirect, W.get_nat(r))
    case W.Bad{}:
      W.Bad{}

def get_rcfg.f1(long: Nat, d: W.Dec<Nat>) -> W.Dec<MRecovery.RCfg>:
  match d:
    case W.Got{leak, r}:
      get_rcfg.f2(long, leak, W.get_nat(r))
    case W.Bad{}:
      W.Bad{}

def get_rcfg.f0(d: W.Dec<Nat>) -> W.Dec<MRecovery.RCfg>:
  match d:
    case W.Got{long, r}:
      get_rcfg.f1(long, W.get_nat(r))
    case W.Bad{}:
      W.Bad{}

def get_rcfg(s: String) -> W.Dec<MRecovery.RCfg>:
  get_rcfg.f0(W.get_nat(s))

def put_stuck(x: MDecision.Stuck, rest: String) -> String:
  match x:
    case MDecision.Truncated{}:
      W.put_nat(0n, rest)
    case MDecision.Leaked{}:
      W.put_nat(1n, rest)
    case MDecision.Repeats{before}:
      W.put_nat(2n, W.put_nat(before, rest))

def get_stuck.c2.f0(d: W.Dec<Nat>) -> W.Dec<MDecision.Stuck>:
  match d:
    case W.Got{before, r}:
      W.Got{MDecision.Repeats{before}, r}
    case W.Bad{}:
      W.Bad{}

def get_stuck.tag(d: W.Dec<Nat>) -> W.Dec<MDecision.Stuck>:
  match d:
    case W.Got{n, r}:
      match n:
        case 0n:
          W.Got{MDecision.Truncated{}, r}
        case 1n+p0:
          match p0:
            case 0n:
              W.Got{MDecision.Leaked{}, r}
            case 1n+p1:
              match p1:
                case 0n:
                  get_stuck.c2.f0(W.get_nat(r))
                case 1n+p2:
                  W.Bad{}
    case W.Bad{}:
      W.Bad{}

def get_stuck(s: String) -> W.Dec<MDecision.Stuck>:
  get_stuck.tag(W.get_nat(s))

def put_rk(x: MRecovery.Rk, rest: String) -> String:
  match x:
    case MRecovery.Free{}:
      W.put_nat(0n, rest)
    case MRecovery.Longs{}:
      W.put_nat(1n, rest)
    case MRecovery.Leaks{}:
      W.put_nat(2n, rest)
    case MRecovery.Loops{}:
      W.put_nat(3n, rest)

def get_rk.tag(d: W.Dec<Nat>) -> W.Dec<MRecovery.Rk>:
  match d:
    case W.Got{n, r}:
      match n:
        case 0n:
          W.Got{MRecovery.Free{}, r}
        case 1n+p0:
          match p0:
            case 0n:
              W.Got{MRecovery.Longs{}, r}
            case 1n+p1:
              match p1:
                case 0n:
                  W.Got{MRecovery.Leaks{}, r}
                case 1n+p2:
                  match p2:
                    case 0n:
                      W.Got{MRecovery.Loops{}, r}
                    case 1n+p3:
                      W.Bad{}
    case W.Bad{}:
      W.Bad{}

def get_rk(s: String) -> W.Dec<MRecovery.Rk>:
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

def get_ask.c0.f2(l: MDecision.Lim, t: MDecision.At, d: W.Dec<MState.Reply>) -> W.Dec<Ask>:
  match d:
    case W.Got{reply, r}:
      W.Got{AskReply{l, t, reply}, r}
    case W.Bad{}:
      W.Bad{}

def get_ask.c0.f1(l: MDecision.Lim, d: W.Dec<MDecision.At>) -> W.Dec<Ask>:
  match d:
    case W.Got{t, r}:
      get_ask.c0.f2(l, t, get_reply(r))
    case W.Bad{}:
      W.Bad{}

def get_ask.c0.f0(d: W.Dec<MDecision.Lim>) -> W.Dec<Ask>:
  match d:
    case W.Got{l, r}:
      get_ask.c0.f1(l, get_at(r))
    case W.Bad{}:
      W.Bad{}

def get_ask.c1.f0(d: W.Dec<MState.Ended>) -> W.Dec<Ask>:
  match d:
    case W.Got{m, r}:
      W.Got{AskEnded{m}, r}
    case W.Bad{}:
      W.Bad{}

def get_ask.c2.f1(compacted: Bool, d: W.Dec<MDecision.Th>) -> W.Dec<Ask>:
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

def get_ask.c3.f1(over: Bool, d: W.Dec<MState.Got>) -> W.Dec<Ask>:
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

def get_ask.c4.f3(l: MDecision.Lim, count: Nat, stops: Bool, d: W.Dec<Bool>) -> W.Dec<Ask>:
  match d:
    case W.Got{reset, r}:
      W.Got{AskRound{l, count, stops, reset}, r}
    case W.Bad{}:
      W.Bad{}

def get_ask.c4.f2(l: MDecision.Lim, count: Nat, d: W.Dec<Bool>) -> W.Dec<Ask>:
  match d:
    case W.Got{stops, r}:
      get_ask.c4.f3(l, count, stops, W.get_bool(r))
    case W.Bad{}:
      W.Bad{}

def get_ask.c4.f1(l: MDecision.Lim, d: W.Dec<Nat>) -> W.Dec<Ask>:
  match d:
    case W.Got{count, r}:
      get_ask.c4.f2(l, count, W.get_bool(r))
    case W.Bad{}:
      W.Bad{}

def get_ask.c4.f0(d: W.Dec<MDecision.Lim>) -> W.Dec<Ask>:
  match d:
    case W.Got{l, r}:
      get_ask.c4.f1(l, W.get_nat(r))
    case W.Bad{}:
      W.Bad{}

def get_ask.c5.f3(rc: MRecovery.RCfg, s: MDecision.Stuck, k: MRecovery.Rk, d: W.Dec<Nat>) -> W.Dec<Ask>:
  match d:
    case W.Got{row, r}:
      W.Got{AskRecover{rc, s, k, row}, r}
    case W.Bad{}:
      W.Bad{}

def get_ask.c5.f2(rc: MRecovery.RCfg, s: MDecision.Stuck, d: W.Dec<MRecovery.Rk>) -> W.Dec<Ask>:
  match d:
    case W.Got{k, r}:
      get_ask.c5.f3(rc, s, k, W.get_nat(r))
    case W.Bad{}:
      W.Bad{}

def get_ask.c5.f1(rc: MRecovery.RCfg, d: W.Dec<MDecision.Stuck>) -> W.Dec<Ask>:
  match d:
    case W.Got{s, r}:
      get_ask.c5.f2(rc, s, get_rk(r))
    case W.Bad{}:
      W.Bad{}

def get_ask.c5.f0(d: W.Dec<MRecovery.RCfg>) -> W.Dec<Ask>:
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

def put_then(x: MDecision.Then, rest: String) -> String:
  match x:
    case MDecision.DoAnswer{}:
      W.put_nat(0n, rest)
    case MDecision.DoTools{}:
      W.put_nat(1n, rest)
    case MDecision.DoPoll{}:
      W.put_nat(2n, rest)
    case MDecision.DoRetry{}:
      W.put_nat(3n, rest)
    case MDecision.DoNote{}:
      W.put_nat(4n, rest)
    case MDecision.DoCompact{}:
      W.put_nat(5n, rest)
    case MDecision.DoFail{}:
      W.put_nat(6n, rest)
    case MDecision.DoLate{}:
      W.put_nat(7n, rest)

def get_then.tag(d: W.Dec<Nat>) -> W.Dec<MDecision.Then>:
  match d:
    case W.Got{n, r}:
      match n:
        case 0n:
          W.Got{MDecision.DoAnswer{}, r}
        case 1n+p0:
          match p0:
            case 0n:
              W.Got{MDecision.DoTools{}, r}
            case 1n+p1:
              match p1:
                case 0n:
                  W.Got{MDecision.DoPoll{}, r}
                case 1n+p2:
                  match p2:
                    case 0n:
                      W.Got{MDecision.DoRetry{}, r}
                    case 1n+p3:
                      match p3:
                        case 0n:
                          W.Got{MDecision.DoNote{}, r}
                        case 1n+p4:
                          match p4:
                            case 0n:
                              W.Got{MDecision.DoCompact{}, r}
                            case 1n+p5:
                              match p5:
                                case 0n:
                                  W.Got{MDecision.DoFail{}, r}
                                case 1n+p6:
                                  match p6:
                                    case 0n:
                                      W.Got{MDecision.DoLate{}, r}
                                    case 1n+p7:
                                      W.Bad{}
    case W.Bad{}:
      W.Bad{}

def get_then(s: String) -> W.Dec<MDecision.Then>:
  get_then.tag(W.get_nat(s))

def put_prepared(x: MDecision.Prepared, rest: String) -> String:
  match x:
    case MDecision.Waits{}:
      W.put_nat(0n, rest)
    case MDecision.Sends{background}:
      W.put_nat(1n, W.put_bool(background, rest))

def get_prepared.c1.f0(d: W.Dec<Bool>) -> W.Dec<MDecision.Prepared>:
  match d:
    case W.Got{background, r}:
      W.Got{MDecision.Sends{background}, r}
    case W.Bad{}:
      W.Bad{}

def get_prepared.tag(d: W.Dec<Nat>) -> W.Dec<MDecision.Prepared>:
  match d:
    case W.Got{n, r}:
      match n:
        case 0n:
          W.Got{MDecision.Waits{}, r}
        case 1n+p0:
          match p0:
            case 0n:
              get_prepared.c1.f0(W.get_bool(r))
            case 1n+p1:
              W.Bad{}
    case W.Bad{}:
      W.Bad{}

def get_prepared(s: String) -> W.Dec<MDecision.Prepared>:
  get_prepared.tag(W.get_nat(s))

def put_end(x: MDecision.End, rest: String) -> String:
  match x:
    case MDecision.EndStop{}:
      W.put_nat(0n, rest)
    case MDecision.EndReset{}:
      W.put_nat(1n, rest)
    case MDecision.EndCapped{}:
      W.put_nat(2n, rest)
    case MDecision.EndNext{count}:
      W.put_nat(3n, W.put_nat(count, rest))

def get_end.c3.f0(d: W.Dec<Nat>) -> W.Dec<MDecision.End>:
  match d:
    case W.Got{count, r}:
      W.Got{MDecision.EndNext{count}, r}
    case W.Bad{}:
      W.Bad{}

def get_end.tag(d: W.Dec<Nat>) -> W.Dec<MDecision.End>:
  match d:
    case W.Got{n, r}:
      match n:
        case 0n:
          W.Got{MDecision.EndStop{}, r}
        case 1n+p0:
          match p0:
            case 0n:
              W.Got{MDecision.EndReset{}, r}
            case 1n+p1:
              match p1:
                case 0n:
                  W.Got{MDecision.EndCapped{}, r}
                case 1n+p2:
                  match p2:
                    case 0n:
                      get_end.c3.f0(W.get_nat(r))
                    case 1n+p3:
                      W.Bad{}
    case W.Bad{}:
      W.Bad{}

def get_end(s: String) -> W.Dec<MDecision.End>:
  get_end.tag(W.get_nat(s))

def put_help(x: MDecision.Help, rest: String) -> String:
  match x:
    case MDecision.Runs{}:
      W.put_nat(0n, rest)
    case MDecision.Redoes{row}:
      W.put_nat(1n, W.put_nat(row, rest))
    case MDecision.Stands{}:
      W.put_nat(2n, rest)
    case MDecision.Quits{}:
      W.put_nat(3n, rest)

def get_help.c1.f0(d: W.Dec<Nat>) -> W.Dec<MDecision.Help>:
  match d:
    case W.Got{row, r}:
      W.Got{MDecision.Redoes{row}, r}
    case W.Bad{}:
      W.Bad{}

def get_help.tag(d: W.Dec<Nat>) -> W.Dec<MDecision.Help>:
  match d:
    case W.Got{n, r}:
      match n:
        case 0n:
          W.Got{MDecision.Runs{}, r}
        case 1n+p0:
          match p0:
            case 0n:
              get_help.c1.f0(W.get_nat(r))
            case 1n+p1:
              match p1:
                case 0n:
                  W.Got{MDecision.Stands{}, r}
                case 1n+p2:
                  match p2:
                    case 0n:
                      W.Got{MDecision.Quits{}, r}
                    case 1n+p3:
                      W.Bad{}
    case W.Bad{}:
      W.Bad{}

def get_help(s: String) -> W.Dec<MDecision.Help>:
  get_help.tag(W.get_nat(s))

# The answer to a request: the value of its decision
def answer(a: Ask) -> String:
  match a:
    case AskReply{l, t, reply}:
      put_then(MDecision.decide.reply(l, t, reply), "")
    case AskEnded{m}:
      put_reply(MState.Ended.reply(m), "")
    case AskPrepare{compacted, th}:
      put_prepared(MDecision.decide.prepare(compacted, th), "")
    case AskCompact{over, got}:
      W.put_bool(MDecision.decide.compact(over, got), "")
    case AskRound{l, count, stops, reset}:
      put_end(MDecision.decide.round(l, count, stops, reset), "")
    case AskRecover{rc, s, k, row}:
      put_help(MDecision.decide.recover(rc, s, k, row), "")
    case AskPoll{retryable, failures, retries}:
      W.put_bool(MDecision.decide.poll(retryable, failures, retries), "")

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
