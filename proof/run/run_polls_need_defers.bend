# eukhe: the proof of LAW run_polls_need_defers

import Base
import ../../bend/run/measure.bend as RnMeasure
import ../../bend/run/state.bend as RnState
import ../../bend/run/step.bend as RnStep
import ../../laws/run.bend as Run
import ../base/nat.bend as LNat

# The polls
# ---------
# After any inputs, with k = the deferred replies in a row: in a call,
# k + p = polls (the polls left and the deferred replies so far make the
# cap); a run the poll cap failed had k = polls + 1.

def PInv.why(+P: Nat, why: RnState.Why, +k: Nat) -> Type:
  match why:
    case RnState.Polls{}:
      {k == 1n+P : Nat}
    case RnState.Model{}:
      Unit
    case RnState.Rounds{}:
      Unit

def PInv.ph(+P: Nat, ph: RnState.Ph, +p: Nat, +k: Nat) -> Type:
  match ph:
    case RnState.Call{}:
      {Nat.add(k, p) == P : Nat}
    case RnState.Failed{why}:
      PInv.why(P, why, k)
    case RnState.Prepare{}:
      Unit
    case RnState.Compact{over}:
      Unit
    case RnState.Tools{}:
      Unit
    case RnState.Answered{}:
      Unit
    case RnState.Aborted{}:
      Unit

def PInv(+cfg: RnState.Cfg, +s: RnState.St, +k: Nat) -> Type:
  PInv.ph(RnState.Cfg.polls(cfg), RnState.St.ph(s), RnState.St.p(s), k)

def pinv_prepare_cut(+cap: Nat, +P: Nat, +A: Nat, +N: Nat, cut: Bool, +r: Nat, c: Nat, +a: Nat, +n: Nat) -> PInv(RnState.Cfg{cap, P, A, N}, RnStep.prepare.cut(RnState.Cfg{cap, P, A, N}, cut, r, c, a, n), 0n):
  match cut c:
    case True{} 1n+d:
      Unit{}
    case True{} 0n:
      {==}
    case False{} c:
      {==}

def pinv_prepare(+cap: Nat, +P: Nat, +A: Nat, +N: Nat, reply: RnState.Reply, +r: Nat, +c: Nat, +a: Nat, +n: Nat) -> PInv(RnState.Cfg{cap, P, A, N}, RnStep.prepare(RnState.Cfg{cap, P, A, N}, reply, r, c, a, n), 0n):
  match reply:
    case RnState.Overflow{cut}:
      pinv_prepare_cut(cap, P, A, N, cut, r, c, a, n)
    case RnState.Plain{}:
      {==}
    case RnState.Calls{}:
      {==}
    case RnState.Deferred{}:
      {==}
    case RnState.Error{retryable, noted}:
      {==}

def pinv_retry(+cap: Nat, +P: Nat, +A: Nat, +N: Nat, retryable: Bool, +r: Nat, +c: Nat, a: Nat, +n: Nat, +p: Nat) -> PInv(RnState.Cfg{cap, P, A, N}, RnStep.retry(RnState.Cfg{cap, P, A, N}, retryable, r, c, a, n, p), 0n):
  match retryable a:
    case True{} 1n+b:
      Unit{}
    case True{} 0n:
      Unit{}
    case False{} a:
      Unit{}

def pinv_note(+cap: Nat, +P: Nat, +A: Nat, +N: Nat, +r: Nat, +c: Nat, +a: Nat, n: Nat, +p: Nat) -> PInv(RnState.Cfg{cap, P, A, N}, RnStep.note(RnState.Cfg{cap, P, A, N}, r, c, a, n, p), 0n):
  match n:
    case 1n+m:
      Unit{}
    case 0n:
      Unit{}

def pinv_error(+cap: Nat, +P: Nat, +A: Nat, +N: Nat, retryable: Bool, noted: Bool, +r: Nat, +c: Nat, +a: Nat, +n: Nat, +p: Nat) -> PInv(RnState.Cfg{cap, P, A, N}, RnStep.error(RnState.Cfg{cap, P, A, N}, retryable, noted, r, c, a, n, p), 0n):
  match noted:
    case True{}:
      pinv_note(cap, P, A, N, r, c, a, n, p)
    case False{}:
      pinv_retry(cap, P, A, N, retryable, r, c, a, n, p)

def pinv_overflow(+cap: Nat, +P: Nat, +A: Nat, +N: Nat, cut: Bool, +r: Nat, c: Nat, +a: Nat, +n: Nat, +p: Nat) -> PInv(RnState.Cfg{cap, P, A, N}, RnStep.overflow(cut, r, c, a, n, p), 0n):
  match cut c:
    case True{} 1n+d:
      Unit{}
    case True{} 0n:
      Unit{}
    case False{} c:
      Unit{}

# the last poll's deferred reply makes polls + 1 in a row
def polls_full(+k: Nat, -P: Nat, i: {Nat.add(k, 0n) == P : Nat}) -> {1n+k == 1n+P : Nat}:
  %i : {1n+k == 1n+_ : Nat}
  %Equal.sym(Nat, Nat.add(k, 0n), k, LNat.add_zero(k)) : {1n+k == 1n+_ : Nat}
  {==}

def pinv_call(+cap: Nat, +P: Nat, +A: Nat, +N: Nat, reply: RnState.Reply, +r: Nat, +c: Nat, +a: Nat, +n: Nat, p: Nat, +k: Nat, i: {Nat.add(k, p) == P : Nat}) -> PInv(RnState.Cfg{cap, P, A, N}, RnStep.call(RnState.Cfg{cap, P, A, N}, reply, r, c, a, n, p), RnMeasure.defers.reply(reply, k)):
  match reply:
    case RnState.Plain{}:
      Unit{}
    case RnState.Calls{}:
      Unit{}
    case RnState.Deferred{}:
      match p:
        case 0n:
          polls_full(k, P, i)
        case 1n+q:
          %i : {1n+Nat.add(k, q) == _ : Nat}
          LNat.add_succ_r(k, q)
    case RnState.Error{retryable, noted}:
      pinv_error(cap, P, A, N, retryable, noted, r, c, a, n, p)
    case RnState.Overflow{cut}:
      pinv_overflow(cap, P, A, N, cut, r, c, a, n, p)

def pinv_compact(+cap: Nat, +P: Nat, +A: Nat, +N: Nat, over: Bool, got: RnState.Got, +r: Nat, +c: Nat, +a: Nat, +n: Nat, +p: Nat) -> PInv(RnState.Cfg{cap, P, A, N}, RnStep.compact(RnState.Cfg{cap, P, A, N}, over, got, r, c, a, n, p), 0n):
  match over got:
    case over RnState.Built{}:
      Unit{}
    case True{} RnState.Kept{}:
      Unit{}
    case False{} RnState.Kept{}:
      Unit{}
    case over RnState.Broke{}:
      Unit{}

def pinv_round(+cap: Nat, +P: Nat, +A: Nat, +N: Nat, reset: Bool, r: Nat, +c: Nat, +a: Nat, +n: Nat, +p: Nat) -> PInv(RnState.Cfg{cap, P, A, N}, RnStep.round(RnState.Cfg{cap, P, A, N}, reset, r, c, a, n, p), 0n):
  match reset r:
    case reset 0n:
      Unit{}
    case True{} 1n+s:
      Unit{}
    case False{} 1n+s:
      Unit{}

def pinv_tools(+cap: Nat, +P: Nat, +A: Nat, +N: Nat, fin: RnState.Fin, +r: Nat, +c: Nat, +a: Nat, +n: Nat, +p: Nat) -> PInv(RnState.Cfg{cap, P, A, N}, RnStep.tools(RnState.Cfg{cap, P, A, N}, fin, r, c, a, n, p), 0n):
  match fin:
    case RnState.Stops{}:
      Unit{}
    case RnState.Goes{}:
      pinv_round(cap, P, A, N, False{}, r, c, a, n, p)
    case RnState.Resets{}:
      pinv_round(cap, P, A, N, True{}, r, c, a, n, p)

# one input keeps the poll invariant
def pinv_step(+cfg: RnState.Cfg, +s: RnState.St, +e: RnState.Ev, +k: Nat, i: PInv(cfg, s, k)) -> PInv(cfg, RnStep.step(cfg, s, e), RnMeasure.defers.at(RnState.St.ph(s), e, k)):
  match cfg:
    case RnState.Cfg{cap, pp, aa, nn}:
      match s:
        case RnState.St{ph, r, c, a, n, p}:
          match ph e:
            case RnState.Answered{} e:
              i
            case RnState.Aborted{} e:
              i
            case RnState.Failed{why} e:
              i
            case RnState.Prepare{} RnState.Abort{}:
              Unit{}
            case RnState.Call{} RnState.Abort{}:
              Unit{}
            case RnState.Compact{over} RnState.Abort{}:
              Unit{}
            case RnState.Tools{} RnState.Abort{}:
              Unit{}
            case RnState.Prepare{} RnState.Go{reply, fin, got}:
              pinv_prepare(cap, pp, aa, nn, reply, r, c, a, n)
            case RnState.Call{} RnState.Go{reply, fin, got}:
              pinv_call(cap, pp, aa, nn, reply, r, c, a, n, p, k, i)
            case RnState.Compact{over} RnState.Go{reply, fin, got}:
              pinv_compact(cap, pp, aa, nn, over, got, r, c, a, n, p)
            case RnState.Tools{} RnState.Go{reply, fin, got}:
              pinv_tools(cap, pp, aa, nn, fin, r, c, a, n, p)

def pinv_run(evs: List<&2, RnState.Ev>, +cfg: RnState.Cfg, +s: RnState.St, +k: Nat, i: PInv(cfg, s, k)) -> PInv(cfg, RnStep.run.go(evs, cfg, s), RnMeasure.defers.go(evs, cfg, s, k)):
  match evs:
    case Nil{}:
      i
    case +e <> rest:
      pinv_run(rest, cfg, RnStep.step(cfg, s, e), RnMeasure.defers.at(RnState.St.ph(s), e, k), pinv_step(cfg, s, e, k, i))

# a run the poll cap failed had polls + 1 deferred replies in a row
def polls_of(+cfg: RnState.Cfg, +s: RnState.St, +k: Nat, i: PInv(cfg, s, k)) -> Or({RnState.polled(s) == False{} : Bool}, {k == 1n+RnState.Cfg.polls(cfg) : Nat}):
  match cfg:
    case RnState.Cfg{cap, pp, aa, nn}:
      match s:
        case RnState.St{ph, r, c, a, n, p}:
          match ph:
            case RnState.Failed{why}:
              match why:
                case RnState.Polls{}:
                  Inr{i}
                case RnState.Model{}:
                  Inl{{==}}
                case RnState.Rounds{}:
                  Inl{{==}}
            case RnState.Prepare{}:
              Inl{{==}}
            case RnState.Call{}:
              Inl{{==}}
            case RnState.Compact{over}:
              Inl{{==}}
            case RnState.Tools{}:
              Inl{{==}}
            case RnState.Answered{}:
              Inl{{==}}
            case RnState.Aborted{}:
              Inl{{==}}

def polls_need_defers(+cfg: RnState.Cfg, +evs: List<&2, RnState.Ev>) -> Or({RnState.polled(RnStep.run(cfg, evs)) == False{} : Bool}, {RnMeasure.defers(cfg, evs) == 1n+RnState.Cfg.polls(cfg) : Nat}):
  polls_of(cfg, RnStep.run(cfg, evs), RnMeasure.defers(cfg, evs), pinv_run(evs, cfg, RnState.init(cfg), 0n, Unit{}))

def Run.run_polls_need_defers(cfg, evs):
  polls_need_defers(cfg, evs)
