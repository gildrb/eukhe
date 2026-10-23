# eukhe: the proof of LAW run_polls_need_defers

import Base
import ../../bend/run.bend as Rn
import ../../laws/run.bend as Run
import ../base.bend as L

# The polls
# ---------
# After any inputs, with k = the deferred replies in a row: in a call,
# k + p = polls (the polls left and the deferred replies so far make the
# cap); a run the poll cap failed had k = polls + 1.

def PInv.why(+P: Nat, why: Rn.Why, +k: Nat) -> Type:
  match why:
    case Rn.Polls{}:
      {k == 1n+P : Nat}
    case Rn.Model{}:
      Unit
    case Rn.Rounds{}:
      Unit

def PInv.ph(+P: Nat, ph: Rn.Ph, +p: Nat, +k: Nat) -> Type:
  match ph:
    case Rn.Call{}:
      {Nat.add(k, p) == P : Nat}
    case Rn.Failed{why}:
      PInv.why(P, why, k)
    case Rn.Prepare{}:
      Unit
    case Rn.Compact{over}:
      Unit
    case Rn.Tools{}:
      Unit
    case Rn.Answered{}:
      Unit
    case Rn.Aborted{}:
      Unit

def PInv(+cfg: Rn.Cfg, +s: Rn.St, +k: Nat) -> Type:
  PInv.ph(Rn.Cfg.polls(cfg), Rn.St.ph(s), Rn.St.p(s), k)

def pinv_prepare_cut(+cap: Nat, +P: Nat, +A: Nat, +N: Nat, cut: Bool, +r: Nat, c: Nat, +a: Nat, +n: Nat) -> PInv(Rn.Cfg{cap, P, A, N}, Rn.prepare.cut(Rn.Cfg{cap, P, A, N}, cut, r, c, a, n), 0n):
  match cut c:
    case True{} 1n+d:
      Unit{}
    case True{} 0n:
      {==}
    case False{} c:
      {==}

def pinv_prepare(+cap: Nat, +P: Nat, +A: Nat, +N: Nat, reply: Rn.Reply, +r: Nat, +c: Nat, +a: Nat, +n: Nat) -> PInv(Rn.Cfg{cap, P, A, N}, Rn.prepare(Rn.Cfg{cap, P, A, N}, reply, r, c, a, n), 0n):
  match reply:
    case Rn.Overflow{cut}:
      pinv_prepare_cut(cap, P, A, N, cut, r, c, a, n)
    case Rn.Plain{}:
      {==}
    case Rn.Calls{}:
      {==}
    case Rn.Deferred{}:
      {==}
    case Rn.Error{retryable, noted}:
      {==}

def pinv_retry(+cap: Nat, +P: Nat, +A: Nat, +N: Nat, retryable: Bool, +r: Nat, +c: Nat, a: Nat, +n: Nat, +p: Nat) -> PInv(Rn.Cfg{cap, P, A, N}, Rn.retry(Rn.Cfg{cap, P, A, N}, retryable, r, c, a, n, p), 0n):
  match retryable a:
    case True{} 1n+b:
      Unit{}
    case True{} 0n:
      Unit{}
    case False{} a:
      Unit{}

def pinv_note(+cap: Nat, +P: Nat, +A: Nat, +N: Nat, +r: Nat, +c: Nat, +a: Nat, n: Nat, +p: Nat) -> PInv(Rn.Cfg{cap, P, A, N}, Rn.note(Rn.Cfg{cap, P, A, N}, r, c, a, n, p), 0n):
  match n:
    case 1n+m:
      Unit{}
    case 0n:
      Unit{}

def pinv_error(+cap: Nat, +P: Nat, +A: Nat, +N: Nat, retryable: Bool, noted: Bool, +r: Nat, +c: Nat, +a: Nat, +n: Nat, +p: Nat) -> PInv(Rn.Cfg{cap, P, A, N}, Rn.error(Rn.Cfg{cap, P, A, N}, retryable, noted, r, c, a, n, p), 0n):
  match noted:
    case True{}:
      pinv_note(cap, P, A, N, r, c, a, n, p)
    case False{}:
      pinv_retry(cap, P, A, N, retryable, r, c, a, n, p)

def pinv_overflow(+cap: Nat, +P: Nat, +A: Nat, +N: Nat, cut: Bool, +r: Nat, c: Nat, +a: Nat, +n: Nat, +p: Nat) -> PInv(Rn.Cfg{cap, P, A, N}, Rn.overflow(cut, r, c, a, n, p), 0n):
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
  %Equal.sym(Nat, Nat.add(k, 0n), k, L.add_zero(k)) : {1n+k == 1n+_ : Nat}
  {==}

def pinv_call(+cap: Nat, +P: Nat, +A: Nat, +N: Nat, reply: Rn.Reply, +r: Nat, +c: Nat, +a: Nat, +n: Nat, p: Nat, +k: Nat, i: {Nat.add(k, p) == P : Nat}) -> PInv(Rn.Cfg{cap, P, A, N}, Rn.call(Rn.Cfg{cap, P, A, N}, reply, r, c, a, n, p), Rn.defers.reply(reply, k)):
  match reply:
    case Rn.Plain{}:
      Unit{}
    case Rn.Calls{}:
      Unit{}
    case Rn.Deferred{}:
      match p:
        case 0n:
          polls_full(k, P, i)
        case 1n+q:
          %i : {1n+Nat.add(k, q) == _ : Nat}
          L.add_succ_r(k, q)
    case Rn.Error{retryable, noted}:
      pinv_error(cap, P, A, N, retryable, noted, r, c, a, n, p)
    case Rn.Overflow{cut}:
      pinv_overflow(cap, P, A, N, cut, r, c, a, n, p)

def pinv_compact(+cap: Nat, +P: Nat, +A: Nat, +N: Nat, over: Bool, got: Rn.Got, +r: Nat, +c: Nat, +a: Nat, +n: Nat, +p: Nat) -> PInv(Rn.Cfg{cap, P, A, N}, Rn.compact(Rn.Cfg{cap, P, A, N}, over, got, r, c, a, n, p), 0n):
  match over got:
    case over Rn.Built{}:
      Unit{}
    case True{} Rn.Kept{}:
      Unit{}
    case False{} Rn.Kept{}:
      Unit{}
    case over Rn.Broke{}:
      Unit{}

def pinv_round(+cap: Nat, +P: Nat, +A: Nat, +N: Nat, reset: Bool, r: Nat, +c: Nat, +a: Nat, +n: Nat, +p: Nat) -> PInv(Rn.Cfg{cap, P, A, N}, Rn.round(Rn.Cfg{cap, P, A, N}, reset, r, c, a, n, p), 0n):
  match reset r:
    case reset 0n:
      Unit{}
    case True{} 1n+s:
      Unit{}
    case False{} 1n+s:
      Unit{}

def pinv_tools(+cap: Nat, +P: Nat, +A: Nat, +N: Nat, fin: Rn.Fin, +r: Nat, +c: Nat, +a: Nat, +n: Nat, +p: Nat) -> PInv(Rn.Cfg{cap, P, A, N}, Rn.tools(Rn.Cfg{cap, P, A, N}, fin, r, c, a, n, p), 0n):
  match fin:
    case Rn.Stops{}:
      Unit{}
    case Rn.Goes{}:
      pinv_round(cap, P, A, N, False{}, r, c, a, n, p)
    case Rn.Resets{}:
      pinv_round(cap, P, A, N, True{}, r, c, a, n, p)

# one input keeps the poll invariant
def pinv_step(+cfg: Rn.Cfg, +s: Rn.St, +e: Rn.Ev, +k: Nat, i: PInv(cfg, s, k)) -> PInv(cfg, Rn.step(cfg, s, e), Rn.defers.at(Rn.St.ph(s), e, k)):
  match cfg:
    case Rn.Cfg{cap, P, A, N}:
      match s:
        case Rn.St{ph, r, c, a, n, p}:
          match ph e:
            case Rn.Answered{} e:
              i
            case Rn.Aborted{} e:
              i
            case Rn.Failed{why} e:
              i
            case Rn.Prepare{} Rn.Abort{}:
              Unit{}
            case Rn.Call{} Rn.Abort{}:
              Unit{}
            case Rn.Compact{over} Rn.Abort{}:
              Unit{}
            case Rn.Tools{} Rn.Abort{}:
              Unit{}
            case Rn.Prepare{} Rn.Go{reply, fin, got}:
              pinv_prepare(cap, P, A, N, reply, r, c, a, n)
            case Rn.Call{} Rn.Go{reply, fin, got}:
              pinv_call(cap, P, A, N, reply, r, c, a, n, p, k, i)
            case Rn.Compact{over} Rn.Go{reply, fin, got}:
              pinv_compact(cap, P, A, N, over, got, r, c, a, n, p)
            case Rn.Tools{} Rn.Go{reply, fin, got}:
              pinv_tools(cap, P, A, N, fin, r, c, a, n, p)

def pinv_run(evs: List<&2, Rn.Ev>, +cfg: Rn.Cfg, +s: Rn.St, +k: Nat, i: PInv(cfg, s, k)) -> PInv(cfg, Rn.run.go(evs, cfg, s), Rn.defers.go(evs, cfg, s, k)):
  match evs:
    case Nil{}:
      i
    case +e <> rest:
      pinv_run(rest, cfg, Rn.step(cfg, s, e), Rn.defers.at(Rn.St.ph(s), e, k), pinv_step(cfg, s, e, k, i))

# a run the poll cap failed had polls + 1 deferred replies in a row
def polls_of(+cfg: Rn.Cfg, +s: Rn.St, +k: Nat, i: PInv(cfg, s, k)) -> Or({Rn.polled(s) == False{} : Bool}, {k == 1n+Rn.Cfg.polls(cfg) : Nat}):
  match cfg:
    case Rn.Cfg{cap, P, A, N}:
      match s:
        case Rn.St{ph, r, c, a, n, p}:
          match ph:
            case Rn.Failed{why}:
              match why:
                case Rn.Polls{}:
                  Inr{i}
                case Rn.Model{}:
                  Inl{{==}}
                case Rn.Rounds{}:
                  Inl{{==}}
            case Rn.Prepare{}:
              Inl{{==}}
            case Rn.Call{}:
              Inl{{==}}
            case Rn.Compact{over}:
              Inl{{==}}
            case Rn.Tools{}:
              Inl{{==}}
            case Rn.Answered{}:
              Inl{{==}}
            case Rn.Aborted{}:
              Inl{{==}}

def polls_need_defers(+cfg: Rn.Cfg, +evs: List<&2, Rn.Ev>) -> Or({Rn.polled(Rn.run(cfg, evs)) == False{} : Bool}, {Rn.defers(cfg, evs) == 1n+Rn.Cfg.polls(cfg) : Nat}):
  polls_of(cfg, Rn.run(cfg, evs), Rn.defers(cfg, evs), pinv_run(evs, cfg, Rn.init(cfg), 0n, Unit{}))

def Run.run_polls_need_defers(cfg, evs):
  polls_need_defers(cfg, evs)
