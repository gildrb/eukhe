# eukhe: the proof of LAW run_reply_saturates_the_attempt

import Base
import ../../bend/run/decision.bend as RnDecision
import ../../bend/run/state.bend as RnState
import ../../laws/run.bend as Run
import ./base.bend as LA

def rk.min_le(+a: Nat, +c: Nat, +r: Nat, +e: {Nat.is_le(r, c) == True{} : Bool}) -> {Nat.is_lt(a, r) == Nat.is_lt(Nat.min(a, c), r) : Bool}:
  match a:
    case 0n:
      {==}
    case 1n+u:
      match c:
        case 0n:
          match r:
            case 0n:
              {==}
            case 1n+q:
              LA.rk.absurd({Nat.is_lt(1n+u, 1n+q) == Nat.is_lt(Nat.min(1n+u, 0n), 1n+q) : Bool}, e)
        case 1n+d:
          match r:
            case 0n:
              {==}
            case 1n+q:
              rk.min_le(u, d, q, e)

def rk.min_sub(+k: Nat, +a: Nat, +c: Nat, +r: Nat, +e: {Nat.is_le(Nat.add(k, r), c) == True{} : Bool}) -> {Nat.is_lt(Nat.sub(a, k), r) == Nat.is_lt(Nat.sub(Nat.min(a, c), k), r) : Bool}:
  match k:
    case 0n:
      %LA.rk.sub0(a) : {Nat.is_lt(_, r) == Nat.is_lt(Nat.sub(Nat.min(a, c), 0n), r) : Bool}
      %LA.rk.sub0(Nat.min(a, c)) : {Nat.is_lt(a, r) == Nat.is_lt(_, r) : Bool}
      rk.min_le(a, c, r, e)
    case 1n+j:
      match a:
        case 0n:
          {==}
        case 1n+u:
          match c:
            case 0n:
              LA.rk.absurd({Nat.is_lt(Nat.sub(1n+u, 1n+j), r) == Nat.is_lt(Nat.sub(Nat.min(1n+u, 0n), 1n+j), r) : Bool}, e)
            case 1n+d:
              rk.min_sub(j, u, d, r, e)

def rk.ss(+a: Nat, +n: Nat) -> {Nat.sub(a, 1n+n) == Nat.sub(Nat.sub(a, 1n), n) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+u:
      %LA.rk.sub0(u) : {Nat.sub(u, n) == Nat.sub(_, n) : Nat}
      {==}

def rk.lt_le1(+c: Nat, +x: Nat, +e: {Nat.is_lt(x, c) == True{} : Bool}) -> {Nat.is_le(1n+x, c) == True{} : Bool}:
  match c:
    case 0n:
      match x:
        case 0n:
          LA.rk.absurd({Nat.is_le(1n, 0n) == True{} : Bool}, e)
        case 1n+y:
          LA.rk.absurd({Nat.is_le(2n+y, 0n) == True{} : Bool}, e)
    case 1n+d:
      Equal.trans(Bool, Nat.is_le(x, d), Nat.is_lt(x, 1n+d), True{}, LA.rk.lt_s(d, x), e)

def rk.sat_attempt(+l: RnDecision.Lim, +t: RnDecision.At, +reply: RnState.Reply, +cap: Nat, +e: {Nat.is_lt(Nat.add(RnDecision.At.notes(t), RnDecision.Lim.retries(l)), cap) == True{} : Bool}) -> {Run.rust.after_reply(l, Run.rust.sat_attempt(t, cap), reply) == Run.rust.after_reply(l, t, reply) : RnDecision.Then}:
  match l:
    case RnDecision.Lim{+rounds, +wait, +retries, +most}:
      match t:
        case RnDecision.At{+attempt, +notes, +waited, +compacted}:
          match reply:
            case RnState.Plain{}:
              {==}
            case RnState.Calls{}:
              {==}
            case RnState.Deferred{}:
              {==}
            case RnState.Error{retryable, noted}:
              match retryable noted:
                case retryable True{}:
                  {==}
                case True{} False{}:
                  +m = Nat.min(attempt, cap)
                  %rk.ss(m, notes) : {Run.rust.retry(Nat.is_lt(_, retries)) == Run.rust.retry(Nat.is_lt(Nat.sub(Nat.sub(attempt, 1n), notes), retries)) : RnDecision.Then}
                  %rk.ss(attempt, notes) : {Run.rust.retry(Nat.is_lt(Nat.sub(m, 1n+notes), retries)) == Run.rust.retry(Nat.is_lt(_, retries)) : RnDecision.Then}
                  %rk.min_sub(1n+notes, attempt, cap, retries, rk.lt_le1(cap, Nat.add(notes, retries), e)) : {Run.rust.retry(_) == Run.rust.retry(Nat.is_lt(Nat.sub(attempt, 1n+notes), retries)) : RnDecision.Then}
                  {==}
                case False{} False{}:
                  {==}
            case RnState.Overflow{cut}:
              {==}

def rk.run_reply_saturates_the_attempt(+l: RnDecision.Lim, +t: RnDecision.At, +reply: RnState.Reply, +cap: Nat, +e: {Nat.is_lt(Nat.add(RnDecision.At.notes(t), RnDecision.Lim.retries(l)), cap) == True{} : Bool}) -> {RnDecision.decide.reply(l, Run.rust.sat_attempt(t, cap), reply) == RnDecision.decide.reply(l, t, reply) : RnDecision.Then}:
  +t2 = Run.rust.sat_attempt(t, cap)
  Equal.trans(RnDecision.Then, RnDecision.decide.reply(l, t2, reply), Run.rust.after_reply(l, t2, reply), RnDecision.decide.reply(l, t, reply), LA.rk.run_reply_is_the_rust_rule(l, t2, reply), Equal.trans(RnDecision.Then, Run.rust.after_reply(l, t2, reply), Run.rust.after_reply(l, t, reply), RnDecision.decide.reply(l, t, reply), rk.sat_attempt(l, t, reply, cap, e), Equal.sym(RnDecision.Then, RnDecision.decide.reply(l, t, reply), Run.rust.after_reply(l, t, reply), LA.rk.run_reply_is_the_rust_rule(l, t, reply))))

def Run.run_reply_saturates_the_attempt(l, t, reply, cap, e):
  rk.run_reply_saturates_the_attempt(l, t, reply, cap, e)
