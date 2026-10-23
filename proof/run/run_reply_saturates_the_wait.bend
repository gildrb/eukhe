# eukhe: the proof of LAW run_reply_saturates_the_wait

import Base
import ../../bend/run.bend as Rn
import ../../laws/run.bend as Run
import ./base.bend as LA

def rk.min_lt(+w: Nat, +c: Nat, +x: Nat, +e: {Nat.is_lt(x, c) == True{} : Bool}) -> {Nat.is_lt(x, w) == Nat.is_lt(x, Nat.min(w, c)) : Bool}:
  match w:
    case 0n:
      {==}
    case 1n+v:
      match c:
        case 0n:
          match x:
            case 0n:
              LA.rk.absurd({Nat.is_lt(0n, 1n+v) == Nat.is_lt(0n, Nat.min(1n+v, 0n)) : Bool}, e)
            case 1n+y:
              LA.rk.absurd({Nat.is_lt(1n+y, 1n+v) == Nat.is_lt(1n+y, Nat.min(1n+v, 0n)) : Bool}, e)
        case 1n+d:
          match x:
            case 0n:
              {==}
            case 1n+y:
              rk.min_lt(v, d, y, e)

def rk.sat_wait(+l: Rn.Lim, +t: Rn.At, +reply: Rn.Reply, +cap: Nat, +e: {Nat.is_lt(Rn.At.waited(t), cap) == True{} : Bool}) -> {Run.rust.after_reply(Run.rust.sat_wait(l, cap), t, reply) == Run.rust.after_reply(l, t, reply) : Rn.Then}:
  match l:
    case Rn.Lim{+rounds, +wait, +retries, +most}:
      match t:
        case Rn.At{+attempt, +notes, +waited, +compacted}:
          match reply:
            case Rn.Plain{}:
              {==}
            case Rn.Calls{}:
              {==}
            case Rn.Deferred{}:
              %rk.min_lt(wait, cap, waited, e) : {Run.rust.wait(_) == Run.rust.wait(Nat.is_lt(waited, wait)) : Rn.Then}
              {==}
            case Rn.Error{retryable, noted}:
              match retryable noted:
                case retryable True{}:
                  {==}
                case True{} False{}:
                  {==}
                case False{} False{}:
                  {==}
            case Rn.Overflow{cut}:
              {==}

def rk.run_reply_saturates_the_wait(+l: Rn.Lim, +t: Rn.At, +reply: Rn.Reply, +cap: Nat, +e: {Nat.is_lt(Rn.At.waited(t), cap) == True{} : Bool}) -> {Rn.decide.reply(Run.rust.sat_wait(l, cap), t, reply) == Rn.decide.reply(l, t, reply) : Rn.Then}:
  +l2 = Run.rust.sat_wait(l, cap)
  Equal.trans(Rn.Then, Rn.decide.reply(l2, t, reply), Run.rust.after_reply(l2, t, reply), Rn.decide.reply(l, t, reply), LA.rk.run_reply_is_the_rust_rule(l2, t, reply), Equal.trans(Rn.Then, Run.rust.after_reply(l2, t, reply), Run.rust.after_reply(l, t, reply), Rn.decide.reply(l, t, reply), rk.sat_wait(l, t, reply, cap, e), Equal.sym(Rn.Then, Rn.decide.reply(l, t, reply), Run.rust.after_reply(l, t, reply), LA.rk.run_reply_is_the_rust_rule(l, t, reply))))

def Run.run_reply_saturates_the_wait(l, t, reply, cap, e):
  rk.run_reply_saturates_the_wait(l, t, reply, cap, e)
