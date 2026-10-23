# eukhe: the proof of LAW restart_decide_verdict

import Base
import ../../bend/supervise.bend as Su
import ../../laws/supervise.bend as Supervise
import ./base.bend as LA

def ps.rs_pow2(e: Nat) -> {Nat.pow(2n, e) == Supervise.restart_pow2(e) : Nat}:
  match e:
    case 0n:
      {==}
    case 1n+p:
      %ps.rs_pow2(p) : {Nat.mul(2n, Nat.pow(2n, p)) == Nat.mul(2n, _) : Nat}
      {==}

def ps.rs_verdict(b: Bool, +c: Su.Cfg, +n: Nat) -> {Su.verdict.put(b, c, n) == Supervise.restart_verdict_put(b, c, n) : Su.Verdict}:
  match b:
    case True{}:
      {==}
    case False{}:
      match c:
        case Su.Cfg{k, w, +b0, +m}:
          %ps.rs_pow2(Nat.min(Nat.sub(n, 1n), 7n)) : {Su.Relaunch{n, Nat.min(Nat.mul(Nat.pow(2n, Nat.min(Nat.sub(n, 1n), 7n)), b0), m)} == Su.Relaunch{n, Nat.min(Nat.mul(_, b0), m)} : Su.Verdict}
          {==}

def Supervise.restart_decide_verdict(c, s, g):
  match s:
    case Su.St{a, n}:
      %LA.ps.rs_window(Su.Cfg.w(c), g, a) : {Su.verdict(c, 1n+List.length(&2, Nat, Su.keep(Su.Cfg.w(c), Su.older(g, a)))) == Supervise.restart_verdict_put(Nat.is_lt(Su.Cfg.k(c), 1n+List.length(&2, Nat, _)), c, 1n+List.length(&2, Nat, _)) : Su.Verdict}
      ps.rs_verdict(Nat.is_lt(Su.Cfg.k(c), 1n+List.length(&2, Nat, Su.keep(Su.Cfg.w(c), Su.older(g, a)))), c, 1n+List.length(&2, Nat, Su.keep(Su.Cfg.w(c), Su.older(g, a))))
