# eukhe: the proof of LAW rec_stuck_gets_help

import Base
import ../../bend/run.bend as Rn
import ../../laws/run.bend as Run

# A stuck reply always gets help
# ------------------------------

def help_long(u: Bool, -n: Nat, -same: Nat, -last: Nat, -r: Rn.Rec) -> {Rn.Act.helps(Rn.Dec.act(Rn.rec.long(u, n, same, last, r))) == True{} : Bool}:
  match u:
    case True{}:
      {==}
    case False{}:
      {==}

def help_leak(u: Bool, -n: Nat, -same: Nat, -last: Nat, -r: Rn.Rec) -> {Rn.Act.helps(Rn.Dec.act(Rn.rec.leak(u, n, same, last, r))) == True{} : Bool}:
  match u:
    case True{}:
      {==}
    case False{}:
      {==}

def help_ran(fresh: Bool, u: Bool, -kept: Bool, -m: Nat, -h: Nat, -n: Nat, -same: Nat, -last: Nat, -r: Rn.Rec) -> {Rn.Act.helps(Rn.Dec.act(Rn.rec.ran(fresh, u, kept, m, h, n, same, last, r))) == True{} : Bool}:
  match fresh u:
    case True{} u:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      {==}

def help_out(+rc: Rn.RCfg, o: Rn.Out, +k: Rn.Rk, +row: Nat, +same: Nat, +last: Nat) -> {Bool.or(Bool.not(Rn.Out.stuck(o)), Rn.Act.helps(Rn.Dec.act(Rn.rec.go(rc, o, k, row, same, last)))) == True{} : Bool}:
  match o:
    case Rn.Long{}:
      help_long(Rn.below(Rn.Rk.longs(k, row), Rn.RCfg.long(rc)), Rn.Rk.longs(k, row), same, last, Rn.Rec{k, row, same, last})
    case Rn.Leak{rebuilt, +h, kept}:
      match rebuilt:
        case True{}:
          help_ran(Rn.below(Rn.again(same, last, h), Rn.RCfg.repeat(rc)), Rn.below(Rn.Rk.loops(k, row), Rn.RCfg.redirect(rc)), kept, Rn.again(same, last, h), h, Rn.Rk.loops(k, row), same, last, Rn.Rec{k, row, same, last})
        case False{}:
          help_leak(Rn.below(Rn.Rk.leaks(k, row), Rn.RCfg.leak(rc)), Rn.Rk.leaks(k, row), same, last, Rn.Rec{k, row, same, last})
    case Rn.Ran{+h, kept}:
      help_ran(Rn.below(Rn.again(same, last, h), Rn.RCfg.repeat(rc)), Rn.below(Rn.Rk.loops(k, row), Rn.RCfg.redirect(rc)), kept, Rn.again(same, last, h), h, Rn.Rk.loops(k, row), same, last, Rn.Rec{k, row, same, last})
    case Rn.Noted{}:
      {==}
    case Rn.Said{}:
      {==}
    case Rn.Answer{}:
      {==}
    case Rn.Other{}:
      {==}

def stuck_gets_help(+rc: Rn.RCfg, o: Rn.Out, r: Rn.Rec) -> {Bool.or(Bool.not(Rn.Out.stuck(o)), Rn.Act.helps(Rn.Dec.act(Rn.Rec.step(rc, o, r)))) == True{} : Bool}:
  match r:
    case Rn.Rec{k, row, same, last}:
      help_out(rc, o, k, row, same, last)

def Run.rec_stuck_gets_help(rc, o, r):
  stuck_gets_help(rc, o, r)
