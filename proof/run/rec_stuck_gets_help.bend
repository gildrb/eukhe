# eukhe: the proof of LAW rec_stuck_gets_help

import Base
import ../../bend/stop.bend as Stop
import ../../bend/run/recovery.bend as RnRecovery
import ../../laws/run/recover.bend as Run

# A stuck reply always gets help
# ------------------------------

def help_leak(u: Bool, -n: Nat, -same: Nat, -last: Nat, -r: RnRecovery.Rec) -> {RnRecovery.Act.helps(RnRecovery.Dec.act(RnRecovery.rec.leak(u, n, same, last, r))) == True{} : Bool}:
  match u:
    case True{}:
      {==}
    case False{}:
      {==}

def help_empty(u: Bool, -n: Nat, -same: Nat, -last: Nat, -r: RnRecovery.Rec) -> {RnRecovery.Act.helps(RnRecovery.Dec.act(RnRecovery.rec.empty(u, n, same, last, r))) == True{} : Bool}:
  match u:
    case True{}:
      {==}
    case False{}:
      {==}

def help_ran(fresh: Bool, u: Bool, -kept: Bool, -m: Nat, -h: Nat, -n: Nat, -same: Nat, -last: Nat, -r: RnRecovery.Rec) -> {RnRecovery.Act.helps(RnRecovery.Dec.act(RnRecovery.rec.ran(fresh, u, kept, m, h, n, same, last, r))) == True{} : Bool}:
  match fresh u:
    case True{} u:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      {==}

def help_think(s: Bool, u: Bool, l: Bool, -n: Nat, -same: Nat, -last: Nat, -r: RnRecovery.Rec) -> {RnRecovery.Act.helps(RnRecovery.Dec.act(RnRecovery.rec.think(s, u, l, n, same, last, r))) == True{} : Bool}:
  match s:
    case True{}:
      {==}
    case False{}:
      match u:
        case True{}:
          {==}
        case False{}:
          match l:
            case True{}:
              {==}
            case False{}:
              {==}

def help_out(+rc: RnRecovery.RCfg, o: RnRecovery.Out, +k: RnRecovery.Rk, +row: Nat, +same: Nat, +last: Nat) -> {Bool.or(Bool.not(RnRecovery.Out.stuck(o)), RnRecovery.Act.helps(RnRecovery.Dec.act(RnRecovery.rec.go(rc, o, k, row, same, last)))) == True{} : Bool}:
  match o:
    case RnRecovery.Leak{rebuilt, +h, kept}:
      match rebuilt:
        case True{}:
          help_ran(RnRecovery.below(RnRecovery.again(same, last, h), RnRecovery.RCfg.repeat(rc)), RnRecovery.below(RnRecovery.Rk.loops(k, row), RnRecovery.RCfg.redirect(rc)), kept, RnRecovery.again(same, last, h), h, RnRecovery.Rk.loops(k, row), same, last, RnRecovery.Rec{k, row, same, last})
        case False{}:
          help_leak(RnRecovery.below(RnRecovery.Rk.leaks(k, row), RnRecovery.RCfg.leak(rc)), RnRecovery.Rk.leaks(k, row), same, last, RnRecovery.Rec{k, row, same, last})
    case RnRecovery.Ran{+h, kept}:
      help_ran(RnRecovery.below(RnRecovery.again(same, last, h), RnRecovery.RCfg.repeat(rc)), RnRecovery.below(RnRecovery.Rk.loops(k, row), RnRecovery.RCfg.redirect(rc)), kept, RnRecovery.again(same, last, h), h, RnRecovery.Rk.loops(k, row), same, last, RnRecovery.Rec{k, row, same, last})
    case RnRecovery.Noted{}:
      {==}
    case RnRecovery.Said{}:
      {==}
    case RnRecovery.Answer{}:
      {==}
    case RnRecovery.Other{}:
      {==}
    case RnRecovery.Empty{}:
      help_empty(RnRecovery.below(RnRecovery.Rk.empties(k, row), Stop.empty_cap()), RnRecovery.Rk.empties(k, row), same, last, RnRecovery.Rec{k, row, same, last})
    case RnRecovery.Think{shrink, lower}:
      help_think(shrink, RnRecovery.below(RnRecovery.Rk.longs(k, row), RnRecovery.RCfg.long(rc)), Bool.and(lower, Nat.is_eq(RnRecovery.Rk.longs(k, row), RnRecovery.RCfg.long(rc))), RnRecovery.Rk.longs(k, row), same, last, RnRecovery.Rec{k, row, same, last})

def stuck_gets_help(+rc: RnRecovery.RCfg, o: RnRecovery.Out, r: RnRecovery.Rec) -> {Bool.or(Bool.not(RnRecovery.Out.stuck(o)), RnRecovery.Act.helps(RnRecovery.Dec.act(RnRecovery.Rec.step(rc, o, r)))) == True{} : Bool}:
  match r:
    case RnRecovery.Rec{k, row, same, last}:
      help_out(rc, o, k, row, same, last)

def Run.rec_stuck_gets_help(rc, o, r):
  stuck_gets_help(rc, o, r)
