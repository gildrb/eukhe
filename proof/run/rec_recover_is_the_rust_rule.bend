# eukhe: the proof of LAW rec_recover_is_the_rust_rule

import Base
import ../../bend/run/decision.bend as RnDecision
import ../../bend/run/recovery.bend as RnRecovery
import ../../laws/run.bend as Run

def rk.below(+a: Nat, +b: Nat) -> {Nat.is_lt(a, b) == RnRecovery.below(a, b) : Bool}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      rk.below(p, q)

def rk.long(+b: Bool, +n: Nat, +same: Nat, +last: Nat, +r: RnRecovery.Rec) -> {RnDecision.Help.of(RnRecovery.rec.long(b, n, same, last, r)) == Run.rust.redo(b, n, RnDecision.Quits{}) : RnDecision.Help}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def rk.leak(+b: Bool, +n: Nat, +same: Nat, +last: Nat, +r: RnRecovery.Rec) -> {RnDecision.Help.of(RnRecovery.rec.leak(b, n, same, last, r)) == Run.rust.redo(b, n, RnDecision.Stands{}) : RnDecision.Help}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def rk.ran(+fresh: Bool, +under: Bool, +m: Nat, +h: Nat, +n: Nat, +same: Nat, +last: Nat, +r: RnRecovery.Rec) -> {RnDecision.Help.of(RnRecovery.rec.ran(fresh, under, True{}, m, h, n, same, last, r)) == Run.rust.calls(fresh, Run.rust.redo(under, n, RnDecision.Quits{})) : RnDecision.Help}:
  match fresh under:
    case True{} True{}:
      {==}
    case True{} False{}:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      {==}

def rk.again(+before: Nat) -> {1n+before == RnRecovery.again(before, 0n, 0n) : Nat}:
  match before:
    case 0n:
      {==}
    case 1n+j:
      {==}

def rk.long_row(+k: RnRecovery.Rk, +row: Nat) -> {RnRecovery.Rk.longs(k, row) == Run.rust.long_row(k, row) : Nat}:
  match k:
    case RnRecovery.Free{}:
      {==}
    case RnRecovery.Longs{}:
      {==}
    case RnRecovery.Leaks{}:
      {==}
    case RnRecovery.Loops{}:
      {==}

def rk.leak_row(+k: RnRecovery.Rk, +row: Nat) -> {RnRecovery.Rk.leaks(k, row) == Run.rust.leak_row(k, row) : Nat}:
  match k:
    case RnRecovery.Free{}:
      {==}
    case RnRecovery.Longs{}:
      {==}
    case RnRecovery.Leaks{}:
      {==}
    case RnRecovery.Loops{}:
      {==}

def rk.loop_row(+k: RnRecovery.Rk, +row: Nat) -> {RnRecovery.Rk.loops(k, row) == Run.rust.loop_row(k, row) : Nat}:
  match k:
    case RnRecovery.Free{}:
      {==}
    case RnRecovery.Longs{}:
      {==}
    case RnRecovery.Leaks{}:
      {==}
    case RnRecovery.Loops{}:
      {==}

def rk.rec_recover_is_the_rust_rule(+rc: RnRecovery.RCfg, +s: RnDecision.Stuck, +k: RnRecovery.Rk, +row: Nat) -> {RnDecision.decide.recover(rc, s, k, row) == Run.rust.recover(rc, s, k, row) : RnDecision.Help}:
  match rc:
    case RnRecovery.RCfg{+long, +leak, +redirect, +repeat}:
      match s:
        case RnDecision.Truncated{}:
          +x = RnRecovery.Rk.longs(k, row)
          +r = {RnRecovery.Rec{k, row, 0n, 0n} : RnRecovery.Rec}
          %rk.long_row(k, row) : {RnDecision.Help.of(RnRecovery.rec.long(RnRecovery.below(x, long), x, 0n, 0n, r)) == Run.rust.redo(Nat.is_lt(_, long), _, RnDecision.Quits{}) : RnDecision.Help}
          %rk.below(x, long) : {RnDecision.Help.of(RnRecovery.rec.long(_, x, 0n, 0n, r)) == Run.rust.redo(Nat.is_lt(x, long), x, RnDecision.Quits{}) : RnDecision.Help}
          rk.long(Nat.is_lt(x, long), x, 0n, 0n, r)
        case RnDecision.Leaked{}:
          +x = RnRecovery.Rk.leaks(k, row)
          +r = {RnRecovery.Rec{k, row, 0n, 0n} : RnRecovery.Rec}
          %rk.leak_row(k, row) : {RnDecision.Help.of(RnRecovery.rec.leak(RnRecovery.below(x, leak), x, 0n, 0n, r)) == Run.rust.redo(Nat.is_lt(_, leak), _, RnDecision.Stands{}) : RnDecision.Help}
          %rk.below(x, leak) : {RnDecision.Help.of(RnRecovery.rec.leak(_, x, 0n, 0n, r)) == Run.rust.redo(Nat.is_lt(x, leak), x, RnDecision.Stands{}) : RnDecision.Help}
          rk.leak(Nat.is_lt(x, leak), x, 0n, 0n, r)
        case RnDecision.Repeats{+before}:
          +y = RnRecovery.Rk.loops(k, row)
          +r = {RnRecovery.Rec{k, row, before, 0n} : RnRecovery.Rec}
          %rk.again(before) : {RnDecision.Help.of(RnRecovery.rec.ran(RnRecovery.below(_, repeat), RnRecovery.below(y, redirect), True{}, _, 0n, y, before, 0n, r)) == Run.rust.calls(Nat.is_lt(1n+before, repeat), Run.rust.redo(Nat.is_lt(Run.rust.loop_row(k, row), redirect), Run.rust.loop_row(k, row), RnDecision.Quits{})) : RnDecision.Help}
          %rk.loop_row(k, row) : {RnDecision.Help.of(RnRecovery.rec.ran(RnRecovery.below(1n+before, repeat), RnRecovery.below(y, redirect), True{}, 1n+before, 0n, y, before, 0n, r)) == Run.rust.calls(Nat.is_lt(1n+before, repeat), Run.rust.redo(Nat.is_lt(_, redirect), _, RnDecision.Quits{})) : RnDecision.Help}
          %rk.below(1n+before, repeat) : {RnDecision.Help.of(RnRecovery.rec.ran(_, RnRecovery.below(y, redirect), True{}, 1n+before, 0n, y, before, 0n, r)) == Run.rust.calls(Nat.is_lt(1n+before, repeat), Run.rust.redo(Nat.is_lt(y, redirect), y, RnDecision.Quits{})) : RnDecision.Help}
          %rk.below(y, redirect) : {RnDecision.Help.of(RnRecovery.rec.ran(Nat.is_lt(1n+before, repeat), _, True{}, 1n+before, 0n, y, before, 0n, r)) == Run.rust.calls(Nat.is_lt(1n+before, repeat), Run.rust.redo(Nat.is_lt(y, redirect), y, RnDecision.Quits{})) : RnDecision.Help}
          rk.ran(Nat.is_lt(1n+before, repeat), Nat.is_lt(y, redirect), 1n+before, 0n, y, before, 0n, r)

def Run.rec_recover_is_the_rust_rule(rc, s, k, row):
  rk.rec_recover_is_the_rust_rule(rc, s, k, row)
