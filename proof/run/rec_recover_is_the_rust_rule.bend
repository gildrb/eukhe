# eukhe: the proof of LAW rec_recover_is_the_rust_rule

import Base
import ../../bend/run.bend as Rn
import ../../LAWS.bend as Laws

def rk.below(+a: Nat, +b: Nat) -> {Nat.is_lt(a, b) == Rn.below(a, b) : Bool}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      rk.below(p, q)

def rk.long(+b: Bool, +n: Nat, +same: Nat, +last: Nat, +r: Rn.Rec) -> {Rn.Help.of(Rn.rec.long(b, n, same, last, r)) == Laws.rust.redo(b, n, Rn.Quits{}) : Rn.Help}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def rk.leak(+b: Bool, +n: Nat, +same: Nat, +last: Nat, +r: Rn.Rec) -> {Rn.Help.of(Rn.rec.leak(b, n, same, last, r)) == Laws.rust.redo(b, n, Rn.Stands{}) : Rn.Help}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def rk.ran(+fresh: Bool, +under: Bool, +m: Nat, +h: Nat, +n: Nat, +same: Nat, +last: Nat, +r: Rn.Rec) -> {Rn.Help.of(Rn.rec.ran(fresh, under, True{}, m, h, n, same, last, r)) == Laws.rust.calls(fresh, Laws.rust.redo(under, n, Rn.Quits{})) : Rn.Help}:
  match fresh under:
    case True{} True{}:
      {==}
    case True{} False{}:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      {==}

def rk.again(+before: Nat) -> {1n+before == Rn.again(before, 0n, 0n) : Nat}:
  match before:
    case 0n:
      {==}
    case 1n+j:
      {==}

def rk.long_row(+k: Rn.Rk, +row: Nat) -> {Rn.Rk.longs(k, row) == Laws.rust.long_row(k, row) : Nat}:
  match k:
    case Rn.Free{}:
      {==}
    case Rn.Longs{}:
      {==}
    case Rn.Leaks{}:
      {==}
    case Rn.Loops{}:
      {==}

def rk.leak_row(+k: Rn.Rk, +row: Nat) -> {Rn.Rk.leaks(k, row) == Laws.rust.leak_row(k, row) : Nat}:
  match k:
    case Rn.Free{}:
      {==}
    case Rn.Longs{}:
      {==}
    case Rn.Leaks{}:
      {==}
    case Rn.Loops{}:
      {==}

def rk.loop_row(+k: Rn.Rk, +row: Nat) -> {Rn.Rk.loops(k, row) == Laws.rust.loop_row(k, row) : Nat}:
  match k:
    case Rn.Free{}:
      {==}
    case Rn.Longs{}:
      {==}
    case Rn.Leaks{}:
      {==}
    case Rn.Loops{}:
      {==}

def rk.rec_recover_is_the_rust_rule(+rc: Rn.RCfg, +s: Rn.Stuck, +k: Rn.Rk, +row: Nat) -> {Rn.decide.recover(rc, s, k, row) == Laws.rust.recover(rc, s, k, row) : Rn.Help}:
  match rc:
    case Rn.RCfg{+long, +leak, +redirect, +repeat}:
      match s:
        case Rn.Truncated{}:
          +x = Rn.Rk.longs(k, row)
          +r = {Rn.Rec{k, row, 0n, 0n} : Rn.Rec}
          %rk.long_row(k, row) : {Rn.Help.of(Rn.rec.long(Rn.below(x, long), x, 0n, 0n, r)) == Laws.rust.redo(Nat.is_lt(_, long), _, Rn.Quits{}) : Rn.Help}
          %rk.below(x, long) : {Rn.Help.of(Rn.rec.long(_, x, 0n, 0n, r)) == Laws.rust.redo(Nat.is_lt(x, long), x, Rn.Quits{}) : Rn.Help}
          rk.long(Nat.is_lt(x, long), x, 0n, 0n, r)
        case Rn.Leaked{}:
          +x = Rn.Rk.leaks(k, row)
          +r = {Rn.Rec{k, row, 0n, 0n} : Rn.Rec}
          %rk.leak_row(k, row) : {Rn.Help.of(Rn.rec.leak(Rn.below(x, leak), x, 0n, 0n, r)) == Laws.rust.redo(Nat.is_lt(_, leak), _, Rn.Stands{}) : Rn.Help}
          %rk.below(x, leak) : {Rn.Help.of(Rn.rec.leak(_, x, 0n, 0n, r)) == Laws.rust.redo(Nat.is_lt(x, leak), x, Rn.Stands{}) : Rn.Help}
          rk.leak(Nat.is_lt(x, leak), x, 0n, 0n, r)
        case Rn.Repeats{+before}:
          +y = Rn.Rk.loops(k, row)
          +r = {Rn.Rec{k, row, before, 0n} : Rn.Rec}
          %rk.again(before) : {Rn.Help.of(Rn.rec.ran(Rn.below(_, repeat), Rn.below(y, redirect), True{}, _, 0n, y, before, 0n, r)) == Laws.rust.calls(Nat.is_lt(1n+before, repeat), Laws.rust.redo(Nat.is_lt(Laws.rust.loop_row(k, row), redirect), Laws.rust.loop_row(k, row), Rn.Quits{})) : Rn.Help}
          %rk.loop_row(k, row) : {Rn.Help.of(Rn.rec.ran(Rn.below(1n+before, repeat), Rn.below(y, redirect), True{}, 1n+before, 0n, y, before, 0n, r)) == Laws.rust.calls(Nat.is_lt(1n+before, repeat), Laws.rust.redo(Nat.is_lt(_, redirect), _, Rn.Quits{})) : Rn.Help}
          %rk.below(1n+before, repeat) : {Rn.Help.of(Rn.rec.ran(_, Rn.below(y, redirect), True{}, 1n+before, 0n, y, before, 0n, r)) == Laws.rust.calls(Nat.is_lt(1n+before, repeat), Laws.rust.redo(Nat.is_lt(y, redirect), y, Rn.Quits{})) : Rn.Help}
          %rk.below(y, redirect) : {Rn.Help.of(Rn.rec.ran(Nat.is_lt(1n+before, repeat), _, True{}, 1n+before, 0n, y, before, 0n, r)) == Laws.rust.calls(Nat.is_lt(1n+before, repeat), Laws.rust.redo(Nat.is_lt(y, redirect), y, Rn.Quits{})) : Rn.Help}
          rk.ran(Nat.is_lt(1n+before, repeat), Nat.is_lt(y, redirect), 1n+before, 0n, y, before, 0n, r)

def Laws.rec_recover_is_the_rust_rule(rc, s, k, row):
  rk.rec_recover_is_the_rust_rule(rc, s, k, row)
