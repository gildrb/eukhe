# eukhe: the proof of LAW rec_recover_is_the_rust_rule

import Base
import ../../bend/stop.bend as Stop
import ../../bend/run/decision.bend as RnDecision
import ../../bend/run/recovery.bend as RnRecovery
import ../../laws/run.bend as Run
import ../../laws/stop.bend as LawsStop
import ../../spec/harness/stop.bend as StSpec

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

def rk.leak(+b: Bool, +n: Nat, +same: Nat, +last: Nat, +r: RnRecovery.Rec) -> {RnDecision.Help.of(RnRecovery.rec.leak(b, n, same, last, r)) == Run.rust.redo(b, n, RnDecision.Quits{}) : RnDecision.Help}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def rk.empty(+b: Bool, +n: Nat, +same: Nat, +last: Nat, +r: RnRecovery.Rec) -> {RnDecision.Help.of(RnRecovery.rec.empty(b, n, same, last, r)) == LawsStop.rust_empty.at(b, n) : RnDecision.Help}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def rk.promise(+b: Bool, +n: Nat, +same: Nat, +last: Nat, +r: RnRecovery.Rec) -> {RnDecision.Help.of(RnRecovery.rec.promise(b, n, same, last, r)) == LawsStop.rust_promise.at(b, n) : RnDecision.Help}:
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
    case RnRecovery.Empties{}:
      {==}
    case RnRecovery.Promises{}:
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
    case RnRecovery.Empties{}:
      {==}
    case RnRecovery.Promises{}:
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
    case RnRecovery.Empties{}:
      {==}
    case RnRecovery.Promises{}:
      {==}

def rk.empty_row(+k: RnRecovery.Rk, +row: Nat) -> {RnRecovery.Rk.empties(k, row) == LawsStop.rust_empty_row(k, row) : Nat}:
  match k:
    case RnRecovery.Free{}:
      {==}
    case RnRecovery.Longs{}:
      {==}
    case RnRecovery.Leaks{}:
      {==}
    case RnRecovery.Loops{}:
      {==}
    case RnRecovery.Empties{}:
      {==}
    case RnRecovery.Promises{}:
      {==}

def rk.promise_row(+k: RnRecovery.Rk, +row: Nat) -> {RnRecovery.Rk.promises(k, row) == LawsStop.rust_promise_row(k, row) : Nat}:
  match k:
    case RnRecovery.Free{}:
      {==}
    case RnRecovery.Longs{}:
      {==}
    case RnRecovery.Leaks{}:
      {==}
    case RnRecovery.Loops{}:
      {==}
    case RnRecovery.Empties{}:
      {==}
    case RnRecovery.Promises{}:
      {==}

def rk.long_row_stop(+k: RnRecovery.Rk, +row: Nat) -> {RnRecovery.Rk.longs(k, row) == LawsStop.rust_long_row(k, row) : Nat}:
  match k:
    case RnRecovery.Free{}:
      {==}
    case RnRecovery.Longs{}:
      {==}
    case RnRecovery.Leaks{}:
      {==}
    case RnRecovery.Loops{}:
      {==}
    case RnRecovery.Empties{}:
      {==}
    case RnRecovery.Promises{}:
      {==}

# the spec's window test is the model's
def rk.bound(+w: Nat, +c: Nat, +p: Nat, +o: Nat) -> {StSpec.ran_out(w, c, p, o) == RnRecovery.bound(w, c, p, o) : Bool}:
  match w:
    case 0n:
      {==}
    case 1n+v:
      {==}

def rk.at_cap(le: Bool, +x: Nat, +r: RnRecovery.Rec) -> {RnDecision.Help.of(RnRecovery.rec.think.note(False{}, le, x, 0n, 0n, r)) == StSpec.at_cap(le, x) : RnDecision.Help}:
  match le:
    case True{}:
      {==}
    case False{}:
      {==}

def rk.think_note(lt: Bool, +lower: Bool, +x: Nat, +long: Nat, +r: RnRecovery.Rec) -> {RnDecision.Help.of(RnRecovery.rec.think.note(lt, Bool.and(lower, Nat.is_eq(x, long)), x, 0n, 0n, r)) == StSpec.under(lt, lower, x, long) : RnDecision.Help}:
  match lt:
    case True{}:
      {==}
    case False{}:
      rk.at_cap(Bool.and(lower, Nat.is_eq(x, long)), x, r)

def rk.think(s: Bool, +lower: Bool, +x: Nat, +long: Nat, +r: RnRecovery.Rec) -> {RnDecision.Help.of(RnRecovery.rec.think(s, Nat.is_lt(x, long), Bool.and(lower, Nat.is_eq(x, long)), x, 0n, 0n, r)) == StSpec.ladder(s, lower, x, long) : RnDecision.Help}:
  match s:
    case True{}:
      {==}
    case False{}:
      rk.think_note(Nat.is_lt(x, long), lower, x, long, r)

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
          %rk.leak_row(k, row) : {RnDecision.Help.of(RnRecovery.rec.leak(RnRecovery.below(x, leak), x, 0n, 0n, r)) == Run.rust.redo(Nat.is_lt(_, leak), _, RnDecision.Quits{}) : RnDecision.Help}
          %rk.below(x, leak) : {RnDecision.Help.of(RnRecovery.rec.leak(_, x, 0n, 0n, r)) == Run.rust.redo(Nat.is_lt(x, leak), x, RnDecision.Quits{}) : RnDecision.Help}
          rk.leak(Nat.is_lt(x, leak), x, 0n, 0n, r)
        case RnDecision.Repeats{+before}:
          +y = RnRecovery.Rk.loops(k, row)
          +r = {RnRecovery.Rec{k, row, before, 0n} : RnRecovery.Rec}
          %rk.again(before) : {RnDecision.Help.of(RnRecovery.rec.ran(RnRecovery.below(_, repeat), RnRecovery.below(y, redirect), True{}, _, 0n, y, before, 0n, r)) == Run.rust.calls(Nat.is_lt(1n+before, repeat), Run.rust.redo(Nat.is_lt(Run.rust.loop_row(k, row), redirect), Run.rust.loop_row(k, row), RnDecision.Quits{})) : RnDecision.Help}
          %rk.loop_row(k, row) : {RnDecision.Help.of(RnRecovery.rec.ran(RnRecovery.below(1n+before, repeat), RnRecovery.below(y, redirect), True{}, 1n+before, 0n, y, before, 0n, r)) == Run.rust.calls(Nat.is_lt(1n+before, repeat), Run.rust.redo(Nat.is_lt(_, redirect), _, RnDecision.Quits{})) : RnDecision.Help}
          %rk.below(1n+before, repeat) : {RnDecision.Help.of(RnRecovery.rec.ran(_, RnRecovery.below(y, redirect), True{}, 1n+before, 0n, y, before, 0n, r)) == Run.rust.calls(Nat.is_lt(1n+before, repeat), Run.rust.redo(Nat.is_lt(y, redirect), y, RnDecision.Quits{})) : RnDecision.Help}
          %rk.below(y, redirect) : {RnDecision.Help.of(RnRecovery.rec.ran(Nat.is_lt(1n+before, repeat), _, True{}, 1n+before, 0n, y, before, 0n, r)) == Run.rust.calls(Nat.is_lt(1n+before, repeat), Run.rust.redo(Nat.is_lt(y, redirect), y, RnDecision.Quits{})) : RnDecision.Help}
          rk.ran(Nat.is_lt(1n+before, repeat), Nat.is_lt(y, redirect), 1n+before, 0n, y, before, 0n, r)
        case RnDecision.Emptied{}:
          +x = RnRecovery.Rk.empties(k, row)
          +r = {RnRecovery.Rec{k, row, 0n, 0n} : RnRecovery.Rec}
          %rk.empty_row(k, row) : {RnDecision.Help.of(RnRecovery.rec.empty(RnRecovery.below(x, Stop.empty_cap()), x, 0n, 0n, r)) == LawsStop.rust_empty.at(Nat.is_lt(_, Stop.empty_cap()), _) : RnDecision.Help}
          %rk.below(x, Stop.empty_cap()) : {RnDecision.Help.of(RnRecovery.rec.empty(_, x, 0n, 0n, r)) == LawsStop.rust_empty.at(Nat.is_lt(x, Stop.empty_cap()), x) : RnDecision.Help}
          rk.empty(Nat.is_lt(x, Stop.empty_cap()), x, 0n, 0n, r)
        case RnDecision.Promised{}:
          +x = RnRecovery.Rk.promises(k, row)
          +r = {RnRecovery.Rec{k, row, 0n, 0n} : RnRecovery.Rec}
          %rk.promise_row(k, row) : {RnDecision.Help.of(RnRecovery.rec.promise(RnRecovery.below(x, Stop.promise_cap()), x, 0n, 0n, r)) == LawsStop.rust_promise.at(Nat.is_lt(_, Stop.promise_cap()), _) : RnDecision.Help}
          %rk.below(x, Stop.promise_cap()) : {RnDecision.Help.of(RnRecovery.rec.promise(_, x, 0n, 0n, r)) == LawsStop.rust_promise.at(Nat.is_lt(x, Stop.promise_cap()), x) : RnDecision.Help}
          rk.promise(Nat.is_lt(x, Stop.promise_cap()), x, 0n, 0n, r)
        case RnDecision.Thought{+w, +c, +p, +o, +cu, +lo}:
          +x = RnRecovery.Rk.longs(k, row)
          +r = {RnRecovery.Rec{k, row, 0n, 0n} : RnRecovery.Rec}
          %rk.long_row_stop(k, row) : {RnDecision.Help.of(RnRecovery.rec.think(Bool.and(cu, RnRecovery.bound(w, c, p, o)), RnRecovery.below(x, long), Bool.and(lo, Nat.is_eq(x, long)), x, 0n, 0n, r)) == StSpec.ladder(Bool.and(cu, StSpec.ran_out(w, c, p, o)), lo, _, long) : RnDecision.Help}
          %rk.bound(w, c, p, o) : {RnDecision.Help.of(RnRecovery.rec.think(Bool.and(cu, _), RnRecovery.below(x, long), Bool.and(lo, Nat.is_eq(x, long)), x, 0n, 0n, r)) == StSpec.ladder(Bool.and(cu, StSpec.ran_out(w, c, p, o)), lo, x, long) : RnDecision.Help}
          %rk.below(x, long) : {RnDecision.Help.of(RnRecovery.rec.think(Bool.and(cu, StSpec.ran_out(w, c, p, o)), _, Bool.and(lo, Nat.is_eq(x, long)), x, 0n, 0n, r)) == StSpec.ladder(Bool.and(cu, StSpec.ran_out(w, c, p, o)), lo, x, long) : RnDecision.Help}
          rk.think(Bool.and(cu, StSpec.ran_out(w, c, p, o)), lo, x, long, r)

def Run.rec_recover_is_the_rust_rule(rc, s, k, row):
  rk.rec_recover_is_the_rust_rule(rc, s, k, row)
