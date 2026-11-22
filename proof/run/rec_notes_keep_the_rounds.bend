# eukhe: the proof of LAW rec_notes_keep_the_rounds
#
# PROOF: rec.leak and rec.empty keep the rounds on both arms, whatever
# the cap test gives; a repeat as the spec counts it is no fresh call
# (LRR.rr.rounds_off), and rec.ran keeps the rounds on both arms of a
# repeat.

import Base
import ../../bend/run/recovery.bend as RnRecovery
import ../../laws/run/recover.bend as RunRecover
import ./base/recover.bend as LRR

def kr.leak(b: Bool, +n: Nat, +k: RnRecovery.Rk, +row: Nat, +s: Nat, +l: Nat) -> {RunRecover.rounds_of(RnRecovery.Dec.r(RnRecovery.rec.leak(b, n, s, l, RnRecovery.Rec{k, row, s, l}))) == RnRecovery.Rec{RnRecovery.Free{}, 0n, s, l} : RnRecovery.Rec}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def kr.empty(b: Bool, +n: Nat, +k: RnRecovery.Rk, +row: Nat, +s: Nat, +l: Nat) -> {RunRecover.rounds_of(RnRecovery.Dec.r(RnRecovery.rec.empty(b, n, s, l, RnRecovery.Rec{k, row, s, l}))) == RnRecovery.Rec{RnRecovery.Free{}, 0n, s, l} : RnRecovery.Rec}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def kr.ran(b: Bool, +kept: Bool, +m: Nat, +h: Nat, +n: Nat, +k: RnRecovery.Rk, +row: Nat, +s: Nat, +l: Nat) -> {RunRecover.rounds_of(RnRecovery.Dec.r(RnRecovery.rec.ran(False{}, b, kept, m, h, n, s, l, RnRecovery.Rec{k, row, s, l}))) == RnRecovery.Rec{RnRecovery.Free{}, 0n, s, l} : RnRecovery.Rec}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def kr.repeat(+k: RnRecovery.Rk, +row: Nat, +re: Nat, +rp: Nat, +h: Nat, +kept: Bool, +s: Nat, +l: Nat, off: {RnRecovery.below(RnRecovery.again(s, l, h), rp) == False{} : Bool}) -> {RunRecover.rounds_of(RnRecovery.Dec.r(RnRecovery.rec.ran(RnRecovery.below(RnRecovery.again(s, l, h), rp), RnRecovery.below(RnRecovery.Rk.loops(k, row), re), kept, RnRecovery.again(s, l, h), h, RnRecovery.Rk.loops(k, row), s, l, RnRecovery.Rec{k, row, s, l}))) == RnRecovery.Rec{RnRecovery.Free{}, 0n, s, l} : RnRecovery.Rec}:
  %Equal.sym(Bool, RnRecovery.below(RnRecovery.again(s, l, h), rp), False{}, off) : {RunRecover.rounds_of(RnRecovery.Dec.r(RnRecovery.rec.ran(_, RnRecovery.below(RnRecovery.Rk.loops(k, row), re), kept, RnRecovery.again(s, l, h), h, RnRecovery.Rk.loops(k, row), s, l, RnRecovery.Rec{k, row, s, l}))) == RnRecovery.Rec{RnRecovery.Free{}, 0n, s, l} : RnRecovery.Rec}
  kr.ran(RnRecovery.below(RnRecovery.Rk.loops(k, row), re), kept, RnRecovery.again(s, l, h), h, RnRecovery.Rk.loops(k, row), k, row, s, l)

def RunRecover.rec_notes_keep_the_rounds(rc, h, kept, k, row, same, last, rep):
  match rc:
    case RnRecovery.RCfg{+long, +le, +re, +rp}:
      (kr.leak(RnRecovery.below(RnRecovery.Rk.leaks(k, row), le), RnRecovery.Rk.leaks(k, row), k, row, same, last), (kr.repeat(k, row, re, rp, h, kept, same, last, LRR.rr.rounds_off(same, last, h, rp, rep)), kr.empty(RnRecovery.below(RnRecovery.Rk.empties(k, row), 3n), RnRecovery.Rk.empties(k, row), k, row, same, last)))
