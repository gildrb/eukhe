# eukhe: the proof of LAW rec_repeat_never_runs
#
# PROOF: the spec's rounds are the model's (LRR.rr.rounds_off), so calls
# that make `repeat` or more rounds are no fresh calls; rebuilt leaked
# calls step as calls. By cases on the note: the redirect notes in a row
# the model reads (Rk.loops) are the spec's (redirects), and `below` is
# Nat.is_lt (LR.str.below); then by cases on whether a redirect note is
# left: the next redirect note, else the failed run with the record kept.

import Base
import ../../bend/run/recovery.bend as RnRecovery
import ../../laws/run/recover.bend as RunRecover
import ../stop/base/recover.bend as LR
import ./base/recover.bend as LRR

# no fresh calls: under the redirect cap the next note, else the run fails
def rq.tail(b: Bool, +kept: Bool, +m: Nat, +h: Nat, +n: Nat, +k: RnRecovery.Rk, +row: Nat, +s: Nat, +l: Nat) -> {RnRecovery.rec.ran(False{}, b, kept, m, h, n, s, l, RnRecovery.Rec{k, row, s, l}) == RunRecover.repeat_help.go(b, n, k, row, s, l) : RnRecovery.Dec}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# the model's redirect notes in a row are the spec's, after any note
def rq.k(k: RnRecovery.Rk, +row: Nat, +rd: Nat, +h: Nat, +kept: Bool, +s: Nat, +l: Nat) -> {RnRecovery.rec.ran(False{}, RnRecovery.below(RnRecovery.Rk.loops(k, row), rd), kept, RnRecovery.again(s, l, h), h, RnRecovery.Rk.loops(k, row), s, l, RnRecovery.Rec{k, row, s, l}) == RunRecover.repeat_help(rd, k, row, s, l) : RnRecovery.Dec}:
  match k:
    case RnRecovery.Free{}:
      %LR.str.below(0n, rd) : {RnRecovery.rec.ran(False{}, _, kept, RnRecovery.again(s, l, h), h, 0n, s, l, RnRecovery.Rec{RnRecovery.Free{}, row, s, l}) == RunRecover.repeat_help.go(Nat.is_lt(0n, rd), 0n, RnRecovery.Free{}, row, s, l) : RnRecovery.Dec}
      rq.tail(Nat.is_lt(0n, rd), kept, RnRecovery.again(s, l, h), h, 0n, RnRecovery.Free{}, row, s, l)
    case RnRecovery.Longs{}:
      %LR.str.below(0n, rd) : {RnRecovery.rec.ran(False{}, _, kept, RnRecovery.again(s, l, h), h, 0n, s, l, RnRecovery.Rec{RnRecovery.Longs{}, row, s, l}) == RunRecover.repeat_help.go(Nat.is_lt(0n, rd), 0n, RnRecovery.Longs{}, row, s, l) : RnRecovery.Dec}
      rq.tail(Nat.is_lt(0n, rd), kept, RnRecovery.again(s, l, h), h, 0n, RnRecovery.Longs{}, row, s, l)
    case RnRecovery.Leaks{}:
      %LR.str.below(0n, rd) : {RnRecovery.rec.ran(False{}, _, kept, RnRecovery.again(s, l, h), h, 0n, s, l, RnRecovery.Rec{RnRecovery.Leaks{}, row, s, l}) == RunRecover.repeat_help.go(Nat.is_lt(0n, rd), 0n, RnRecovery.Leaks{}, row, s, l) : RnRecovery.Dec}
      rq.tail(Nat.is_lt(0n, rd), kept, RnRecovery.again(s, l, h), h, 0n, RnRecovery.Leaks{}, row, s, l)
    case RnRecovery.Loops{}:
      %LR.str.below(row, rd) : {RnRecovery.rec.ran(False{}, _, kept, RnRecovery.again(s, l, h), h, row, s, l, RnRecovery.Rec{RnRecovery.Loops{}, row, s, l}) == RunRecover.repeat_help.go(Nat.is_lt(row, rd), row, RnRecovery.Loops{}, row, s, l) : RnRecovery.Dec}
      rq.tail(Nat.is_lt(row, rd), kept, RnRecovery.again(s, l, h), h, row, RnRecovery.Loops{}, row, s, l)
    case RnRecovery.Empties{}:
      %LR.str.below(0n, rd) : {RnRecovery.rec.ran(False{}, _, kept, RnRecovery.again(s, l, h), h, 0n, s, l, RnRecovery.Rec{RnRecovery.Empties{}, row, s, l}) == RunRecover.repeat_help.go(Nat.is_lt(0n, rd), 0n, RnRecovery.Empties{}, row, s, l) : RnRecovery.Dec}
      rq.tail(Nat.is_lt(0n, rd), kept, RnRecovery.again(s, l, h), h, 0n, RnRecovery.Empties{}, row, s, l)

# calls that make `repeat` or more rounds
def rq.ran(+lg: Nat, +lk: Nat, +rd: Nat, +rp: Nat, +h: Nat, +kept: Bool, +k: RnRecovery.Rk, +row: Nat, +s: Nat, +l: Nat, off: {RnRecovery.below(RnRecovery.again(s, l, h), rp) == False{} : Bool}) -> {RnRecovery.Rec.step(RnRecovery.RCfg{lg, lk, rd, rp}, RnRecovery.Ran{h, kept}, RnRecovery.Rec{k, row, s, l}) == RunRecover.repeat_help(rd, k, row, s, l) : RnRecovery.Dec}:
  %Equal.sym(Bool, RnRecovery.below(RnRecovery.again(s, l, h), rp), False{}, off) : {RnRecovery.rec.ran(_, RnRecovery.below(RnRecovery.Rk.loops(k, row), rd), kept, RnRecovery.again(s, l, h), h, RnRecovery.Rk.loops(k, row), s, l, RnRecovery.Rec{k, row, s, l}) == RunRecover.repeat_help(rd, k, row, s, l) : RnRecovery.Dec}
  rq.k(k, row, rd, h, kept, s, l)

# rebuilt leaked calls that make `repeat` or more rounds
def rq.leak(+lg: Nat, +lk: Nat, +rd: Nat, +rp: Nat, +h: Nat, +kept: Bool, +k: RnRecovery.Rk, +row: Nat, +s: Nat, +l: Nat, off: {RnRecovery.below(RnRecovery.again(s, l, h), rp) == False{} : Bool}) -> {RnRecovery.Rec.step(RnRecovery.RCfg{lg, lk, rd, rp}, RnRecovery.Leak{True{}, h, kept}, RnRecovery.Rec{k, row, s, l}) == RunRecover.repeat_help(rd, k, row, s, l) : RnRecovery.Dec}:
  %Equal.sym(Bool, RnRecovery.below(RnRecovery.again(s, l, h), rp), False{}, off) : {RnRecovery.rec.ran(_, RnRecovery.below(RnRecovery.Rk.loops(k, row), rd), kept, RnRecovery.again(s, l, h), h, RnRecovery.Rk.loops(k, row), s, l, RnRecovery.Rec{k, row, s, l}) == RunRecover.repeat_help(rd, k, row, s, l) : RnRecovery.Dec}
  rq.k(k, row, rd, h, kept, s, l)

def RunRecover.rec_repeat_never_runs(rc, h, kept, k, row, same, last, rep):
  match rc:
    case RnRecovery.RCfg{+long, +le, +re, +rp}:
      (rq.ran(long, le, re, rp, h, kept, k, row, same, last, LRR.rr.rounds_off(same, last, h, rp, rep)), rq.leak(long, le, re, rp, h, kept, k, row, same, last, LRR.rr.rounds_off(same, last, h, rp, rep)))
