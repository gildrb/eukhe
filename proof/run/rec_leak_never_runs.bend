# eukhe: the proof of LAW rec_leak_never_runs
#
# PROOF: by cases on the note: the leak notes in a row the model reads
# (Rk.leaks) are the spec's (leak_notes), and `below` is Nat.is_lt
# (LR.str.below); then by cases on whether a leak note is left.

import Base
import ../../bend/run/recovery.bend as RnRecovery
import ../../laws/run/recover.bend as RunRecover
import ../stop/base/recover.bend as LR

# under the leak cap the next leak note, else the run fails
def lq.tail(b: Bool, +n: Nat, +k: RnRecovery.Rk, +row: Nat, +s: Nat, +l: Nat) -> {RnRecovery.rec.leak(b, n, s, l, RnRecovery.Rec{k, row, s, l}) == RunRecover.note_help.go(b, RnRecovery.Leaks{}, n, k, row, s, l) : RnRecovery.Dec}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# the model's leak notes in a row are the spec's, after any note
def lq.k(k: RnRecovery.Rk, +row: Nat, +lk: Nat, +s: Nat, +l: Nat) -> {RnRecovery.rec.leak(RnRecovery.below(RnRecovery.Rk.leaks(k, row), lk), RnRecovery.Rk.leaks(k, row), s, l, RnRecovery.Rec{k, row, s, l}) == RunRecover.note_help(lk, RnRecovery.Leaks{}, RunRecover.leak_notes(k, row), k, row, s, l) : RnRecovery.Dec}:
  match k:
    case RnRecovery.Free{}:
      %LR.str.below(0n, lk) : {RnRecovery.rec.leak(_, 0n, s, l, RnRecovery.Rec{RnRecovery.Free{}, row, s, l}) == RunRecover.note_help.go(Nat.is_lt(0n, lk), RnRecovery.Leaks{}, 0n, RnRecovery.Free{}, row, s, l) : RnRecovery.Dec}
      lq.tail(Nat.is_lt(0n, lk), 0n, RnRecovery.Free{}, row, s, l)
    case RnRecovery.Longs{}:
      %LR.str.below(0n, lk) : {RnRecovery.rec.leak(_, 0n, s, l, RnRecovery.Rec{RnRecovery.Longs{}, row, s, l}) == RunRecover.note_help.go(Nat.is_lt(0n, lk), RnRecovery.Leaks{}, 0n, RnRecovery.Longs{}, row, s, l) : RnRecovery.Dec}
      lq.tail(Nat.is_lt(0n, lk), 0n, RnRecovery.Longs{}, row, s, l)
    case RnRecovery.Leaks{}:
      %LR.str.below(row, lk) : {RnRecovery.rec.leak(_, row, s, l, RnRecovery.Rec{RnRecovery.Leaks{}, row, s, l}) == RunRecover.note_help.go(Nat.is_lt(row, lk), RnRecovery.Leaks{}, row, RnRecovery.Leaks{}, row, s, l) : RnRecovery.Dec}
      lq.tail(Nat.is_lt(row, lk), row, RnRecovery.Leaks{}, row, s, l)
    case RnRecovery.Loops{}:
      %LR.str.below(0n, lk) : {RnRecovery.rec.leak(_, 0n, s, l, RnRecovery.Rec{RnRecovery.Loops{}, row, s, l}) == RunRecover.note_help.go(Nat.is_lt(0n, lk), RnRecovery.Leaks{}, 0n, RnRecovery.Loops{}, row, s, l) : RnRecovery.Dec}
      lq.tail(Nat.is_lt(0n, lk), 0n, RnRecovery.Loops{}, row, s, l)
    case RnRecovery.Empties{}:
      %LR.str.below(0n, lk) : {RnRecovery.rec.leak(_, 0n, s, l, RnRecovery.Rec{RnRecovery.Empties{}, row, s, l}) == RunRecover.note_help.go(Nat.is_lt(0n, lk), RnRecovery.Leaks{}, 0n, RnRecovery.Empties{}, row, s, l) : RnRecovery.Dec}
      lq.tail(Nat.is_lt(0n, lk), 0n, RnRecovery.Empties{}, row, s, l)

def RunRecover.rec_leak_never_runs(rc, h, kept, k, row, same, last):
  lq.k(k, row, RnRecovery.RCfg.leak(rc), same, last)
