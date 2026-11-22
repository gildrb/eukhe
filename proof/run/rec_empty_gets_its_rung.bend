# eukhe: the proof of LAW rec_empty_gets_its_rung
#
# PROOF: the empty cap is 3 (Stop.empty_cap); by cases on the note: the
# empty notes in a row the model reads (Rk.empties) are the spec's
# (empty_notes), and `below` is Nat.is_lt (LR.str.below); then by cases
# on whether an empty note is left.

import Base
import ../../bend/run/recovery.bend as RnRecovery
import ../../laws/run/recover.bend as RunRecover
import ../stop/base/recover.bend as LR

# under the empty cap the next empty note, else the run fails
def eq.tail(b: Bool, +n: Nat, +k: RnRecovery.Rk, +row: Nat, +s: Nat, +l: Nat) -> {RnRecovery.rec.empty(b, n, s, l, RnRecovery.Rec{k, row, s, l}) == RunRecover.note_help.go(b, RnRecovery.Empties{}, n, k, row, s, l) : RnRecovery.Dec}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# the model's empty notes in a row are the spec's, after any note
def eq.k(k: RnRecovery.Rk, +row: Nat, +s: Nat, +l: Nat) -> {RnRecovery.rec.empty(RnRecovery.below(RnRecovery.Rk.empties(k, row), 3n), RnRecovery.Rk.empties(k, row), s, l, RnRecovery.Rec{k, row, s, l}) == RunRecover.note_help(3n, RnRecovery.Empties{}, RunRecover.empty_notes(k, row), k, row, s, l) : RnRecovery.Dec}:
  match k:
    case RnRecovery.Free{}:
      %LR.str.below(0n, 3n) : {RnRecovery.rec.empty(_, 0n, s, l, RnRecovery.Rec{RnRecovery.Free{}, row, s, l}) == RunRecover.note_help.go(Nat.is_lt(0n, 3n), RnRecovery.Empties{}, 0n, RnRecovery.Free{}, row, s, l) : RnRecovery.Dec}
      eq.tail(Nat.is_lt(0n, 3n), 0n, RnRecovery.Free{}, row, s, l)
    case RnRecovery.Longs{}:
      %LR.str.below(0n, 3n) : {RnRecovery.rec.empty(_, 0n, s, l, RnRecovery.Rec{RnRecovery.Longs{}, row, s, l}) == RunRecover.note_help.go(Nat.is_lt(0n, 3n), RnRecovery.Empties{}, 0n, RnRecovery.Longs{}, row, s, l) : RnRecovery.Dec}
      eq.tail(Nat.is_lt(0n, 3n), 0n, RnRecovery.Longs{}, row, s, l)
    case RnRecovery.Leaks{}:
      %LR.str.below(0n, 3n) : {RnRecovery.rec.empty(_, 0n, s, l, RnRecovery.Rec{RnRecovery.Leaks{}, row, s, l}) == RunRecover.note_help.go(Nat.is_lt(0n, 3n), RnRecovery.Empties{}, 0n, RnRecovery.Leaks{}, row, s, l) : RnRecovery.Dec}
      eq.tail(Nat.is_lt(0n, 3n), 0n, RnRecovery.Leaks{}, row, s, l)
    case RnRecovery.Loops{}:
      %LR.str.below(0n, 3n) : {RnRecovery.rec.empty(_, 0n, s, l, RnRecovery.Rec{RnRecovery.Loops{}, row, s, l}) == RunRecover.note_help.go(Nat.is_lt(0n, 3n), RnRecovery.Empties{}, 0n, RnRecovery.Loops{}, row, s, l) : RnRecovery.Dec}
      eq.tail(Nat.is_lt(0n, 3n), 0n, RnRecovery.Loops{}, row, s, l)
    case RnRecovery.Empties{}:
      %LR.str.below(row, 3n) : {RnRecovery.rec.empty(_, row, s, l, RnRecovery.Rec{RnRecovery.Empties{}, row, s, l}) == RunRecover.note_help.go(Nat.is_lt(row, 3n), RnRecovery.Empties{}, row, RnRecovery.Empties{}, row, s, l) : RnRecovery.Dec}
      eq.tail(Nat.is_lt(row, 3n), row, RnRecovery.Empties{}, row, s, l)

def RunRecover.rec_empty_gets_its_rung(rc, k, row, same, last):
  eq.k(k, row, same, last)
