# eukhe: the proof of LAW rec_think_gets_its_rung
#
# PROOF: by cases on the note: the length notes in a row the model reads
# (Rk.longs) are the spec's (length_notes), and `below` is Nat.is_lt
# (LR.str.below); then by cases on whether the window ran out with a
# compaction to make, a length note is left, and the last rung lowers.

import Base
import ../../bend/run/recovery.bend as RnRecovery
import ../../laws/run/recover.bend as RunRecover
import ../stop/base/recover.bend as LR

# the ladder's rungs
def tq.tail(shrink: Bool, under: Bool, lowers: Bool, +n: Nat, +k: RnRecovery.Rk, +row: Nat, +s: Nat, +l: Nat) -> {RnRecovery.rec.think(shrink, under, lowers, n, s, l, RnRecovery.Rec{k, row, s, l}) == RunRecover.think_help.go(shrink, under, lowers, n, k, row, s, l) : RnRecovery.Dec}:
  match shrink:
    case True{}:
      {==}
    case False{}:
      match under:
        case True{}:
          {==}
        case False{}:
          match lowers:
            case True{}:
              {==}
            case False{}:
              {==}

# the model's length notes in a row are the spec's, after any note
def tq.k(k: RnRecovery.Rk, +row: Nat, +long: Nat, +shrink: Bool, +lower: Bool, +s: Nat, +l: Nat) -> {RnRecovery.rec.think(shrink, RnRecovery.below(RnRecovery.Rk.longs(k, row), long), Bool.and(lower, Nat.is_eq(RnRecovery.Rk.longs(k, row), long)), RnRecovery.Rk.longs(k, row), s, l, RnRecovery.Rec{k, row, s, l}) == RunRecover.think_help(shrink, lower, long, k, row, s, l) : RnRecovery.Dec}:
  match k:
    case RnRecovery.Free{}:
      %LR.str.below(0n, long) : {RnRecovery.rec.think(shrink, _, Bool.and(lower, Nat.is_eq(0n, long)), 0n, s, l, RnRecovery.Rec{RnRecovery.Free{}, row, s, l}) == RunRecover.think_help.go(shrink, Nat.is_lt(0n, long), Bool.and(lower, Nat.is_eq(0n, long)), 0n, RnRecovery.Free{}, row, s, l) : RnRecovery.Dec}
      tq.tail(shrink, Nat.is_lt(0n, long), Bool.and(lower, Nat.is_eq(0n, long)), 0n, RnRecovery.Free{}, row, s, l)
    case RnRecovery.Longs{}:
      %LR.str.below(row, long) : {RnRecovery.rec.think(shrink, _, Bool.and(lower, Nat.is_eq(row, long)), row, s, l, RnRecovery.Rec{RnRecovery.Longs{}, row, s, l}) == RunRecover.think_help.go(shrink, Nat.is_lt(row, long), Bool.and(lower, Nat.is_eq(row, long)), row, RnRecovery.Longs{}, row, s, l) : RnRecovery.Dec}
      tq.tail(shrink, Nat.is_lt(row, long), Bool.and(lower, Nat.is_eq(row, long)), row, RnRecovery.Longs{}, row, s, l)
    case RnRecovery.Leaks{}:
      %LR.str.below(0n, long) : {RnRecovery.rec.think(shrink, _, Bool.and(lower, Nat.is_eq(0n, long)), 0n, s, l, RnRecovery.Rec{RnRecovery.Leaks{}, row, s, l}) == RunRecover.think_help.go(shrink, Nat.is_lt(0n, long), Bool.and(lower, Nat.is_eq(0n, long)), 0n, RnRecovery.Leaks{}, row, s, l) : RnRecovery.Dec}
      tq.tail(shrink, Nat.is_lt(0n, long), Bool.and(lower, Nat.is_eq(0n, long)), 0n, RnRecovery.Leaks{}, row, s, l)
    case RnRecovery.Loops{}:
      %LR.str.below(0n, long) : {RnRecovery.rec.think(shrink, _, Bool.and(lower, Nat.is_eq(0n, long)), 0n, s, l, RnRecovery.Rec{RnRecovery.Loops{}, row, s, l}) == RunRecover.think_help.go(shrink, Nat.is_lt(0n, long), Bool.and(lower, Nat.is_eq(0n, long)), 0n, RnRecovery.Loops{}, row, s, l) : RnRecovery.Dec}
      tq.tail(shrink, Nat.is_lt(0n, long), Bool.and(lower, Nat.is_eq(0n, long)), 0n, RnRecovery.Loops{}, row, s, l)
    case RnRecovery.Empties{}:
      %LR.str.below(0n, long) : {RnRecovery.rec.think(shrink, _, Bool.and(lower, Nat.is_eq(0n, long)), 0n, s, l, RnRecovery.Rec{RnRecovery.Empties{}, row, s, l}) == RunRecover.think_help.go(shrink, Nat.is_lt(0n, long), Bool.and(lower, Nat.is_eq(0n, long)), 0n, RnRecovery.Empties{}, row, s, l) : RnRecovery.Dec}
      tq.tail(shrink, Nat.is_lt(0n, long), Bool.and(lower, Nat.is_eq(0n, long)), 0n, RnRecovery.Empties{}, row, s, l)

def RunRecover.rec_think_gets_its_rung(rc, shrink, lower, k, row, same, last):
  tq.k(k, row, RnRecovery.RCfg.long(rc), shrink, lower, same, last)
