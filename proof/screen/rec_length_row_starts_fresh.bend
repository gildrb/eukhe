# eukhe: the proof of LAW rec_length_row_starts_fresh
#
# PROOF: a note of no recovery or of another one counts no length note, so
# the first length stop is below the cap 1 + m and is retried with length
# note 1; the rest of the row is rec_length_notes_then_quit's from row 1
# under the cap m + 1 (fresh.add_one). A length note is no other note.

import Base
import ../../bend/run/recovery.bend as RnRecovery
import ../../laws/screen/recover.bend as ScreenRecover
import ../base/logic/logic.bend as LLogicLogic
import ./rec_length_notes_then_quit.bend as PRecLengthNotesThenQuit

def fresh.add_one(m: Nat) -> {Nat.add(m, 1n) == 1n+m : Nat}:
  match m:
    case 0n:
      {==}
    case 1n+p:
      %fresh.add_one(p) : {1n+Nat.add(p, 1n) == 1n+_ : Nat}
      {==}

def fresh.at(+m: Nat, +lk: Nat, +rd: Nat, +rp: Nat, +same: Nat, +last: Nat) -> {RnRecovery.Dec{RnRecovery.Redo{}, RnRecovery.Rec{RnRecovery.Longs{}, 1n, same, last}} <> ScreenRecover.rec_row(RnRecovery.RCfg{1n+m, lk, rd, rp}, RnRecovery.Long{}, 1n+m, RnRecovery.Rec{RnRecovery.Longs{}, 1n, same, last}) == ScreenRecover.rec_notes_then_quit(1n+m, RnRecovery.Longs{}, 0n, same, last) : List<&2, RnRecovery.Dec>}:
  %fresh.add_one(m) : {RnRecovery.Dec{RnRecovery.Redo{}, RnRecovery.Rec{RnRecovery.Longs{}, 1n, same, last}} <> ScreenRecover.rec_row(RnRecovery.RCfg{_, lk, rd, rp}, RnRecovery.Long{}, 1n+m, RnRecovery.Rec{RnRecovery.Longs{}, 1n, same, last}) == ScreenRecover.rec_notes_then_quit(1n+m, RnRecovery.Longs{}, 0n, same, last) : List<&2, RnRecovery.Dec>}
  PRecLengthNotesThenQuit.long.cons(RnRecovery.Dec{RnRecovery.Redo{}, RnRecovery.Rec{RnRecovery.Longs{}, 1n, same, last}}, ScreenRecover.rec_row(RnRecovery.RCfg{Nat.add(m, 1n), lk, rd, rp}, RnRecovery.Long{}, 1n+m, RnRecovery.Rec{RnRecovery.Longs{}, 1n, same, last}), ScreenRecover.rec_notes_then_quit(m, RnRecovery.Longs{}, 1n, same, last), PRecLengthNotesThenQuit.long.row(m, lk, rd, rp, 1n, same, last))

def fresh.law(+lk: Nat, +rd: Nat, +rp: Nat, k: RnRecovery.Rk, +row: Nat, +m: Nat, +same: Nat, +last: Nat, other: {ScreenRecover.rec_is_longs(k) == False{} : Bool}) -> {ScreenRecover.rec_row(RnRecovery.RCfg{1n+m, lk, rd, rp}, RnRecovery.Long{}, 2n+m, RnRecovery.Rec{k, row, same, last}) == ScreenRecover.rec_notes_then_quit(1n+m, RnRecovery.Longs{}, 0n, same, last) : List<&2, RnRecovery.Dec>}:
  match k:
    case RnRecovery.Free{}:
      fresh.at(m, lk, rd, rp, same, last)
    case RnRecovery.Longs{}:
      LLogicLogic.screen.ps.absurdF({ScreenRecover.rec_row(RnRecovery.RCfg{1n+m, lk, rd, rp}, RnRecovery.Long{}, 2n+m, RnRecovery.Rec{RnRecovery.Longs{}, row, same, last}) == ScreenRecover.rec_notes_then_quit(1n+m, RnRecovery.Longs{}, 0n, same, last) : List<&2, RnRecovery.Dec>}, Equal.sym(Bool, True{}, False{}, other))
    case RnRecovery.Leaks{}:
      fresh.at(m, lk, rd, rp, same, last)
    case RnRecovery.Loops{}:
      fresh.at(m, lk, rd, rp, same, last)
    case RnRecovery.Empties{}:
      fresh.at(m, lk, rd, rp, same, last)

def ScreenRecover.rec_length_row_starts_fresh(lk, rd, rp, k, row, m, same, last, other):
  fresh.law(lk, rd, rp, k, row, m, same, last, other)
