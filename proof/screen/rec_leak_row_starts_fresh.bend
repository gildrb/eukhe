# eukhe: the proof of LAW rec_leak_row_starts_fresh
#
# PROOF: as rec_length_row_starts_fresh's, on the leak cap: a note of no
# recovery or of another one counts no leak note, so the first leak is
# retried with leak note 1, and the rest is rec_leak_notes_then_quit's from
# row 1 under the cap m + 1. A leak note is no other note.

import Base
import ../../bend/run/recovery.bend as RnRecovery
import ../../laws/screen/recover.bend as ScreenRecover
import ../base/logic/logic.bend as LLogicLogic
import ./rec_length_notes_then_quit.bend as PRecLengthNotesThenQuit
import ./rec_length_row_starts_fresh.bend as PRecLengthRowStartsFresh
import ./rec_leak_notes_then_quit.bend as PRecLeakNotesThenQuit

def leakfresh.at(+m: Nat, +lg: Nat, +rd: Nat, +rp: Nat, +h: Nat, +kept: Bool, +same: Nat, +last: Nat) -> {RnRecovery.Dec{RnRecovery.Redo{}, RnRecovery.Rec{RnRecovery.Leaks{}, 1n, same, last}} <> ScreenRecover.rec_row(RnRecovery.RCfg{lg, 1n+m, rd, rp}, RnRecovery.Leak{False{}, h, kept}, 1n+m, RnRecovery.Rec{RnRecovery.Leaks{}, 1n, same, last}) == ScreenRecover.rec_notes_then_quit(1n+m, RnRecovery.Leaks{}, 0n, same, last) : List<&2, RnRecovery.Dec>}:
  %PRecLengthRowStartsFresh.fresh.add_one(m) : {RnRecovery.Dec{RnRecovery.Redo{}, RnRecovery.Rec{RnRecovery.Leaks{}, 1n, same, last}} <> ScreenRecover.rec_row(RnRecovery.RCfg{lg, _, rd, rp}, RnRecovery.Leak{False{}, h, kept}, 1n+m, RnRecovery.Rec{RnRecovery.Leaks{}, 1n, same, last}) == ScreenRecover.rec_notes_then_quit(1n+m, RnRecovery.Leaks{}, 0n, same, last) : List<&2, RnRecovery.Dec>}
  PRecLengthNotesThenQuit.long.cons(RnRecovery.Dec{RnRecovery.Redo{}, RnRecovery.Rec{RnRecovery.Leaks{}, 1n, same, last}}, ScreenRecover.rec_row(RnRecovery.RCfg{lg, Nat.add(m, 1n), rd, rp}, RnRecovery.Leak{False{}, h, kept}, 1n+m, RnRecovery.Rec{RnRecovery.Leaks{}, 1n, same, last}), ScreenRecover.rec_notes_then_quit(m, RnRecovery.Leaks{}, 1n, same, last), PRecLeakNotesThenQuit.leak.row(m, lg, rd, rp, h, kept, 1n, same, last))

def leakfresh.law(+lg: Nat, +rd: Nat, +rp: Nat, +h: Nat, +kept: Bool, k: RnRecovery.Rk, +row: Nat, +m: Nat, +same: Nat, +last: Nat, other: {ScreenRecover.rec_is_leaks(k) == False{} : Bool}) -> {ScreenRecover.rec_row(RnRecovery.RCfg{lg, 1n+m, rd, rp}, RnRecovery.Leak{False{}, h, kept}, 2n+m, RnRecovery.Rec{k, row, same, last}) == ScreenRecover.rec_notes_then_quit(1n+m, RnRecovery.Leaks{}, 0n, same, last) : List<&2, RnRecovery.Dec>}:
  match k:
    case RnRecovery.Free{}:
      leakfresh.at(m, lg, rd, rp, h, kept, same, last)
    case RnRecovery.Longs{}:
      leakfresh.at(m, lg, rd, rp, h, kept, same, last)
    case RnRecovery.Leaks{}:
      LLogicLogic.screen.ps.absurdF({ScreenRecover.rec_row(RnRecovery.RCfg{lg, 1n+m, rd, rp}, RnRecovery.Leak{False{}, h, kept}, 2n+m, RnRecovery.Rec{RnRecovery.Leaks{}, row, same, last}) == ScreenRecover.rec_notes_then_quit(1n+m, RnRecovery.Leaks{}, 0n, same, last) : List<&2, RnRecovery.Dec>}, Equal.sym(Bool, True{}, False{}, other))
    case RnRecovery.Loops{}:
      leakfresh.at(m, lg, rd, rp, h, kept, same, last)
    case RnRecovery.Empties{}:
      leakfresh.at(m, lg, rd, rp, h, kept, same, last)

def ScreenRecover.rec_leak_row_starts_fresh(lg, rd, rp, h, kept, k, row, m, same, last, other):
  leakfresh.law(lg, rd, rp, h, kept, k, row, m, same, last, other)
