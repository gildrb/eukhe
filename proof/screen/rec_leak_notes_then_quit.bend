# eukhe: the proof of LAW rec_leak_notes_then_quit
#
# PROOF: as rec_length_notes_then_quit's, on the leak cap: induction on the
# notes left m, for every row j; below the cap m + j the leaked calls are
# retried with leak note j + 1, at it the run fails.

import Base
import ../../bend/run/recovery.bend as RnRecovery
import ../../laws/screen/recover.bend as ScreenRecover
import ./rec_length_notes_then_quit.bend as PRecLengthNotesThenQuit

def leak.row(m: Nat, +lg: Nat, +rd: Nat, +rp: Nat, +h: Nat, +kept: Bool, +j: Nat, +same: Nat, +last: Nat) -> {ScreenRecover.rec_row(RnRecovery.RCfg{lg, Nat.add(m, j), rd, rp}, RnRecovery.Leak{False{}, h, kept}, 1n+m, RnRecovery.Rec{RnRecovery.Leaks{}, j, same, last}) == ScreenRecover.rec_notes_then_quit(m, RnRecovery.Leaks{}, j, same, last) : List<&2, RnRecovery.Dec>}:
  match m:
    case 0n:
      %Equal.sym(Bool, RnRecovery.below(j, j), False{}, PRecLengthNotesThenQuit.long.below_self(j)) : {RnRecovery.rec.leak(_, j, same, last, RnRecovery.Rec{RnRecovery.Leaks{}, j, same, last}) <> ScreenRecover.rec_row(RnRecovery.RCfg{lg, j, rd, rp}, RnRecovery.Leak{False{}, h, kept}, 0n, RnRecovery.Dec.r(RnRecovery.rec.leak(_, j, same, last, RnRecovery.Rec{RnRecovery.Leaks{}, j, same, last}))) == [RnRecovery.Dec{RnRecovery.Quit{}, RnRecovery.Rec{RnRecovery.Leaks{}, j, same, last}}] : List<&2, RnRecovery.Dec>}
      {==}
    case 1n++p:
      %Equal.sym(Bool, RnRecovery.below(j, 1n+Nat.add(p, j)), True{}, PRecLengthNotesThenQuit.long.below_more(j, p)) : {RnRecovery.rec.leak(_, j, same, last, RnRecovery.Rec{RnRecovery.Leaks{}, j, same, last}) <> ScreenRecover.rec_row(RnRecovery.RCfg{lg, 1n+Nat.add(p, j), rd, rp}, RnRecovery.Leak{False{}, h, kept}, 1n+p, RnRecovery.Dec.r(RnRecovery.rec.leak(_, j, same, last, RnRecovery.Rec{RnRecovery.Leaks{}, j, same, last}))) == ScreenRecover.rec_notes_then_quit(1n+p, RnRecovery.Leaks{}, j, same, last) : List<&2, RnRecovery.Dec>}
      %PRecLengthNotesThenQuit.long.add_succ(p, j) : {RnRecovery.Dec{RnRecovery.Redo{}, RnRecovery.Rec{RnRecovery.Leaks{}, 1n+j, same, last}} <> ScreenRecover.rec_row(RnRecovery.RCfg{lg, _, rd, rp}, RnRecovery.Leak{False{}, h, kept}, 1n+p, RnRecovery.Rec{RnRecovery.Leaks{}, 1n+j, same, last}) == ScreenRecover.rec_notes_then_quit(1n+p, RnRecovery.Leaks{}, j, same, last) : List<&2, RnRecovery.Dec>}
      PRecLengthNotesThenQuit.long.cons(RnRecovery.Dec{RnRecovery.Redo{}, RnRecovery.Rec{RnRecovery.Leaks{}, 1n+j, same, last}}, ScreenRecover.rec_row(RnRecovery.RCfg{lg, Nat.add(p, 1n+j), rd, rp}, RnRecovery.Leak{False{}, h, kept}, 1n+p, RnRecovery.Rec{RnRecovery.Leaks{}, 1n+j, same, last}), ScreenRecover.rec_notes_then_quit(p, RnRecovery.Leaks{}, 1n+j, same, last), leak.row(p, lg, rd, rp, h, kept, 1n+j, same, last))

def ScreenRecover.rec_leak_notes_then_quit(lg, rd, rp, h, kept, j, m, same, last):
  leak.row(m, lg, rd, rp, h, kept, j, same, last)
