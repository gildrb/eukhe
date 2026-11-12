# eukhe: the proof of LAW rec_length_notes_then_quit
#
# PROOF: induction on the notes left m, for every row j: with m left the
# row j is below the cap m + j (long.below_more), so the length stop is
# retried with note j + 1 and m - 1 are left under the same cap, read as
# (m - 1) + (j + 1); with none left the row is at the cap (long.below_self)
# and the run fails.

import Base
import ../../bend/run/recovery.bend as RnRecovery
import ../../laws/screen/recover.bend as ScreenRecover

def long.add_succ(a: Nat, -b: Nat) -> {Nat.add(a, 1n+b) == 1n+Nat.add(a, b) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      %long.add_succ(p, b) : {1n+Nat.add(p, 1n+b) == 1n+_ : Nat}
      {==}

def long.below_self(j: Nat) -> {RnRecovery.below(j, j) == False{} : Bool}:
  match j:
    case 0n:
      {==}
    case 1n+q:
      long.below_self(q)

def long.below_more(j: Nat, +p: Nat) -> {RnRecovery.below(j, 1n+Nat.add(p, j)) == True{} : Bool}:
  match j:
    case 0n:
      {==}
    case 1n+q:
      %Equal.sym(Nat, Nat.add(p, 1n+q), 1n+Nat.add(p, q), long.add_succ(p, q)) : {RnRecovery.below(q, _) == True{} : Bool}
      long.below_more(q, p)

def long.cons(-d: RnRecovery.Dec, -xs: List<&2, RnRecovery.Dec>, -ys: List<&2, RnRecovery.Dec>, e: {xs == ys : List<&2, RnRecovery.Dec>}) -> {d <> xs == d <> ys : List<&2, RnRecovery.Dec>}:
  %e : {d <> xs == d <> _ : List<&2, RnRecovery.Dec>}
  {==}

def long.row(m: Nat, +lk: Nat, +rd: Nat, +rp: Nat, +j: Nat, +same: Nat, +last: Nat) -> {ScreenRecover.rec_row(RnRecovery.RCfg{Nat.add(m, j), lk, rd, rp}, RnRecovery.Think{False{}, False{}}, 1n+m, RnRecovery.Rec{RnRecovery.Longs{}, j, same, last}) == ScreenRecover.rec_notes_then_quit(m, RnRecovery.Longs{}, j, same, last) : List<&2, RnRecovery.Dec>}:
  match m:
    case 0n:
      %Equal.sym(Bool, RnRecovery.below(j, j), False{}, long.below_self(j)) : {RnRecovery.rec.think.note(_, False{}, j, same, last, RnRecovery.Rec{RnRecovery.Longs{}, j, same, last}) <> ScreenRecover.rec_row(RnRecovery.RCfg{j, lk, rd, rp}, RnRecovery.Think{False{}, False{}}, 0n, RnRecovery.Dec.r(RnRecovery.rec.think.note(_, False{}, j, same, last, RnRecovery.Rec{RnRecovery.Longs{}, j, same, last}))) == [RnRecovery.Dec{RnRecovery.Quit{}, RnRecovery.Rec{RnRecovery.Longs{}, j, same, last}}] : List<&2, RnRecovery.Dec>}
      {==}
    case 1n++p:
      %Equal.sym(Bool, RnRecovery.below(j, 1n+Nat.add(p, j)), True{}, long.below_more(j, p)) : {RnRecovery.rec.think.note(_, False{}, j, same, last, RnRecovery.Rec{RnRecovery.Longs{}, j, same, last}) <> ScreenRecover.rec_row(RnRecovery.RCfg{1n+Nat.add(p, j), lk, rd, rp}, RnRecovery.Think{False{}, False{}}, 1n+p, RnRecovery.Dec.r(RnRecovery.rec.think.note(_, False{}, j, same, last, RnRecovery.Rec{RnRecovery.Longs{}, j, same, last}))) == ScreenRecover.rec_notes_then_quit(1n+p, RnRecovery.Longs{}, j, same, last) : List<&2, RnRecovery.Dec>}
      %long.add_succ(p, j) : {RnRecovery.Dec{RnRecovery.Redo{}, RnRecovery.Rec{RnRecovery.Longs{}, 1n+j, same, last}} <> ScreenRecover.rec_row(RnRecovery.RCfg{_, lk, rd, rp}, RnRecovery.Think{False{}, False{}}, 1n+p, RnRecovery.Rec{RnRecovery.Longs{}, 1n+j, same, last}) == ScreenRecover.rec_notes_then_quit(1n+p, RnRecovery.Longs{}, j, same, last) : List<&2, RnRecovery.Dec>}
      long.cons(RnRecovery.Dec{RnRecovery.Redo{}, RnRecovery.Rec{RnRecovery.Longs{}, 1n+j, same, last}}, ScreenRecover.rec_row(RnRecovery.RCfg{Nat.add(p, 1n+j), lk, rd, rp}, RnRecovery.Think{False{}, False{}}, 1n+p, RnRecovery.Rec{RnRecovery.Longs{}, 1n+j, same, last}), ScreenRecover.rec_notes_then_quit(p, RnRecovery.Longs{}, 1n+j, same, last), long.row(p, lk, rd, rp, 1n+j, same, last))

def ScreenRecover.rec_length_notes_then_quit(lk, rd, rp, j, m, same, last):
  long.row(m, lk, rd, rp, j, same, last)
