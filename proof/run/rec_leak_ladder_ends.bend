# eukhe: the proof of LAW rec_leak_ladder_ends
#
# PROOF: as for decide.recover (LRR.rr.leak_go), on the model: under the
# cap the step is the next leak note, at the cap or past it the failed
# run; by induction on the notes left, each record the step leaves read
# next; a note that is no leak note counts no leak note.

import Base
import ../../bend/run/recovery.bend as RnRecovery
import ../../bend/run/decision.bend as RnDecision
import ../../laws/run/recover.bend as RunRecover
import ../stop/base/recover.bend as LR

# under the cap, the next leak note, the rounds kept
def lk.under(+q: Nat, +j: Nat, +l0: Nat, +re: Nat, +rp: Nat, +h: Nat, +kept: Bool, +s: Nat, +l: Nat) -> {RnRecovery.Rec.step(RnRecovery.RCfg{l0, 1n+Nat.add(q, j), re, rp}, RnRecovery.Leak{False{}, h, kept}, RnRecovery.Rec{RnRecovery.Leaks{}, j, s, l}) == RnRecovery.Dec{RnRecovery.Redo{}, RnRecovery.Rec{RnRecovery.Leaks{}, 1n+j, s, l}} : RnRecovery.Dec}:
  %Equal.sym(Bool, RnRecovery.below(j, 1n+Nat.add(q, j)), True{}, LR.str.below_add(q, j)) : {RnRecovery.rec.leak(_, j, s, l, RnRecovery.Rec{RnRecovery.Leaks{}, j, s, l}) == RnRecovery.Dec{RnRecovery.Redo{}, RnRecovery.Rec{RnRecovery.Leaks{}, 1n+j, s, l}} : RnRecovery.Dec}
  {==}

# at the cap, the run fails
def lk.cap(+j: Nat, +l0: Nat, +re: Nat, +rp: Nat, +h: Nat, +kept: Bool, +s: Nat, +l: Nat) -> {RnRecovery.Rec.step(RnRecovery.RCfg{l0, j, re, rp}, RnRecovery.Leak{False{}, h, kept}, RnRecovery.Rec{RnRecovery.Leaks{}, j, s, l}) == RnRecovery.Dec{RnRecovery.Quit{}, RnRecovery.Rec{RnRecovery.Leaks{}, j, s, l}} : RnRecovery.Dec}:
  %Equal.sym(Bool, RnRecovery.below(j, j), False{}, LR.str.below_refl(j)) : {RnRecovery.rec.leak(_, j, s, l, RnRecovery.Rec{RnRecovery.Leaks{}, j, s, l}) == RnRecovery.Dec{RnRecovery.Quit{}, RnRecovery.Rec{RnRecovery.Leaks{}, j, s, l}} : RnRecovery.Dec}
  {==}

# past the cap, the run fails
def lk.past(+j: Nat, +x: Nat, +l0: Nat, +re: Nat, +rp: Nat, +h: Nat, +kept: Bool, +s: Nat, +l: Nat) -> {RnRecovery.Dec.act(RnRecovery.Rec.step(RnRecovery.RCfg{l0, j, re, rp}, RnRecovery.Leak{False{}, h, kept}, RnRecovery.Rec{RnRecovery.Leaks{}, Nat.add(j, x), s, l})) == RnRecovery.Quit{} : RnRecovery.Act}:
  %Equal.sym(Bool, RnRecovery.below(Nat.add(j, x), j), False{}, LR.str.past(j, x)) : {RnRecovery.Dec.act(RnRecovery.rec.leak(_, Nat.add(j, x), s, l, RnRecovery.Rec{RnRecovery.Leaks{}, Nat.add(j, x), s, l})) == RnRecovery.Quit{} : RnRecovery.Act}
  {==}

# from j notes with m under the cap, m notes, then the run fails
def lk.go(m: Nat, +j: Nat, +l0: Nat, +re: Nat, +rp: Nat, +h: Nat, +kept: Bool, +s: Nat, +l: Nat) -> {RunRecover.rec_helps(1n+m, RnRecovery.RCfg{l0, Nat.add(m, j), re, rp}, RnRecovery.Leak{False{}, h, kept}, RnRecovery.Rec.step(RnRecovery.RCfg{l0, Nat.add(m, j), re, rp}, RnRecovery.Leak{False{}, h, kept}, RnRecovery.Rec{RnRecovery.Leaks{}, j, s, l})) == RunRecover.notes_then_quit(m, j) : List<&2, RnDecision.Help>}:
  match m:
    case 0n:
      %Equal.sym(RnRecovery.Dec, RnRecovery.Rec.step(RnRecovery.RCfg{l0, j, re, rp}, RnRecovery.Leak{False{}, h, kept}, RnRecovery.Rec{RnRecovery.Leaks{}, j, s, l}), RnRecovery.Dec{RnRecovery.Quit{}, RnRecovery.Rec{RnRecovery.Leaks{}, j, s, l}}, lk.cap(j, l0, re, rp, h, kept, s, l)) : {RunRecover.rec_helps(1n, RnRecovery.RCfg{l0, j, re, rp}, RnRecovery.Leak{False{}, h, kept}, _) == RunRecover.notes_then_quit(0n, j) : List<&2, RnDecision.Help>}
      {==}
    case 1n++q:
      %Equal.sym(RnRecovery.Dec, RnRecovery.Rec.step(RnRecovery.RCfg{l0, 1n+Nat.add(q, j), re, rp}, RnRecovery.Leak{False{}, h, kept}, RnRecovery.Rec{RnRecovery.Leaks{}, j, s, l}), RnRecovery.Dec{RnRecovery.Redo{}, RnRecovery.Rec{RnRecovery.Leaks{}, 1n+j, s, l}}, lk.under(q, j, l0, re, rp, h, kept, s, l)) : {RunRecover.rec_helps(2n+q, RnRecovery.RCfg{l0, 1n+Nat.add(q, j), re, rp}, RnRecovery.Leak{False{}, h, kept}, _) == RunRecover.notes_then_quit(1n+q, j) : List<&2, RnDecision.Help>}
      %LR.str.add_succ(q, j) : {RnDecision.Redoes{1n+j} <> RunRecover.rec_helps(1n+q, RnRecovery.RCfg{l0, _, re, rp}, RnRecovery.Leak{False{}, h, kept}, RnRecovery.Rec.step(RnRecovery.RCfg{l0, _, re, rp}, RnRecovery.Leak{False{}, h, kept}, RnRecovery.Rec{RnRecovery.Leaks{}, 1n+j, s, l})) == RnDecision.Redoes{1n+j} <> RunRecover.notes_then_quit(q, 1n+j) : List<&2, RnDecision.Help>}
      %lk.go(q, 1n+j, l0, re, rp, h, kept, s, l) : {RnDecision.Redoes{1n+j} <> RunRecover.rec_helps(1n+q, RnRecovery.RCfg{l0, Nat.add(q, 1n+j), re, rp}, RnRecovery.Leak{False{}, h, kept}, RnRecovery.Rec.step(RnRecovery.RCfg{l0, Nat.add(q, 1n+j), re, rp}, RnRecovery.Leak{False{}, h, kept}, RnRecovery.Rec{RnRecovery.Leaks{}, 1n+j, s, l})) == RnDecision.Redoes{1n+j} <> _ : List<&2, RnDecision.Help>}
      {==}

# a note that is no leak note counts no leak note: the row goes as after
# a leak note of row 0
def lk.first(k: RnRecovery.Rk, +row: Nat, +long: Nat, le: Nat, +re: Nat, +rp: Nat, +h: Nat, +kept: Bool, +s: Nat, +l: Nat, other: {RunRecover.leak_note(k) == False{} : Bool}) -> {RunRecover.rec_helps(1n+le, RnRecovery.RCfg{long, le, re, rp}, RnRecovery.Leak{False{}, h, kept}, RnRecovery.Rec.step(RnRecovery.RCfg{long, le, re, rp}, RnRecovery.Leak{False{}, h, kept}, RnRecovery.Rec{k, row, s, l})) == RunRecover.rec_helps(1n+le, RnRecovery.RCfg{long, le, re, rp}, RnRecovery.Leak{False{}, h, kept}, RnRecovery.Rec.step(RnRecovery.RCfg{long, le, re, rp}, RnRecovery.Leak{False{}, h, kept}, RnRecovery.Rec{RnRecovery.Leaks{}, 0n, s, l})) : List<&2, RnDecision.Help>}:
  match k:
    case RnRecovery.Free{}:
      match le:
        case 0n:
          {==}
        case 1n+z:
          {==}
    case RnRecovery.Longs{}:
      match le:
        case 0n:
          {==}
        case 1n+z:
          {==}
    case RnRecovery.Leaks{}:
      LR.str.absurd_t({RunRecover.rec_helps(1n+le, RnRecovery.RCfg{long, le, re, rp}, RnRecovery.Leak{False{}, h, kept}, RnRecovery.Rec.step(RnRecovery.RCfg{long, le, re, rp}, RnRecovery.Leak{False{}, h, kept}, RnRecovery.Rec{RnRecovery.Leaks{}, row, s, l})) == RunRecover.rec_helps(1n+le, RnRecovery.RCfg{long, le, re, rp}, RnRecovery.Leak{False{}, h, kept}, RnRecovery.Rec.step(RnRecovery.RCfg{long, le, re, rp}, RnRecovery.Leak{False{}, h, kept}, RnRecovery.Rec{RnRecovery.Leaks{}, 0n, s, l})) : List<&2, RnDecision.Help>}, other)
    case RnRecovery.Loops{}:
      match le:
        case 0n:
          {==}
        case 1n+z:
          {==}
    case RnRecovery.Empties{}:
      match le:
        case 0n:
          {==}
        case 1n+z:
          {==}

# after a note that is no leak note, notes 1 to the cap, then the run fails
def lk.part(+k: RnRecovery.Rk, +row: Nat, +long: Nat, +le: Nat, +re: Nat, +rp: Nat, +h: Nat, +kept: Bool, +s: Nat, +l: Nat, other: {RunRecover.leak_note(k) == False{} : Bool}) -> {RunRecover.rec_helps(1n+le, RnRecovery.RCfg{long, le, re, rp}, RnRecovery.Leak{False{}, h, kept}, RnRecovery.Rec.step(RnRecovery.RCfg{long, le, re, rp}, RnRecovery.Leak{False{}, h, kept}, RnRecovery.Rec{k, row, s, l})) == RunRecover.notes_then_quit(le, 0n) : List<&2, RnDecision.Help>}:
  %Equal.sym(List<&2, RnDecision.Help>, RunRecover.rec_helps(1n+le, RnRecovery.RCfg{long, le, re, rp}, RnRecovery.Leak{False{}, h, kept}, RnRecovery.Rec.step(RnRecovery.RCfg{long, le, re, rp}, RnRecovery.Leak{False{}, h, kept}, RnRecovery.Rec{k, row, s, l})), RunRecover.rec_helps(1n+le, RnRecovery.RCfg{long, le, re, rp}, RnRecovery.Leak{False{}, h, kept}, RnRecovery.Rec.step(RnRecovery.RCfg{long, le, re, rp}, RnRecovery.Leak{False{}, h, kept}, RnRecovery.Rec{RnRecovery.Leaks{}, 0n, s, l})), lk.first(k, row, long, le, re, rp, h, kept, s, l, other)) : {_ == RunRecover.notes_then_quit(le, 0n) : List<&2, RnDecision.Help>}
  %LR.str.add_zero(le) : {RunRecover.rec_helps(1n+le, RnRecovery.RCfg{long, _, re, rp}, RnRecovery.Leak{False{}, h, kept}, RnRecovery.Rec.step(RnRecovery.RCfg{long, _, re, rp}, RnRecovery.Leak{False{}, h, kept}, RnRecovery.Rec{RnRecovery.Leaks{}, 0n, s, l})) == RunRecover.notes_then_quit(le, 0n) : List<&2, RnDecision.Help>}
  lk.go(le, 0n, long, re, rp, h, kept, s, l)

def RunRecover.rec_leak_ladder_ends(rc, h, kept, k, row, same, last, x, other):
  match rc:
    case RnRecovery.RCfg{+long, +le, +re, +rp}:
      (lk.part(k, row, long, le, re, rp, h, kept, same, last, other), lk.past(le, x, long, re, rp, h, kept, same, last))
