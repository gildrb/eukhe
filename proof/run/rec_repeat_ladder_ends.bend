# eukhe: the proof of LAW rec_repeat_ladder_ends
#
# PROOF: the spec's rounds are the model's (LRR.rr.rounds_off), so calls
# that make `repeat` or more rounds are no fresh calls; then as for
# decide.recover (LRR.rr.rep_go), on the model: under the redirect cap
# the step is the next redirect note, at the cap or past it the failed
# run; by induction on the notes left, each record the step leaves read
# next; a note that is no redirect note counts no redirect note.

import Base
import ../../bend/run/recovery.bend as RnRecovery
import ../../bend/run/decision.bend as RnDecision
import ../../laws/run/recover.bend as RunRecover
import ../stop/base/recover.bend as LR
import ./base/recover.bend as LRR

# under the redirect cap, the next redirect note, the rounds kept
def rl.under(+q: Nat, +j: Nat, +l0: Nat, +le: Nat, +rp: Nat, +h: Nat, +kept: Bool, +s: Nat, +l: Nat, off: {RnRecovery.below(RnRecovery.again(s, l, h), rp) == False{} : Bool}) -> {RnRecovery.Rec.step(RnRecovery.RCfg{l0, le, 1n+Nat.add(q, j), rp}, RnRecovery.Ran{h, kept}, RnRecovery.Rec{RnRecovery.Loops{}, j, s, l}) == RnRecovery.Dec{RnRecovery.Redo{}, RnRecovery.Rec{RnRecovery.Loops{}, 1n+j, s, l}} : RnRecovery.Dec}:
  %Equal.sym(Bool, RnRecovery.below(RnRecovery.again(s, l, h), rp), False{}, off) : {RnRecovery.rec.ran(_, RnRecovery.below(j, 1n+Nat.add(q, j)), kept, RnRecovery.again(s, l, h), h, j, s, l, RnRecovery.Rec{RnRecovery.Loops{}, j, s, l}) == RnRecovery.Dec{RnRecovery.Redo{}, RnRecovery.Rec{RnRecovery.Loops{}, 1n+j, s, l}} : RnRecovery.Dec}
  %Equal.sym(Bool, RnRecovery.below(j, 1n+Nat.add(q, j)), True{}, LR.str.below_add(q, j)) : {RnRecovery.rec.ran(False{}, _, kept, RnRecovery.again(s, l, h), h, j, s, l, RnRecovery.Rec{RnRecovery.Loops{}, j, s, l}) == RnRecovery.Dec{RnRecovery.Redo{}, RnRecovery.Rec{RnRecovery.Loops{}, 1n+j, s, l}} : RnRecovery.Dec}
  {==}

# at the redirect cap, the run fails
def rl.cap(+j: Nat, +l0: Nat, +le: Nat, +rp: Nat, +h: Nat, +kept: Bool, +s: Nat, +l: Nat, off: {RnRecovery.below(RnRecovery.again(s, l, h), rp) == False{} : Bool}) -> {RnRecovery.Rec.step(RnRecovery.RCfg{l0, le, j, rp}, RnRecovery.Ran{h, kept}, RnRecovery.Rec{RnRecovery.Loops{}, j, s, l}) == RnRecovery.Dec{RnRecovery.Quit{}, RnRecovery.Rec{RnRecovery.Loops{}, j, s, l}} : RnRecovery.Dec}:
  %Equal.sym(Bool, RnRecovery.below(RnRecovery.again(s, l, h), rp), False{}, off) : {RnRecovery.rec.ran(_, RnRecovery.below(j, j), kept, RnRecovery.again(s, l, h), h, j, s, l, RnRecovery.Rec{RnRecovery.Loops{}, j, s, l}) == RnRecovery.Dec{RnRecovery.Quit{}, RnRecovery.Rec{RnRecovery.Loops{}, j, s, l}} : RnRecovery.Dec}
  %Equal.sym(Bool, RnRecovery.below(j, j), False{}, LR.str.below_refl(j)) : {RnRecovery.rec.ran(False{}, _, kept, RnRecovery.again(s, l, h), h, j, s, l, RnRecovery.Rec{RnRecovery.Loops{}, j, s, l}) == RnRecovery.Dec{RnRecovery.Quit{}, RnRecovery.Rec{RnRecovery.Loops{}, j, s, l}} : RnRecovery.Dec}
  {==}

# past the redirect cap, the run fails
def rl.past(+j: Nat, +x: Nat, +l0: Nat, +le: Nat, +rp: Nat, +h: Nat, +kept: Bool, +s: Nat, +l: Nat, off: {RnRecovery.below(RnRecovery.again(s, l, h), rp) == False{} : Bool}) -> {RnRecovery.Dec.act(RnRecovery.Rec.step(RnRecovery.RCfg{l0, le, j, rp}, RnRecovery.Ran{h, kept}, RnRecovery.Rec{RnRecovery.Loops{}, Nat.add(j, x), s, l})) == RnRecovery.Quit{} : RnRecovery.Act}:
  %Equal.sym(Bool, RnRecovery.below(RnRecovery.again(s, l, h), rp), False{}, off) : {RnRecovery.Dec.act(RnRecovery.rec.ran(_, RnRecovery.below(Nat.add(j, x), j), kept, RnRecovery.again(s, l, h), h, Nat.add(j, x), s, l, RnRecovery.Rec{RnRecovery.Loops{}, Nat.add(j, x), s, l})) == RnRecovery.Quit{} : RnRecovery.Act}
  %Equal.sym(Bool, RnRecovery.below(Nat.add(j, x), j), False{}, LR.str.past(j, x)) : {RnRecovery.Dec.act(RnRecovery.rec.ran(False{}, _, kept, RnRecovery.again(s, l, h), h, Nat.add(j, x), s, l, RnRecovery.Rec{RnRecovery.Loops{}, Nat.add(j, x), s, l})) == RnRecovery.Quit{} : RnRecovery.Act}
  {==}

# from j redirect notes with m under the cap, m notes, then the run fails
def rl.go(m: Nat, +j: Nat, +l0: Nat, +le: Nat, +rp: Nat, +h: Nat, +kept: Bool, +s: Nat, +l: Nat, +off: {RnRecovery.below(RnRecovery.again(s, l, h), rp) == False{} : Bool}) -> {RunRecover.rec_helps(1n+m, RnRecovery.RCfg{l0, le, Nat.add(m, j), rp}, RnRecovery.Ran{h, kept}, RnRecovery.Rec.step(RnRecovery.RCfg{l0, le, Nat.add(m, j), rp}, RnRecovery.Ran{h, kept}, RnRecovery.Rec{RnRecovery.Loops{}, j, s, l})) == RunRecover.notes_then_quit(m, j) : List<&2, RnDecision.Help>}:
  match m:
    case 0n:
      %Equal.sym(RnRecovery.Dec, RnRecovery.Rec.step(RnRecovery.RCfg{l0, le, j, rp}, RnRecovery.Ran{h, kept}, RnRecovery.Rec{RnRecovery.Loops{}, j, s, l}), RnRecovery.Dec{RnRecovery.Quit{}, RnRecovery.Rec{RnRecovery.Loops{}, j, s, l}}, rl.cap(j, l0, le, rp, h, kept, s, l, off)) : {RunRecover.rec_helps(1n, RnRecovery.RCfg{l0, le, j, rp}, RnRecovery.Ran{h, kept}, _) == RunRecover.notes_then_quit(0n, j) : List<&2, RnDecision.Help>}
      {==}
    case 1n++q:
      %Equal.sym(RnRecovery.Dec, RnRecovery.Rec.step(RnRecovery.RCfg{l0, le, 1n+Nat.add(q, j), rp}, RnRecovery.Ran{h, kept}, RnRecovery.Rec{RnRecovery.Loops{}, j, s, l}), RnRecovery.Dec{RnRecovery.Redo{}, RnRecovery.Rec{RnRecovery.Loops{}, 1n+j, s, l}}, rl.under(q, j, l0, le, rp, h, kept, s, l, off)) : {RunRecover.rec_helps(2n+q, RnRecovery.RCfg{l0, le, 1n+Nat.add(q, j), rp}, RnRecovery.Ran{h, kept}, _) == RunRecover.notes_then_quit(1n+q, j) : List<&2, RnDecision.Help>}
      %LR.str.add_succ(q, j) : {RnDecision.Redoes{1n+j} <> RunRecover.rec_helps(1n+q, RnRecovery.RCfg{l0, le, _, rp}, RnRecovery.Ran{h, kept}, RnRecovery.Rec.step(RnRecovery.RCfg{l0, le, _, rp}, RnRecovery.Ran{h, kept}, RnRecovery.Rec{RnRecovery.Loops{}, 1n+j, s, l})) == RnDecision.Redoes{1n+j} <> RunRecover.notes_then_quit(q, 1n+j) : List<&2, RnDecision.Help>}
      %rl.go(q, 1n+j, l0, le, rp, h, kept, s, l, off) : {RnDecision.Redoes{1n+j} <> RunRecover.rec_helps(1n+q, RnRecovery.RCfg{l0, le, Nat.add(q, 1n+j), rp}, RnRecovery.Ran{h, kept}, RnRecovery.Rec.step(RnRecovery.RCfg{l0, le, Nat.add(q, 1n+j), rp}, RnRecovery.Ran{h, kept}, RnRecovery.Rec{RnRecovery.Loops{}, 1n+j, s, l})) == RnDecision.Redoes{1n+j} <> _ : List<&2, RnDecision.Help>}
      {==}

# with the repeat not fresh, a note that is no redirect note goes as a
# redirect note of row 0
def rl.first0(k: RnRecovery.Rk, +row: Nat, +l0: Nat, +le: Nat, re: Nat, +rp: Nat, +h: Nat, +kept: Bool, +s: Nat, +l: Nat, other: {RunRecover.loop_note(k) == False{} : Bool}) -> {RunRecover.rec_helps(1n+re, RnRecovery.RCfg{l0, le, re, rp}, RnRecovery.Ran{h, kept}, RnRecovery.rec.ran(False{}, RnRecovery.below(RnRecovery.Rk.loops(k, row), re), kept, RnRecovery.again(s, l, h), h, RnRecovery.Rk.loops(k, row), s, l, RnRecovery.Rec{k, row, s, l})) == RunRecover.rec_helps(1n+re, RnRecovery.RCfg{l0, le, re, rp}, RnRecovery.Ran{h, kept}, RnRecovery.rec.ran(False{}, RnRecovery.below(0n, re), kept, RnRecovery.again(s, l, h), h, 0n, s, l, RnRecovery.Rec{RnRecovery.Loops{}, 0n, s, l})) : List<&2, RnDecision.Help>}:
  match k:
    case RnRecovery.Free{}:
      match re:
        case 0n:
          {==}
        case 1n+z:
          {==}
    case RnRecovery.Longs{}:
      match re:
        case 0n:
          {==}
        case 1n+z:
          {==}
    case RnRecovery.Leaks{}:
      match re:
        case 0n:
          {==}
        case 1n+z:
          {==}
    case RnRecovery.Loops{}:
      LR.str.absurd_t({RunRecover.rec_helps(1n+re, RnRecovery.RCfg{l0, le, re, rp}, RnRecovery.Ran{h, kept}, RnRecovery.rec.ran(False{}, RnRecovery.below(row, re), kept, RnRecovery.again(s, l, h), h, row, s, l, RnRecovery.Rec{RnRecovery.Loops{}, row, s, l})) == RunRecover.rec_helps(1n+re, RnRecovery.RCfg{l0, le, re, rp}, RnRecovery.Ran{h, kept}, RnRecovery.rec.ran(False{}, RnRecovery.below(0n, re), kept, RnRecovery.again(s, l, h), h, 0n, s, l, RnRecovery.Rec{RnRecovery.Loops{}, 0n, s, l})) : List<&2, RnDecision.Help>}, other)
    case RnRecovery.Empties{}:
      match re:
        case 0n:
          {==}
        case 1n+z:
          {==}

def rl.first(+k: RnRecovery.Rk, +row: Nat, +l0: Nat, +le: Nat, +re: Nat, +rp: Nat, +h: Nat, +kept: Bool, +s: Nat, +l: Nat, off: {RnRecovery.below(RnRecovery.again(s, l, h), rp) == False{} : Bool}, other: {RunRecover.loop_note(k) == False{} : Bool}) -> {RunRecover.rec_helps(1n+re, RnRecovery.RCfg{l0, le, re, rp}, RnRecovery.Ran{h, kept}, RnRecovery.Rec.step(RnRecovery.RCfg{l0, le, re, rp}, RnRecovery.Ran{h, kept}, RnRecovery.Rec{k, row, s, l})) == RunRecover.rec_helps(1n+re, RnRecovery.RCfg{l0, le, re, rp}, RnRecovery.Ran{h, kept}, RnRecovery.Rec.step(RnRecovery.RCfg{l0, le, re, rp}, RnRecovery.Ran{h, kept}, RnRecovery.Rec{RnRecovery.Loops{}, 0n, s, l})) : List<&2, RnDecision.Help>}:
  %Equal.sym(Bool, RnRecovery.below(RnRecovery.again(s, l, h), rp), False{}, off) : {RunRecover.rec_helps(1n+re, RnRecovery.RCfg{l0, le, re, rp}, RnRecovery.Ran{h, kept}, RnRecovery.rec.ran(_, RnRecovery.below(RnRecovery.Rk.loops(k, row), re), kept, RnRecovery.again(s, l, h), h, RnRecovery.Rk.loops(k, row), s, l, RnRecovery.Rec{k, row, s, l})) == RunRecover.rec_helps(1n+re, RnRecovery.RCfg{l0, le, re, rp}, RnRecovery.Ran{h, kept}, RnRecovery.rec.ran(_, RnRecovery.below(0n, re), kept, RnRecovery.again(s, l, h), h, 0n, s, l, RnRecovery.Rec{RnRecovery.Loops{}, 0n, s, l})) : List<&2, RnDecision.Help>}
  rl.first0(k, row, l0, le, re, rp, h, kept, s, l, other)

# after a note that is no redirect note, redirect notes 1 to the cap, then
# the run fails
def rl.part(+k: RnRecovery.Rk, +row: Nat, +l0: Nat, +le: Nat, +re: Nat, +rp: Nat, +h: Nat, +kept: Bool, +s: Nat, +l: Nat, +off: {RnRecovery.below(RnRecovery.again(s, l, h), rp) == False{} : Bool}, other: {RunRecover.loop_note(k) == False{} : Bool}) -> {RunRecover.rec_helps(1n+re, RnRecovery.RCfg{l0, le, re, rp}, RnRecovery.Ran{h, kept}, RnRecovery.Rec.step(RnRecovery.RCfg{l0, le, re, rp}, RnRecovery.Ran{h, kept}, RnRecovery.Rec{k, row, s, l})) == RunRecover.notes_then_quit(re, 0n) : List<&2, RnDecision.Help>}:
  %Equal.sym(List<&2, RnDecision.Help>, RunRecover.rec_helps(1n+re, RnRecovery.RCfg{l0, le, re, rp}, RnRecovery.Ran{h, kept}, RnRecovery.Rec.step(RnRecovery.RCfg{l0, le, re, rp}, RnRecovery.Ran{h, kept}, RnRecovery.Rec{k, row, s, l})), RunRecover.rec_helps(1n+re, RnRecovery.RCfg{l0, le, re, rp}, RnRecovery.Ran{h, kept}, RnRecovery.Rec.step(RnRecovery.RCfg{l0, le, re, rp}, RnRecovery.Ran{h, kept}, RnRecovery.Rec{RnRecovery.Loops{}, 0n, s, l})), rl.first(k, row, l0, le, re, rp, h, kept, s, l, off, other)) : {_ == RunRecover.notes_then_quit(re, 0n) : List<&2, RnDecision.Help>}
  %LR.str.add_zero(re) : {RunRecover.rec_helps(1n+re, RnRecovery.RCfg{l0, le, _, rp}, RnRecovery.Ran{h, kept}, RnRecovery.Rec.step(RnRecovery.RCfg{l0, le, _, rp}, RnRecovery.Ran{h, kept}, RnRecovery.Rec{RnRecovery.Loops{}, 0n, s, l})) == RunRecover.notes_then_quit(re, 0n) : List<&2, RnDecision.Help>}
  rl.go(re, 0n, l0, le, rp, h, kept, s, l, off)

def RunRecover.rec_repeat_ladder_ends(rc, h, kept, k, row, same, last, x, rep, other):
  match rc:
    case RnRecovery.RCfg{+long, +le, +re, +rp}:
      (rl.part(k, row, long, le, re, rp, h, kept, same, last, LRR.rr.rounds_off(same, last, h, rp, rep), other), rl.past(re, x, long, le, rp, h, kept, same, last, LRR.rr.rounds_off(same, last, h, rp, rep)))
