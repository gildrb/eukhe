# eukhe: lemmas shared by the proofs of laws/stop/cut.bend (R10): what
# the spec's window test says of a cut reply, the model's says (stc.room,
# stc.spent, stc.full); a cut reply with text and room is read as the
# answer (stc.kept); one with text at a spent window and no compaction to
# make is dropped (stc.drops) and read as the run's end (stc.dropped); the
# ladder compacts at a full window (stc.compacts).

import Base
import ../../../bend/run/decision.bend as RnDecision
import ../../../bend/run/recovery.bend as RnRecovery
import ../../../bend/run/state.bend as RnState
import ../../../bend/stop.bend as S
import ../../../spec/harness/stop.bend as StSpec
import ../base.bend as LA
import ../../../laws/stop.bend as Stop

# a window the spec finds with room, the model finds with room
def stc.room(+w: Nat, +ca: Nat, +pr: Nat, +o: Nat, room: {StSpec.ran_out(w, ca, pr, o) == False{} : Bool}) -> {RnRecovery.bound(w, ca, pr, o) == False{} : Bool}:
  %LA.stb.bound(w, ca, pr, o) : {_ == False{} : Bool}
  room

# a window the spec finds run out, the model finds run out
def stc.spent(+w: Nat, +ca: Nat, +pr: Nat, +o: Nat, spent: {StSpec.ran_out(w, ca, pr, o) == True{} : Bool}) -> {RnRecovery.bound(w, ca, pr, o) == True{} : Bool}:
  %LA.stb.bound(w, ca, pr, o) : {_ == True{} : Bool}
  spent

# a window the spec finds full, the model finds full
def stc.full(+w: Nat, +ca: Nat, +pr: Nat, +o: Nat, cu: Bool, full: {StSpec.full(w, ca, pr, o, cu) == True{} : Bool}) -> {RnRecovery.full(w, ca, pr, o, cu) == True{} : Bool}:
  %LA.stb.full(w, ca, pr, o, cu) : {_ == True{} : Bool}
  full

# a cut reply with text whose window has room stands, and the run reads
# it as the answer
def stc.kept(sp: Bool, -b: Bool, -p: Bool, -rc: RnRecovery.RCfg, -k: RnRecovery.Rk, -row: Nat, -w: Nat, -ca: Nat, -pr: Nat, -o: Nat, -cu: Bool, -lo: Bool, e: {sp == False{} : Bool}) -> {Stop.stop_reply(S.walk(S.Facts{True{}, True{}, b, p, sp, cu}), S.Facts{True{}, True{}, b, p, sp, cu}, rc, k, row, w, ca, pr, o, cu, lo) == RnState.Plain{} : RnState.Reply}:
  match sp:
    case True{}:
      LA.stb.absurd({Stop.stop_reply(S.walk(S.Facts{True{}, True{}, b, p, True{}, cu}), S.Facts{True{}, True{}, b, p, True{}, cu}, rc, k, row, w, ca, pr, o, cu, lo) == RnState.Plain{} : RnState.Reply}, Equal.sym(Bool, True{}, False{}, e))
    case False{}:
      {==}

# a cut reply with text whose window is spent, with no compaction to
# make, is dropped
def stc.drops(sp: Bool, -b: Bool, -p: Bool, e: {sp == True{} : Bool}) -> {S.walk(S.Facts{True{}, True{}, b, p, sp, False{}}) == S.Drops{} : S.Pick}:
  match sp:
    case True{}:
      {==}
    case False{}:
      LA.stb.absurd({S.walk(S.Facts{True{}, True{}, b, p, False{}, False{}}) == S.Drops{} : S.Pick}, e)

# ... and the run reads the dropped reply as its end, as at an answer
def stc.dropped(sp: Bool, -b: Bool, -p: Bool, -rc: RnRecovery.RCfg, -k: RnRecovery.Rk, -row: Nat, -w: Nat, -ca: Nat, -pr: Nat, -o: Nat, -lo: Bool, e: {sp == True{} : Bool}) -> {Stop.stop_reply(S.walk(S.Facts{True{}, True{}, b, p, sp, False{}}), S.Facts{True{}, True{}, b, p, sp, False{}}, rc, k, row, w, ca, pr, o, False{}, lo) == RnState.Plain{} : RnState.Reply}:
  match sp:
    case True{}:
      {==}
    case False{}:
      LA.stb.absurd({Stop.stop_reply(S.walk(S.Facts{True{}, True{}, b, p, False{}, False{}}), S.Facts{True{}, True{}, b, p, False{}, False{}}, rc, k, row, w, ca, pr, o, False{}, lo) == RnState.Plain{} : RnState.Reply}, e)

# at a full window the ladder's first rung compacts, whatever the caps,
# the row and the levels
def stc.compacts(-rc: RnRecovery.RCfg, -k: RnRecovery.Rk, -row: Nat, -w: Nat, -ca: Nat, -pr: Nat, -o: Nat, -cu: Bool, -lo: Bool, e: {RnRecovery.full(w, ca, pr, o, cu) == True{} : Bool}) -> {RnDecision.decide.recover(rc, RnDecision.Thought{w, ca, pr, o, cu, lo}, k, row) == RnDecision.Compacts{} : RnDecision.Help}:
  %Equal.sym(Bool, RnRecovery.full(w, ca, pr, o, cu), True{}, e) : {RnDecision.Help.of(RnRecovery.rec.go(rc, RnRecovery.Think{_, lo}, k, row, 0n, 0n)) == RnDecision.Compacts{} : RnDecision.Help}
  {==}
