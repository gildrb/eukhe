# eukhe: lemmas shared by the proofs of laws/stop/cut.bend (R10): what
# the spec's window test says of a cut reply, the model's says (stc.room,
# stc.ran_out); a cut reply with text and room is read as the answer
# (stc.kept); the ladder compacts at a full window (stc.compacts).

import Base
import ../../../bend/run/decision.bend as RnDecision
import ../../../bend/run/recovery.bend as RnRecovery
import ../../../bend/run/state.bend as RnState
import ../../../bend/stop.bend as S
import ../../../spec/harness/stop.bend as StSpec
import ../base.bend as LA
import ../../../laws/stop.bend as Stop

# a window the spec finds not full, the model finds not full
def stc.room(+w: Nat, +ca: Nat, +pr: Nat, +o: Nat, cu: Bool, room: {StSpec.full(w, ca, pr, o, cu) == False{} : Bool}) -> {RnRecovery.full(w, ca, pr, o, cu) == False{} : Bool}:
  %LA.stb.full(w, ca, pr, o, cu) : {_ == False{} : Bool}
  room

# a window the spec finds full, the model finds full
def stc.ran_out(+w: Nat, +ca: Nat, +pr: Nat, +o: Nat, cu: Bool, full: {StSpec.full(w, ca, pr, o, cu) == True{} : Bool}) -> {RnRecovery.full(w, ca, pr, o, cu) == True{} : Bool}:
  %LA.stb.full(w, ca, pr, o, cu) : {_ == True{} : Bool}
  full

# a cut reply with text that is not full stands, and the run reads it as
# the answer
def stc.kept(fu: Bool, -b: Bool, -p: Bool, -rc: RnRecovery.RCfg, -k: RnRecovery.Rk, -row: Nat, -w: Nat, -ca: Nat, -pr: Nat, -o: Nat, -cu: Bool, -lo: Bool, e: {fu == False{} : Bool}) -> {Stop.stop_reply(S.walk(S.Facts{True{}, True{}, b, p, fu}), S.Facts{True{}, True{}, b, p, fu}, rc, k, row, w, ca, pr, o, cu, lo) == RnState.Plain{} : RnState.Reply}:
  match fu:
    case True{}:
      LA.stb.absurd({Stop.stop_reply(S.walk(S.Facts{True{}, True{}, b, p, True{}}), S.Facts{True{}, True{}, b, p, True{}}, rc, k, row, w, ca, pr, o, cu, lo) == RnState.Plain{} : RnState.Reply}, Equal.sym(Bool, True{}, False{}, e))
    case False{}:
      {==}

# at a full window the ladder's first rung compacts, whatever the caps,
# the row and the levels
def stc.compacts(-rc: RnRecovery.RCfg, -k: RnRecovery.Rk, -row: Nat, -w: Nat, -ca: Nat, -pr: Nat, -o: Nat, -cu: Bool, -lo: Bool, e: {RnRecovery.full(w, ca, pr, o, cu) == True{} : Bool}) -> {RnDecision.decide.recover(rc, RnDecision.Thought{w, ca, pr, o, cu, lo}, k, row) == RnDecision.Compacts{} : RnDecision.Help}:
  %Equal.sym(Bool, RnRecovery.full(w, ca, pr, o, cu), True{}, e) : {RnDecision.Help.of(RnRecovery.rec.go(rc, RnRecovery.Think{_, lo}, k, row, 0n, 0n)) == RnDecision.Compacts{} : RnDecision.Help}
  {==}
