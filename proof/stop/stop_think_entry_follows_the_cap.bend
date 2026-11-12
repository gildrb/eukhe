# eukhe: the proof of LAW stop_think_entry_follows_the_cap
#
# PROOF: each spelled request is the entry's encoding of its recover request, which fits the wire, so the entry answers the encoded decision (run_ffi_answers); under the cap the decision is the next note (LR.str.think_under), at it, with no lower level, the failure (LR.str.think_quit).

import Base
import ../../bend/ffi_run.bend as FRn
import ../../bend/wire.bend as Wr
import ../../bend/run/recovery.bend as RnRecovery
import ../../bend/run/decision.bend as RnDecision
import ../../laws/run/entry.bend as RunEntry
import ../run/run_ffi_answers.bend as PRunFfiAnswers
import ./base/recover.bend as LR
import ../../laws/stop/recover.bend as StopRecover

# the entry answers the spelled request with the encoded decision
def ste.wire(+c: Nat, +le: Nat, +re: Nat, +rp: Nat, +w: Nat, +ca: Nat, +p: Nat, +o: Nat, +row: Nat, fit: {StopRecover.think_fits(c, le, re, rp, w, ca, p, o, row) == True{} : Bool}) -> {FRn.ffi(StopRecover.think_ask(c, le, re, rp, w, ca, p, o, row)) == FRn.put_help(RnDecision.decide.recover(RnRecovery.RCfg{c, le, re, rp}, RnDecision.Thought{w, ca, p, o, False{}, False{}}, RnRecovery.Longs{}, row), "") : String}:
  RunEntry.run_ffi_answers(FRn.AskRecover{RnRecovery.RCfg{c, le, re, rp}, RnDecision.Thought{w, ca, p, o, False{}, False{}}, RnRecovery.Longs{}, row}, fit)

def StopRecover.stop_think_entry_follows_the_cap(k, x, le, re, rp, w, c, p, o, fa, fb):
  %Equal.sym(String, FRn.ffi(StopRecover.think_ask(1n+Nat.add(x, k), le, re, rp, w, c, p, o, k)), FRn.put_help(RnDecision.decide.recover(RnRecovery.RCfg{1n+Nat.add(x, k), le, re, rp}, RnDecision.Thought{w, c, p, o, False{}, False{}}, RnRecovery.Longs{}, k), ""), ste.wire(1n+Nat.add(x, k), le, re, rp, w, c, p, o, k, fa)) : {[_, FRn.ffi(StopRecover.think_ask(k, le, re, rp, w, c, p, o, k))] == [Wr.put_nat(1n, Wr.put_nat(1n+k, "")), Wr.put_nat(2n, "")] : List<&2, String>}
  %Equal.sym(String, FRn.ffi(StopRecover.think_ask(k, le, re, rp, w, c, p, o, k)), FRn.put_help(RnDecision.decide.recover(RnRecovery.RCfg{k, le, re, rp}, RnDecision.Thought{w, c, p, o, False{}, False{}}, RnRecovery.Longs{}, k), ""), ste.wire(k, le, re, rp, w, c, p, o, k, fb)) : {[FRn.put_help(RnDecision.decide.recover(RnRecovery.RCfg{1n+Nat.add(x, k), le, re, rp}, RnDecision.Thought{w, c, p, o, False{}, False{}}, RnRecovery.Longs{}, k), ""), _] == [Wr.put_nat(1n, Wr.put_nat(1n+k, "")), Wr.put_nat(2n, "")] : List<&2, String>}
  %Equal.sym(RnDecision.Help, RnDecision.decide.recover(RnRecovery.RCfg{1n+Nat.add(x, k), le, re, rp}, RnDecision.Thought{w, c, p, o, False{}, False{}}, RnRecovery.Longs{}, k), RnDecision.Redoes{1n+k}, LR.str.think_under(x, k, le, re, rp, w, c, p, o, False{})) : {[FRn.put_help(_, ""), FRn.put_help(RnDecision.decide.recover(RnRecovery.RCfg{k, le, re, rp}, RnDecision.Thought{w, c, p, o, False{}, False{}}, RnRecovery.Longs{}, k), "")] == [Wr.put_nat(1n, Wr.put_nat(1n+k, "")), Wr.put_nat(2n, "")] : List<&2, String>}
  %Equal.sym(RnDecision.Help, RnDecision.decide.recover(RnRecovery.RCfg{k, le, re, rp}, RnDecision.Thought{w, c, p, o, False{}, False{}}, RnRecovery.Longs{}, k), RnDecision.Quits{}, LR.str.think_quit(k, le, re, rp, w, c, p, o)) : {[FRn.put_help(RnDecision.Redoes{1n+k}, ""), FRn.put_help(_, "")] == [Wr.put_nat(1n, Wr.put_nat(1n+k, "")), Wr.put_nat(2n, "")] : List<&2, String>}
  {==}
