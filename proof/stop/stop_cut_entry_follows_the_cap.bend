# eukhe: the proof of LAW stop_cut_entry_follows_the_cap
#
# PROOF: each spelled request is the entry's encoding of its recover request, which fits the wire, so the entry answers the encoded decision (run_ffi_answers); under the cap the decision is the next note (LR.str.cut_under), at it the failure (LR.str.cut_quit).

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
def sce.wire(+c: Nat, +le: Nat, +re: Nat, +rp: Nat, +row: Nat, fit: {StopRecover.cut_fits(c, le, re, rp, row) == True{} : Bool}) -> {FRn.ffi(StopRecover.cut_ask(c, le, re, rp, row)) == FRn.put_help(RnDecision.decide.recover(RnRecovery.RCfg{c, le, re, rp}, RnDecision.Truncated{}, RnRecovery.Longs{}, row), "") : String}:
  RunEntry.run_ffi_answers(FRn.AskRecover{RnRecovery.RCfg{c, le, re, rp}, RnDecision.Truncated{}, RnRecovery.Longs{}, row}, fit)

def StopRecover.stop_cut_entry_follows_the_cap(k, x, le, re, rp, fa, fb):
  %Equal.sym(String, FRn.ffi(StopRecover.cut_ask(1n+Nat.add(x, k), le, re, rp, k)), FRn.put_help(RnDecision.decide.recover(RnRecovery.RCfg{1n+Nat.add(x, k), le, re, rp}, RnDecision.Truncated{}, RnRecovery.Longs{}, k), ""), sce.wire(1n+Nat.add(x, k), le, re, rp, k, fa)) : {[_, FRn.ffi(StopRecover.cut_ask(k, le, re, rp, k))] == [Wr.put_nat(1n, Wr.put_nat(1n+k, "")), Wr.put_nat(2n, "")] : List<&2, String>}
  %Equal.sym(String, FRn.ffi(StopRecover.cut_ask(k, le, re, rp, k)), FRn.put_help(RnDecision.decide.recover(RnRecovery.RCfg{k, le, re, rp}, RnDecision.Truncated{}, RnRecovery.Longs{}, k), ""), sce.wire(k, le, re, rp, k, fb)) : {[FRn.put_help(RnDecision.decide.recover(RnRecovery.RCfg{1n+Nat.add(x, k), le, re, rp}, RnDecision.Truncated{}, RnRecovery.Longs{}, k), ""), _] == [Wr.put_nat(1n, Wr.put_nat(1n+k, "")), Wr.put_nat(2n, "")] : List<&2, String>}
  %Equal.sym(RnDecision.Help, RnDecision.decide.recover(RnRecovery.RCfg{1n+Nat.add(x, k), le, re, rp}, RnDecision.Truncated{}, RnRecovery.Longs{}, k), RnDecision.Redoes{1n+k}, LR.str.cut_under(x, k, le, re, rp)) : {[FRn.put_help(_, ""), FRn.put_help(RnDecision.decide.recover(RnRecovery.RCfg{k, le, re, rp}, RnDecision.Truncated{}, RnRecovery.Longs{}, k), "")] == [Wr.put_nat(1n, Wr.put_nat(1n+k, "")), Wr.put_nat(2n, "")] : List<&2, String>}
  %Equal.sym(RnDecision.Help, RnDecision.decide.recover(RnRecovery.RCfg{k, le, re, rp}, RnDecision.Truncated{}, RnRecovery.Longs{}, k), RnDecision.Quits{}, LR.str.cut_quit(k, le, re, rp)) : {[FRn.put_help(RnDecision.Redoes{1n+k}, ""), FRn.put_help(_, "")] == [Wr.put_nat(1n, Wr.put_nat(1n+k, "")), Wr.put_nat(2n, "")] : List<&2, String>}
  {==}
