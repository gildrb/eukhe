# PROOF of LAW command_ffi_res_round_trip: a resolve reply is its tag
# (a Nat), then its path (a list of strings, cfr_strs_rt) and its text (a
# string); each fits, so each reads back by the wire laws, leaving rest.

import Base
import ../LAWS.bend as Laws
import ../bend/ffi_command.bend as FCmd
import ../bend/wire.bend as Wr
import ./wire.bend as PWire
import ./command_ffi_round_trip.bend as CFR

def Laws.command_ffi_res_round_trip(x, rest, h):
  match x:
    case FCmd.RunsW{+p, +a}:
      +hh = h
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(0n, FCmd.put_strs(p, Wr.put_str(a, rest)))), Wr.Got{0n, FCmd.put_strs(p, Wr.put_str(a, rest))}, Laws.wire_nat_round_trip(0n, FCmd.put_strs(p, Wr.put_str(a, rest)), {==})) : {FCmd.get_res.go(_) == Wr.Got{FCmd.RunsW{p, a}, rest} : Wr.Dec<FCmd.ResW>}
      %Equal.sym(Wr.Dec<List<&2, String>>, FCmd.get_strs(FCmd.put_strs(p, Wr.put_str(a, rest))), Wr.Got{p, Wr.put_str(a, rest)}, CFR.cfr_strs_rt(p, Wr.put_str(a, rest), PWire.wr_and_l(Laws.cmd_strs_fit(p), Laws.wire_fits(String.length(a)), hh))) : {FCmd.get_res.runs(_) == Wr.Got{FCmd.RunsW{p, a}, rest} : Wr.Dec<FCmd.ResW>}
      %Equal.sym(Wr.Dec<String>, Wr.get_str(Wr.put_str(a, rest)), Wr.Got{a, rest}, Laws.wire_str_round_trip(a, rest, PWire.wr_and_r(Laws.cmd_strs_fit(p), Laws.wire_fits(String.length(a)), hh))) : {FCmd.get_res.runs.args(p, _) == Wr.Got{FCmd.RunsW{p, a}, rest} : Wr.Dec<FCmd.ResW>}
      {==}
    case FCmd.OpensW{+p}:
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(1n, FCmd.put_strs(p, rest))), Wr.Got{1n, FCmd.put_strs(p, rest)}, Laws.wire_nat_round_trip(1n, FCmd.put_strs(p, rest), {==})) : {FCmd.get_res.go(_) == Wr.Got{FCmd.OpensW{p}, rest} : Wr.Dec<FCmd.ResW>}
      %Equal.sym(Wr.Dec<List<&2, String>>, FCmd.get_strs(FCmd.put_strs(p, rest)), Wr.Got{p, rest}, CFR.cfr_strs_rt(p, rest, h)) : {FCmd.get_res.opens(_) == Wr.Got{FCmd.OpensW{p}, rest} : Wr.Dec<FCmd.ResW>}
      {==}
    case FCmd.UnknownW{+p, +w}:
      +hh = h
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(2n, FCmd.put_strs(p, Wr.put_str(w, rest)))), Wr.Got{2n, FCmd.put_strs(p, Wr.put_str(w, rest))}, Laws.wire_nat_round_trip(2n, FCmd.put_strs(p, Wr.put_str(w, rest)), {==})) : {FCmd.get_res.go(_) == Wr.Got{FCmd.UnknownW{p, w}, rest} : Wr.Dec<FCmd.ResW>}
      %Equal.sym(Wr.Dec<List<&2, String>>, FCmd.get_strs(FCmd.put_strs(p, Wr.put_str(w, rest))), Wr.Got{p, Wr.put_str(w, rest)}, CFR.cfr_strs_rt(p, Wr.put_str(w, rest), PWire.wr_and_l(Laws.cmd_strs_fit(p), Laws.wire_fits(String.length(w)), hh))) : {FCmd.get_res.unknown(_) == Wr.Got{FCmd.UnknownW{p, w}, rest} : Wr.Dec<FCmd.ResW>}
      %Equal.sym(Wr.Dec<String>, Wr.get_str(Wr.put_str(w, rest)), Wr.Got{w, rest}, Laws.wire_str_round_trip(w, rest, PWire.wr_and_r(Laws.cmd_strs_fit(p), Laws.wire_fits(String.length(w)), hh))) : {FCmd.get_res.unknown.word(p, _) == Wr.Got{FCmd.UnknownW{p, w}, rest} : Wr.Dec<FCmd.ResW>}
      {==}
    case FCmd.NoCmdW{}:
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(3n, rest)), Wr.Got{3n, rest}, Laws.wire_nat_round_trip(3n, rest, {==})) : {FCmd.get_res.go(_) == Wr.Got{FCmd.NoCmdW{}, rest} : Wr.Dec<FCmd.ResW>}
      {==}
