# eukhe: the proof of LAW command_ffi_res_round_trip
#
# PROOF of LAW command_ffi_res_round_trip: a resolve reply is its tag
# (a Nat), then its path (a list of strings, cfr_strs_rt) and its text (a
# string); each fits, so each reads back by the wire laws, leaving rest.

import Base
import ../../bend/ffi_command.bend as FCmd
import ../../bend/wire.bend as Wr
import ../../laws/command.bend as Command
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../base/bool/and.bend as LBoolAnd
import ../base/wire.bend as LWire
import ./base.bend as LA

def Command.command_ffi_res_round_trip(x, rest, h):
  match x:
    case FCmd.RunsW{+p, +a}:
      +hh = h
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(0n, FCmd.put_strs(p, Wr.put_str(a, rest)))), Wr.Got{0n, FCmd.put_strs(p, Wr.put_str(a, rest))}, Wire.wire_nat_round_trip(0n, FCmd.put_strs(p, Wr.put_str(a, rest)), {==})) : {FCmd.get_res.go(_) == Wr.Got{FCmd.RunsW{p, a}, rest} : Wr.Dec<FCmd.ResW>}
      %Equal.sym(Wr.Dec<List<&2, String>>, FCmd.get_strs(FCmd.put_strs(p, Wr.put_str(a, rest))), Wr.Got{p, Wr.put_str(a, rest)}, LA.cfr_strs_rt(p, Wr.put_str(a, rest), LBoolAnd.wr_and_l(Command.cmd_strs_fit(p), LawsBase.wire_fits(String.length(a)), hh))) : {FCmd.get_res.runs(_) == Wr.Got{FCmd.RunsW{p, a}, rest} : Wr.Dec<FCmd.ResW>}
      %Equal.sym(Wr.Dec<String>, Wr.get_str(Wr.put_str(a, rest)), Wr.Got{a, rest}, Wire.wire_str_round_trip(a, rest, LBoolAnd.wr_and_r(Command.cmd_strs_fit(p), LawsBase.wire_fits(String.length(a)), hh))) : {FCmd.get_res.runs.args(p, _) == Wr.Got{FCmd.RunsW{p, a}, rest} : Wr.Dec<FCmd.ResW>}
      {==}
    case FCmd.OpensW{+p}:
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(1n, FCmd.put_strs(p, rest))), Wr.Got{1n, FCmd.put_strs(p, rest)}, Wire.wire_nat_round_trip(1n, FCmd.put_strs(p, rest), {==})) : {FCmd.get_res.go(_) == Wr.Got{FCmd.OpensW{p}, rest} : Wr.Dec<FCmd.ResW>}
      %Equal.sym(Wr.Dec<List<&2, String>>, FCmd.get_strs(FCmd.put_strs(p, rest)), Wr.Got{p, rest}, LA.cfr_strs_rt(p, rest, h)) : {FCmd.get_res.opens(_) == Wr.Got{FCmd.OpensW{p}, rest} : Wr.Dec<FCmd.ResW>}
      {==}
    case FCmd.UnknownW{+p, +w}:
      +hh = h
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(2n, FCmd.put_strs(p, Wr.put_str(w, rest)))), Wr.Got{2n, FCmd.put_strs(p, Wr.put_str(w, rest))}, Wire.wire_nat_round_trip(2n, FCmd.put_strs(p, Wr.put_str(w, rest)), {==})) : {FCmd.get_res.go(_) == Wr.Got{FCmd.UnknownW{p, w}, rest} : Wr.Dec<FCmd.ResW>}
      %Equal.sym(Wr.Dec<List<&2, String>>, FCmd.get_strs(FCmd.put_strs(p, Wr.put_str(w, rest))), Wr.Got{p, Wr.put_str(w, rest)}, LA.cfr_strs_rt(p, Wr.put_str(w, rest), LBoolAnd.wr_and_l(Command.cmd_strs_fit(p), LawsBase.wire_fits(String.length(w)), hh))) : {FCmd.get_res.unknown(_) == Wr.Got{FCmd.UnknownW{p, w}, rest} : Wr.Dec<FCmd.ResW>}
      %Equal.sym(Wr.Dec<String>, Wr.get_str(Wr.put_str(w, rest)), Wr.Got{w, rest}, Wire.wire_str_round_trip(w, rest, LBoolAnd.wr_and_r(Command.cmd_strs_fit(p), LawsBase.wire_fits(String.length(w)), hh))) : {FCmd.get_res.unknown.word(p, _) == Wr.Got{FCmd.UnknownW{p, w}, rest} : Wr.Dec<FCmd.ResW>}
      {==}
    case FCmd.NoCmdW{}:
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(3n, rest)), Wr.Got{3n, rest}, Wire.wire_nat_round_trip(3n, rest, {==})) : {FCmd.get_res.go(_) == Wr.Got{FCmd.NoCmdW{}, rest} : Wr.Dec<FCmd.ResW>}
      {==}
