# eukhe: the proof of LAW command_ffi_menu_round_trip
#
# PROOF of LAW command_ffi_menu_round_trip: a menu reply is its tag (a
# Nat), then for the children their path (a list of strings, cfr_strs_rt)
# and their places (a list of Nats, wire_list_round_trip); each fits, so
# each reads back, leaving rest.

import Base
import ../../bend/ffi_command.bend as FCmd
import ../../bend/wire.bend as Wr
import ../../laws/command.bend as Command
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../base/bool/and.bend as LBoolAnd
import ../base/wire.bend as LWire
import ./base.bend as LA

def Command.command_ffi_menu_round_trip(x, rest, h):
  match x:
    case FCmd.NamesW{}:
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(0n, rest)), Wr.Got{0n, rest}, Wire.wire_nat_round_trip(0n, rest, {==})) : {FCmd.get_menu.go(_) == Wr.Got{FCmd.NamesW{}, rest} : Wr.Dec<FCmd.MenuW>}
      {==}
    case FCmd.KidsW{+p, +xs}:
      +hh = h
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(1n, FCmd.put_strs(p, Wr.put_list(~Nat, ~Wr.put_nat, xs, rest)))), Wr.Got{1n, FCmd.put_strs(p, Wr.put_list(~Nat, ~Wr.put_nat, xs, rest))}, Wire.wire_nat_round_trip(1n, FCmd.put_strs(p, Wr.put_list(~Nat, ~Wr.put_nat, xs, rest)), {==})) : {FCmd.get_menu.go(_) == Wr.Got{FCmd.KidsW{p, xs}, rest} : Wr.Dec<FCmd.MenuW>}
      %Equal.sym(Wr.Dec<List<&2, String>>, FCmd.get_strs(FCmd.put_strs(p, Wr.put_list(~Nat, ~Wr.put_nat, xs, rest))), Wr.Got{p, Wr.put_list(~Nat, ~Wr.put_nat, xs, rest)}, LA.cfr_strs_rt(p, Wr.put_list(~Nat, ~Wr.put_nat, xs, rest), LBoolAnd.wr_and_l(Command.cmd_strs_fit(p), Bool.and(LawsBase.wire_fits(List.length(&2, Nat, xs)), LawsBase.wire_nats_fit(xs)), hh))) : {FCmd.get_menu.kids(_) == Wr.Got{FCmd.KidsW{p, xs}, rest} : Wr.Dec<FCmd.MenuW>}
      %Equal.sym(Wr.Dec<List<&2, Nat>>, Wr.get_list(~Nat, ~Wr.get_nat, Wr.put_list(~Nat, ~Wr.put_nat, xs, rest)), Wr.Got{xs, rest}, Wire.wire_list_round_trip(xs, rest, LBoolAnd.wr_and_r(Command.cmd_strs_fit(p), Bool.and(LawsBase.wire_fits(List.length(&2, Nat, xs)), LawsBase.wire_nats_fit(xs)), hh))) : {FCmd.get_menu.items(p, _) == Wr.Got{FCmd.KidsW{p, xs}, rest} : Wr.Dec<FCmd.MenuW>}
      {==}
    case FCmd.ShutW{}:
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(2n, rest)), Wr.Got{2n, rest}, Wire.wire_nat_round_trip(2n, rest, {==})) : {FCmd.get_menu.go(_) == Wr.Got{FCmd.ShutW{}, rest} : Wr.Dec<FCmd.MenuW>}
      {==}
