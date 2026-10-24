# eukhe: the proof of LAW command_ffi_unknown_press
#
# PROOF of LAW command_ffi_unknown_press: after a table that reads back
# (cfr_table_rt), the key tag 2, the line and the row read back (wire
# laws, cfr_sel_rt); the key tag 2 + n reads as itself or as Bad
# (ws_nat_read), and both ways the key is Bad, so the request is malformed.

import Base
import ../../bend/command.bend as Cmd
import ../../bend/ffi_command.bend as FCmd
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../../laws/command/entry.bend as Command
import ../wire/base/spell.bend as LAWireSpell
import ./base/entry.bend as LACommandEntry
import ../base/logic/bool.bend as LLogicBool
import ../base/wire.bend as LWire
import ./command_ffi_round_trip.bend as PCommandFfiRoundTrip


def cup_bad(b: Bool, -n: Nat, -rest: String) -> {FCmd.get_press.go(LAWireSpell.ws_nat_answer(b, 2n+n, rest)) == Wr.Bad{} : Wr.Dec<Cmd.Press>}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def Command.command_ffi_unknown_press(t, l, x, n, rest, h, hl):
  +hh = hl
  +w = Wr.put_nat(2n+n, rest)
  +z = Command.cmd_spell_sel(x, w)
  +y = Wr.put_str(l, z)
  +v = Wr.put_nat(2n, y)
  %LACommandEntry.ce_table(t, v) : {FCmd.ffi(_) == Wr.err("command: malformed request") : String}
  %Equal.sym(Wr.Dec<List<&2, FCmd.EntW>>, FCmd.get_table(FCmd.put_table(t, v)), Wr.Got{t, v}, PCommandFfiRoundTrip.cfr_table_rt(t, v, h)) : {FCmd.ffi.go(FCmd.get_req.table(_)) == Wr.err("command: malformed request") : String}
  %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(v), Wr.Got{2n, y}, Wire.wire_nat_round_trip(2n, y, {==})) : {FCmd.ffi.go(FCmd.get_req.query(t, FCmd.get_query.go(_))) == Wr.err("command: malformed request") : String}
  %Equal.sym(Wr.Dec<String>, Wr.get_str(y), Wr.Got{l, z}, Wire.wire_str_round_trip(l, z, LLogicBool.wr_and_l(LawsBase.wire_fits(String.length(l)), Command.cmd_sel_fits(x), hh))) : {FCmd.ffi.go(FCmd.get_req.query(t, FCmd.get_query.key(_))) == Wr.err("command: malformed request") : String}
  %LACommandEntry.ce_sel(x, w) : {FCmd.ffi.go(FCmd.get_req.query(t, FCmd.get_query.sel(l, FCmd.get_sel(_)))) == Wr.err("command: malformed request") : String}
  %Equal.sym(Wr.Dec<Cmd.Sel>, FCmd.get_sel(FCmd.put_sel(x, w)), Wr.Got{x, w}, PCommandFfiRoundTrip.cfr_sel_rt(x, w, LLogicBool.wr_and_r(LawsBase.wire_fits(String.length(l)), Command.cmd_sel_fits(x), hh))) : {FCmd.ffi.go(FCmd.get_req.query(t, FCmd.get_query.sel(l, _))) == Wr.err("command: malformed request") : String}
  %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(w), LAWireSpell.ws_nat_answer(LawsBase.wire_fits(2n+n), 2n+n, rest), LAWireSpell.ws_nat_read(2n+n, rest)) : {FCmd.ffi.go(FCmd.get_req.query(t, FCmd.get_query.press(l, x, FCmd.get_press.go(_)))) == Wr.err("command: malformed request") : String}
  %Equal.sym(Wr.Dec<Cmd.Press>, FCmd.get_press.go(LAWireSpell.ws_nat_answer(LawsBase.wire_fits(2n+n), 2n+n, rest)), Wr.Bad{}, cup_bad(LawsBase.wire_fits(2n+n), n, rest)) : {FCmd.ffi.go(FCmd.get_req.query(t, FCmd.get_query.press(l, x, _))) == Wr.err("command: malformed request") : String}
  {==}
