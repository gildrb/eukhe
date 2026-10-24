# eukhe: the proof of LAW command_ffi_unknown_row
#
# PROOF of LAW command_ffi_unknown_row: after a table that reads back
# (cfr_table_rt), the key tag 2 and the line read back (wire laws); the
# row tag 2 + n reads as itself or as Bad (ws_nat_read), and both ways
# the row is Bad, so the request is malformed.

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


def cur_bad(b: Bool, -n: Nat, -rest: String) -> {FCmd.get_sel.go(LAWireSpell.ws_nat_answer(b, 2n+n, rest)) == Wr.Bad{} : Wr.Dec<Cmd.Sel>}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def Command.command_ffi_unknown_row(t, l, n, rest, h, hl):
  +z = Wr.put_nat(2n+n, rest)
  +y = Wr.put_str(l, z)
  +x = Wr.put_nat(2n, y)
  %LACommandEntry.ce_table(t, x) : {FCmd.ffi(_) == Wr.err("command: malformed request") : String}
  %Equal.sym(Wr.Dec<List<&2, FCmd.EntW>>, FCmd.get_table(FCmd.put_table(t, x)), Wr.Got{t, x}, PCommandFfiRoundTrip.cfr_table_rt(t, x, h)) : {FCmd.ffi.go(FCmd.get_req.table(_)) == Wr.err("command: malformed request") : String}
  %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(x), Wr.Got{2n, y}, Wire.wire_nat_round_trip(2n, y, {==})) : {FCmd.ffi.go(FCmd.get_req.query(t, FCmd.get_query.go(_))) == Wr.err("command: malformed request") : String}
  %Equal.sym(Wr.Dec<String>, Wr.get_str(y), Wr.Got{l, z}, Wire.wire_str_round_trip(l, z, hl)) : {FCmd.ffi.go(FCmd.get_req.query(t, FCmd.get_query.key(_))) == Wr.err("command: malformed request") : String}
  %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(z), LAWireSpell.ws_nat_answer(LawsBase.wire_fits(2n+n), 2n+n, rest), LAWireSpell.ws_nat_read(2n+n, rest)) : {FCmd.ffi.go(FCmd.get_req.query(t, FCmd.get_query.sel(l, FCmd.get_sel.go(_)))) == Wr.err("command: malformed request") : String}
  %Equal.sym(Wr.Dec<Cmd.Sel>, FCmd.get_sel.go(LAWireSpell.ws_nat_answer(LawsBase.wire_fits(2n+n), 2n+n, rest)), Wr.Bad{}, cur_bad(LawsBase.wire_fits(2n+n), n, rest)) : {FCmd.ffi.go(FCmd.get_req.query(t, FCmd.get_query.sel(l, _))) == Wr.err("command: malformed request") : String}
  {==}
