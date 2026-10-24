# eukhe: the proof of LAW command_ffi_unknown_query
#
# PROOF of LAW command_ffi_unknown_query: after a table that reads back
# (cfr_table_rt), the question tag 3 + n reads as itself when it fits
# and as Bad when too long (ws_nat_read); both ways the question is Bad,
# so the request is malformed.

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


def cuq_bad(b: Bool, -n: Nat, -rest: String) -> {FCmd.get_query.go(LAWireSpell.ws_nat_answer(b, 3n+n, rest)) == Wr.Bad{} : Wr.Dec<FCmd.Query>}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def Command.command_ffi_unknown_query(t, n, rest, h):
  +x = Wr.put_nat(3n+n, rest)
  %LACommandEntry.ce_table(t, x) : {FCmd.ffi(_) == Wr.err("command: malformed request") : String}
  %Equal.sym(Wr.Dec<List<&2, FCmd.EntW>>, FCmd.get_table(FCmd.put_table(t, x)), Wr.Got{t, x}, PCommandFfiRoundTrip.cfr_table_rt(t, x, h)) : {FCmd.ffi.go(FCmd.get_req.table(_)) == Wr.err("command: malformed request") : String}
  %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(x), LAWireSpell.ws_nat_answer(LawsBase.wire_fits(3n+n), 3n+n, rest), LAWireSpell.ws_nat_read(3n+n, rest)) : {FCmd.ffi.go(FCmd.get_req.query(t, FCmd.get_query.go(_))) == Wr.err("command: malformed request") : String}
  %Equal.sym(Wr.Dec<FCmd.Query>, FCmd.get_query.go(LAWireSpell.ws_nat_answer(LawsBase.wire_fits(3n+n), 3n+n, rest)), Wr.Bad{}, cuq_bad(LawsBase.wire_fits(3n+n), n, rest)) : {FCmd.ffi.go(FCmd.get_req.query(t, _)) == Wr.err("command: malformed request") : String}
  {==}
