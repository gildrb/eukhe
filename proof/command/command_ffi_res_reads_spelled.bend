# eukhe: the proof of LAW command_ffi_res_reads_spelled
#
# PROOF of LAW command_ffi_res_reads_spelled: the spelled resolve reply
# is the entry's own encoding (a list of strings is spelled as put_strs
# writes it, LACommandEntry.ce_strs), so the round trip reads it back
# (command_ffi_res_round_trip).

import Base
import ../../bend/ffi_command.bend as FCmd
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../../laws/command/entry.bend as Command
import ./base/entry.bend as LACommandEntry
import ./command_ffi_res_round_trip.bend as PCommandFfiResRoundTrip

def Command.command_ffi_res_reads_spelled(x, rest, h):
  match x:
    case FCmd.RunsW{+p, +a}:
      %LACommandEntry.ce_strs(p, Wr.put_str(a, rest)) : {FCmd.get_res(Wr.put_nat(0n, _)) == Wr.Got{FCmd.RunsW{p, a}, rest} : Wr.Dec<FCmd.ResW>}
      Command.command_ffi_res_round_trip(FCmd.RunsW{p, a}, rest, h)
    case FCmd.OpensW{+p}:
      %LACommandEntry.ce_strs(p, rest) : {FCmd.get_res(Wr.put_nat(1n, _)) == Wr.Got{FCmd.OpensW{p}, rest} : Wr.Dec<FCmd.ResW>}
      Command.command_ffi_res_round_trip(FCmd.OpensW{p}, rest, h)
    case FCmd.UnknownW{+p, +w}:
      %LACommandEntry.ce_strs(p, Wr.put_str(w, rest)) : {FCmd.get_res(Wr.put_nat(2n, _)) == Wr.Got{FCmd.UnknownW{p, w}, rest} : Wr.Dec<FCmd.ResW>}
      Command.command_ffi_res_round_trip(FCmd.UnknownW{p, w}, rest, h)
    case FCmd.NoCmdW{}:
      Command.command_ffi_res_round_trip(FCmd.NoCmdW{}, rest, h)
