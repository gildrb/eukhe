# eukhe: the proof of LAW command_ffi_out_reads_spelled
#
# PROOF of LAW command_ffi_out_reads_spelled: the spelled key reply is
# the entry's own encoding, so the round trip reads it back
# (command_ffi_out_round_trip).

import Base
import ../../bend/ffi_command.bend as FCmd
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../../laws/command/entry.bend as Command
import ./base/entry.bend as LACommandEntry
import ./command_ffi_out_round_trip.bend as PCommandFfiOutRoundTrip

def Command.command_ffi_out_reads_spelled(x, rest, h):
  match x:
    case FCmd.OutW{+l, +a, +b}:
      Command.command_ffi_out_round_trip(FCmd.OutW{l, a, b}, rest, h)
