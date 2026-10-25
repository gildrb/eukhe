# eukhe: the proof of LAW command_ffi_menu_reads_spelled
#
# PROOF of LAW command_ffi_menu_reads_spelled: the spelled menu reply is
# the entry's own encoding (lists of strings and of Nats are spelled as
# the entry writes them: LACommandEntry.ce_strs, Wire.wire_nats_spells),
# so the round trip reads it back (command_ffi_menu_round_trip).

import Base
import ../../bend/ffi_command.bend as FCmd
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../../laws/command/entry.bend as Command
import ./base/entry.bend as LACommandEntry
import ./command_ffi_menu_round_trip.bend as PCommandFfiMenuRoundTrip

def Command.command_ffi_menu_reads_spelled(x, rest, h):
  match x:
    case FCmd.NamesW{}:
      Command.command_ffi_menu_round_trip(FCmd.NamesW{}, rest, h)
    case FCmd.KidsW{+p, +xs}:
      %Wire.wire_nats_spells(xs, rest) : {FCmd.get_menu(Wr.put_nat(1n, LawsBase.wire_spell_strs(p, _))) == Wr.Got{FCmd.KidsW{p, xs}, rest} : Wr.Dec<FCmd.MenuW>}
      %LACommandEntry.ce_strs(p, Wr.put_list(~Nat, ~Wr.put_nat, xs, rest)) : {FCmd.get_menu(Wr.put_nat(1n, _)) == Wr.Got{FCmd.KidsW{p, xs}, rest} : Wr.Dec<FCmd.MenuW>}
      Command.command_ffi_menu_round_trip(FCmd.KidsW{p, xs}, rest, h)
    case FCmd.ShutW{}:
      Command.command_ffi_menu_round_trip(FCmd.ShutW{}, rest, h)
