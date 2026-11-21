# eukhe: the proof of LAW command_ffi_menu_spells
#
# PROOF of LAW command_ffi_menu_spells: by the menu tag; the places are
# spelled as the entry writes a list of Nats (Wire.wire_nats_spells), the
# path as it writes a list of strings (LACommandEntry.ce_strs).

import Base
import ../../bend/ffi_command.bend as FCmd
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../../laws/command/entry.bend as Command
import ./base/entry.bend as LACommandEntry

def Command.command_ffi_menu_spells(x, rest):
  match x:
    case FCmd.NamesW{}:
      {==}
    case FCmd.KidsW{+p, +xs}:
      %Equal.sym(String, Wr.put_list(~Nat, ~Wr.put_nat, xs, rest), LawsBase.wire_spell_nats(xs, rest), Wire.wire_nats_spells(xs, rest)) : {Wr.put_nat(1n, FCmd.put_strs(p, _)) == Command.cmd_spell_menuw(FCmd.KidsW{p, xs}, rest) : String}
      Equal.cong(String, String, z => Wr.put_nat(1n, z), FCmd.put_strs(p, LawsBase.wire_spell_nats(xs, rest)), LawsBase.wire_spell_strs(p, LawsBase.wire_spell_nats(xs, rest)), LACommandEntry.ce_strs(p, LawsBase.wire_spell_nats(xs, rest)))
    case FCmd.ShutW{}:
      {==}
