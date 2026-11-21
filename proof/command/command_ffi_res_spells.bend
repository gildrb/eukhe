# eukhe: the proof of LAW command_ffi_res_spells
#
# PROOF of LAW command_ffi_res_spells: by the reply tag; a path is spelled
# as the entry writes a list of strings (LACommandEntry.ce_strs), the rest
# is the same wire primitives.

import Base
import ../../bend/ffi_command.bend as FCmd
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/command/entry.bend as Command
import ./base/entry.bend as LACommandEntry

def Command.command_ffi_res_spells(x, rest):
  match x:
    case FCmd.RunsW{+p, +a}:
      Equal.cong(String, String, z => Wr.put_nat(0n, z), FCmd.put_strs(p, Wr.put_str(a, rest)), LawsBase.wire_spell_strs(p, Wr.put_str(a, rest)), LACommandEntry.ce_strs(p, Wr.put_str(a, rest)))
    case FCmd.OpensW{+p}:
      Equal.cong(String, String, z => Wr.put_nat(1n, z), FCmd.put_strs(p, rest), LawsBase.wire_spell_strs(p, rest), LACommandEntry.ce_strs(p, rest))
    case FCmd.UnknownW{+p, +w}:
      Equal.cong(String, String, z => Wr.put_nat(2n, z), FCmd.put_strs(p, Wr.put_str(w, rest)), LawsBase.wire_spell_strs(p, Wr.put_str(w, rest)), LACommandEntry.ce_strs(p, Wr.put_str(w, rest)))
    case FCmd.NoCmdW{}:
      {==}
