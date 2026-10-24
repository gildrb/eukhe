# eukhe: the proof of LAW command_ffi_malformed
#
# PROOF of LAW command_ffi_malformed: the entry answers by the reading of
# its input; that reading is Bad, which answers the malformed error.

import Base
import ../../bend/ffi_command.bend as FCmd
import ../../bend/wire.bend as Wr
import ../../laws/command/entry.bend as Command

def Command.command_ffi_malformed(s, bad):
  Equal.cong(Wr.Dec<FCmd.Req>, String, d => FCmd.ffi.go(d), FCmd.get_req(s), Wr.Bad{}, bad)
