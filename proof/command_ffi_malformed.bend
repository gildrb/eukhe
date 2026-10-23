# PROOF of LAW command_ffi_malformed: the entry answers by the reading of
# its input; that reading is Bad, which answers the malformed error.

import Base
import ../LAWS.bend as Laws
import ../bend/ffi_command.bend as FCmd
import ../bend/wire.bend as Wr

def Laws.command_ffi_malformed(s, bad):
  Equal.cong(Wr.Dec<FCmd.Req>, String, d => FCmd.ffi.go(d), FCmd.get_req(s), Wr.Bad{}, bad)
