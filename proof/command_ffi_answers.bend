# PROOF of LAW command_ffi_answers: the encoding of a request that fits
# reads back as the request with nothing left (command_ffi_round_trip with
# rest ""), so the entry finds its input whole and runs the model on it.

import Base
import ../LAWS.bend as Laws
import ../bend/ffi_command.bend as FCmd
import ../bend/wire.bend as Wr
import ./command_ffi_round_trip.bend as CFR

def Laws.command_ffi_answers(r, h):
  Equal.cong(Wr.Dec<FCmd.Req>, String, d => FCmd.ffi.go(d), FCmd.get_req(FCmd.put_req(r, "")), Wr.Got{r, ""}, Laws.command_ffi_round_trip(r, "", h))
