# eukhe: the proof of LAW command_ffi_left_over
#
# PROOF of LAW command_ffi_left_over: the encoding of a request that fits
# reads back as the request with rest left (command_ffi_round_trip); rest
# is not empty, so the entry answers the left-over error.

import Base
import ../../bend/wire.bend as Wr
import ../../bend/ffi_command.bend as FCmd
import ../../LAWS.bend as Laws
import ./command_ffi_round_trip.bend as PCommandFfiRoundTrip

def Laws.command_ffi_left_over(r, rest, h, more):
  %Equal.sym(Wr.Dec<FCmd.Req>, FCmd.get_req(FCmd.put_req(r, rest)), Wr.Got{r, rest}, Laws.command_ffi_round_trip(r, rest, h)) : {FCmd.ffi.go(_) == Wr.err("command: input left over") : String}
  %Equal.sym(Bool, String.is_empty(rest), False{}, more) : {FCmd.ffi.whole(r, _) == Wr.err("command: input left over") : String}
  {==}
