# eukhe: the proof of LAW gateway_commands_entry_req_exact
#
# PROOF: the decoder stages of gateway_commands_entry_exact (gcx.text)
# show that whatever get_req decodes is the spelling of a request that
# fits, then its rest; h names what it decoded.

import Base
import ../../bend/ffi_gateway_commands.bend as FGc
import ../../bend/wire.bend as Wr
import ../../laws/gateway_commands.bend as GatewayCommands
import ../base/wire_dec.bend as LE
import ./gateway_commands_entry_exact.bend as PGcx

def GatewayCommands.gateway_commands_entry_req_exact(s, q, rest, h):
  %h : PGcx.gcx.RP(s, _)
  PGcx.gcx.text(s, Wr.get_str(s), LE.dcw.str(s))
