# eukhe: the proof of LAW gateway_backoff_entry_answers
#
# PROOF: the spelled request reads back whole with nothing left
# (gateway_backoff_entry_reads), so the entry answers the code's wait,
# which is the spec's (gateway_backoff_spec).

import Base
import ../../bend/gateway_backoff.bend as Gb
import ../../bend/ffi_gateway_backoff.bend as FGb
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/gateway_backoff.bend as GatewayBackoff
import ./gateway_backoff_spec.bend as PGatewayBackoffSpec
import ./gateway_backoff_entry_reads.bend as PGatewayBackoffEntryReads

def GatewayBackoff.gateway_backoff_entry_answers(m, h):
  %Equal.sym(Wr.Dec<Maybe<&2, Nat>>, FGb.get_req(GatewayBackoff.gb_w_req(m, "")), Wr.Got{m, ""}, GatewayBackoff.gateway_backoff_entry_reads(m, "", h)) : {FGb.ffi.got(_) == Wr.put_nat(GatewayBackoff.gb_wait(m), "") : String}
  %GatewayBackoff.gateway_backoff_spec(m) : {Wr.put_nat(Gb.next(m), "") == Wr.put_nat(_, "") : String}
  {==}
