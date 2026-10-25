# eukhe: the proof of LAW gateway_backoff_entry_refuses
#
# PROOF: the entry answers either a wait, a Nat (never 'E':
# wire_nat_not_err), or the one error form; so an answer that opens with
# 'E' is that error form.

import Base
import ../../bend/gateway_backoff.bend as Gb
import ../../bend/ffi_gateway_backoff.bend as FGb
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/gateway_backoff.bend as GatewayBackoff
import ../../laws/wire.bend as Wire
import ../wire/wire_nat_not_err.bend as PWireNatNotErr
import ../base/staging.bend as LStg

def gbf.refuse(d: Wr.Dec<Maybe<&2, Nat>>, bad: {LawsBase.wire_opens_err(FGb.ffi.got(d)) == True{} : Bool}) -> {FGb.ffi.got(d) == Wr.err("gateway_backoff: malformed request") : String}:
  match d:
    case Wr.Got{+m, rest}:
      match rest:
        case SNil{}:
          LStg.stg.absurd({Wr.put_nat(Gb.next(m), "") == Wr.err("gateway_backoff: malformed request") : String}, Equal.trans(Bool, True{}, LawsBase.wire_opens_err(Wr.put_nat(Gb.next(m), "")), False{}, Equal.sym(Bool, LawsBase.wire_opens_err(Wr.put_nat(Gb.next(m), "")), True{}, bad), Wire.wire_nat_not_err(Gb.next(m), "")))
        case SCon{x, y}:
          {==}
    case Wr.Bad{}:
      {==}

def GatewayBackoff.gateway_backoff_entry_refuses(s, bad):
  gbf.refuse(FGb.get_req(s), bad)
