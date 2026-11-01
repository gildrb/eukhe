# eukhe: the proof of LAW wait_any_entry_malformed_exact
#
# PROOF: the entry reads every input as the laws' reader does (wa.req); where that reader finds no whole request (it fails, or input is left over), the entry answers its error form, and a request read whole contradicts the premise.

import Base
import ../../bend/wait_any.bend as Wa
import ../../spec/durable/wait_any.bend as WaSpec
import ../../laws/wait_any.bend as WaitAny
import ./base.bend as LW
import ../../bend/ffi_wait_any.bend as FWa
import ../../bend/wire.bend as Wr
import ../../spec/durable/wait_any_wire.bend as SpW

def wa.MI(m: Maybe<&2, FWa.Req>, G: Type) -> Type:
  match m:
    case None{}:
      G
    case Some{x}:
      Unit

def wa.some_none(-x: FWa.Req, -G: Type, e: {Some{x} == None{} : Maybe<&2, FWa.Req>}) -> G:
  %e : wa.MI(_, G)
  Unit{}

def wa.end(e: Bool, -q: FWa.Req, no: {SpW.r_whole.end(e, q) == None{} : Maybe<&2, FWa.Req>}) -> {FWa.ffi.done(q, e) == Wr.err("wait_any: malformed request") : String}:
  match e:
    case True{}:
      wa.some_none(q, {FWa.answer(q) == Wr.err("wait_any: malformed request") : String}, no)
    case False{}:
      {==}

def wa.whole(r: Wr.Dec<FWa.Req>, no: {SpW.r_whole(r) == None{} : Maybe<&2, FWa.Req>}) -> {FWa.ffi.got(r) == Wr.err("wait_any: malformed request") : String}:
  match r:
    case Wr.Got{q, +s}:
      wa.end(Wr.end(s), q, no)
    case Wr.Bad{}:
      {==}

def WaitAny.wait_any_entry_malformed_exact(s, no):
  %Equal.sym(Wr.Dec<FWa.Req>, FWa.get_req(s), SpW.r_req(s), LW.wa.req(s)) : {FWa.ffi.got(_) == Wr.err("wait_any: malformed request") : String}
  wa.whole(SpW.r_req(s), no)
