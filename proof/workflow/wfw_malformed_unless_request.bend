# eukhe: the proof of LAW wfw_malformed_unless_request
#
# PROOF: the decoder reads only spelled requests that fit, the rest after
# them untouched (wc.req of wfw_reads_only_requests); when it reads none
# the entry answers the malformed error, which the premise excludes.

import Base
import ../../bend/ffi_workflow.bend as FW
import ../../bend/wire.bend as Wr
import ../../laws/workflow/model.bend as Workflow
import ../wire/base/spell.bend as LAWireSpell
import ./wfw_reads_only_requests.bend as PWfwReadsOnlyRequests

def wmu.goal(+s: String) -> Type:
  &q: FW.Req -> &rest: String -> {(s, Workflow.wfw_req_fits(q)) == (Workflow.wfw_spell_req(q, rest), True{}) : String & Bool}

def wmu.eq(+s: String, +q: FW.Req, +rest: String, e1: {s == Workflow.wfw_spell_req(q, rest) : String}, e2: {Workflow.wfw_req_fits(q) == True{} : Bool}) -> {(s, Workflow.wfw_req_fits(q)) == (Workflow.wfw_spell_req(q, rest), True{}) : String & Bool}:
  %Equal.sym(String, s, Workflow.wfw_spell_req(q, rest), e1) : {(_, Workflow.wfw_req_fits(q)) == (Workflow.wfw_spell_req(q, rest), True{}) : String & Bool}
  %Equal.sym(Bool, Workflow.wfw_req_fits(q), True{}, e2) : {(Workflow.wfw_spell_req(q, rest), _) == (Workflow.wfw_spell_req(q, rest), True{}) : String & Bool}
  {==}

def wmu.main(+s: String, d: Wr.Dec<FW.Req>, inv: PWfwReadsOnlyRequests.wc.Req(s, d), other: {String.eq(FW.ffi.go(d), Wr.err("workflow: malformed request")) == False{} : Bool}) -> wmu.goal(s):
  match d:
    case Wr.Got{+q, +rest}:
      (e1, e2) = inv
      (q, (rest, wmu.eq(s, q, rest, e1, e2)))
    case Wr.Bad{}:
      LAWireSpell.ws_absurd(wmu.goal(s), other)

def Workflow.wfw_malformed_unless_request(s, other):
  wmu.main(s, FW.get_req(s), PWfwReadsOnlyRequests.wc.req(s), other)
