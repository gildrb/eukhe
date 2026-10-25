# eukhe: the proof of LAW worker_ffi_malformed_unless_request
#
# PROOF of LAW worker_ffi_malformed_unless_request: the decoder reads only
# spelled requests that fit, the rest after them untouched (ci_req_all of
# proof/worker/base/reads.bend); when it reads none the entry answers the
# malformed error, which the premise excludes.

import Base
import ../../bend/ffi_worker.bend as FWk
import ../../bend/wire.bend as Wr
import ../../laws/worker.bend as Worker
import ../wire/base/spell.bend as LAWireSpell
import ./base/reads.bend as LAWorkerReads

def wmu_goal(+s: String) -> Type:
  &r: FWk.Req -> &rest: String -> {(s, Worker.wk_req_fits(r)) == (Worker.wk_spell_req(r, rest), True{}) : String & Bool}

def wmu_eq(+s: String, +r: FWk.Req, +rest: String, e1: {s == Worker.wk_spell_req(r, rest) : String}, e2: {Worker.wk_req_fits(r) == True{} : Bool}) -> {(s, Worker.wk_req_fits(r)) == (Worker.wk_spell_req(r, rest), True{}) : String & Bool}:
  %Equal.sym(String, s, Worker.wk_spell_req(r, rest), e1) : {(_, Worker.wk_req_fits(r)) == (Worker.wk_spell_req(r, rest), True{}) : String & Bool}
  %Equal.sym(Bool, Worker.wk_req_fits(r), True{}, e2) : {(Worker.wk_spell_req(r, rest), _) == (Worker.wk_spell_req(r, rest), True{}) : String & Bool}
  {==}

def wmu_main(+s: String, d: Wr.Dec<FWk.Req>, inv: LAWorkerReads.ci_req(s, d), other: {String.eq(FWk.ffi.go(d), Wr.err("worker: malformed request")) == False{} : Bool}) -> wmu_goal(s):
  match d:
    case Wr.Got{+r, +rest}:
      (e1, e2) = inv
      (r, (rest, wmu_eq(s, r, rest, e1, e2)))
    case Wr.Bad{}:
      LAWireSpell.ws_absurd(wmu_goal(s), other)

def Worker.worker_ffi_malformed_unless_request(s, other):
  wmu_main(s, FWk.get_req(s), LAWorkerReads.ci_req_all(s), other)
