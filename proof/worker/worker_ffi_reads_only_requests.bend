# eukhe: the proof of LAW worker_ffi_reads_only_requests
#
# PROOF of LAW worker_ffi_reads_only_requests: an answer that is not the
# error form comes from a request the decoder read whole (a malformed
# request or input left over answers the error form). The decoder accepts
# only spellings that fit (ci_req_all of proof/worker/base/reads.bend);
# that request is the witness, and the entry answers it with the spelled
# reply (we_run).

import Base
import ../../bend/ffi_worker.bend as FWk
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/worker.bend as Worker
import ../wire/base/spell.bend as LAWireSpell
import ./base/entry.bend as LAWorkerEntry
import ./base/reads.bend as LAWorkerReads

# the claim: s spells a request that fits, and the entry answers it
def wro_goal(+s: String) -> Type:
  &r: FWk.Req -> {(s, (Worker.wk_req_fits(r), FWk.ffi(s))) == (Worker.wk_spell_req(r, ""), (True{}, Worker.wk_spell_reply(r))) : String & (Bool & String)}

def wro_eq(+s: String, +r: FWk.Req, ed: {FWk.get_req(s) == Wr.Got{r, ""} : Wr.Dec<FWk.Req>},
  e1: {s == Worker.wk_spell_req(r, "") : String}, e2: {Worker.wk_req_fits(r) == True{} : Bool}) ->
  {(s, (Worker.wk_req_fits(r), FWk.ffi(s))) == (Worker.wk_spell_req(r, ""), (True{}, Worker.wk_spell_reply(r))) : String & (Bool & String)}:
  %Equal.sym(Wr.Dec<FWk.Req>, FWk.get_req(s), Wr.Got{r, ""}, ed) : {(s, (Worker.wk_req_fits(r), FWk.ffi.go(_))) == (Worker.wk_spell_req(r, ""), (True{}, Worker.wk_spell_reply(r))) : String & (Bool & String)}
  %Equal.sym(String, FWk.ffi.run(r), Worker.wk_spell_reply(r), LAWorkerEntry.we_run(r)) : {(s, (Worker.wk_req_fits(r), _)) == (Worker.wk_spell_req(r, ""), (True{}, Worker.wk_spell_reply(r))) : String & (Bool & String)}
  %Equal.sym(Bool, Worker.wk_req_fits(r), True{}, e2) : {(s, (_, Worker.wk_spell_reply(r))) == (Worker.wk_spell_req(r, ""), (True{}, Worker.wk_spell_reply(r))) : String & (Bool & String)}
  %Equal.sym(String, s, Worker.wk_spell_req(r, ""), e1) : {(_, (True{}, Worker.wk_spell_reply(r))) == (Worker.wk_spell_req(r, ""), (True{}, Worker.wk_spell_reply(r))) : String & (Bool & String)}
  {==}

def wro_rest(+s: String, +r: FWk.Req, rest: String, ed: {FWk.get_req(s) == Wr.Got{r, rest} : Wr.Dec<FWk.Req>},
  e1: {s == Worker.wk_spell_req(r, rest) : String}, e2: {Worker.wk_req_fits(r) == True{} : Bool},
  ok: {LawsBase.wire_opens_err(FWk.ffi.whole(r, String.is_empty(rest))) == False{} : Bool}) -> wro_goal(s):
  match rest:
    case SNil{}:
      (r, wro_eq(s, r, ed, e1, e2))
    case SCon{c, more}:
      LAWireSpell.ws_absurd(wro_goal(s), ok)

def wro_main(+s: String, d: Wr.Dec<FWk.Req>, ed: {FWk.get_req(s) == d : Wr.Dec<FWk.Req>}, inv: LAWorkerReads.ci_req(s, d),
  ok: {LawsBase.wire_opens_err(FWk.ffi.go(d)) == False{} : Bool}) -> wro_goal(s):
  match d:
    case Wr.Got{+r, +rest}:
      (e1, e2) = inv
      wro_rest(s, r, rest, ed, e1, e2, ok)
    case Wr.Bad{}:
      LAWireSpell.ws_absurd(wro_goal(s), ok)

def Worker.worker_ffi_reads_only_requests(s, ok):
  wro_main(s, FWk.get_req(s), {==}, LAWorkerReads.ci_req_all(s), ok)
