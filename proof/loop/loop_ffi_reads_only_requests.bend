# eukhe: the proof of LAW loop_ffi_reads_only_requests
#
# PROOF: a malformed request or input left over answers the error form, so
# the decoder read a request whole. It accepts only spellings that fit
# (le.ci_req_all); that request is the witness, and the entry answers it
# with the spelled reply (le.run).

import Base
import ../../bend/ffi_loop.bend as FLp
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/loop/entry.bend as LoopEntry
import ../wire/base/spell.bend as LAWireSpell
import ./base/entry.bend as LALoopEntry
import ./base/reads.bend as LALoopReads

# the claim: s spells a request that fits, and the entry answers it
def lro_goal(+s: String) -> Type:
  &r: FLp.Req -> {(s, (LoopEntry.lp_req_fits(r), FLp.ffi(s))) == (LoopEntry.lp_spell_req(r, ""), (True{}, LoopEntry.lp_spell_reply(r))) : String & (Bool & String)}

def lro_eq(+s: String, +r: FLp.Req, ed: {FLp.get_req(s) == Wr.Got{r, ""} : Wr.Dec<FLp.Req>},
  e1: {s == LoopEntry.lp_spell_req(r, "") : String}, e2: {LoopEntry.lp_req_fits(r) == True{} : Bool}) ->
  {(s, (LoopEntry.lp_req_fits(r), FLp.ffi(s))) == (LoopEntry.lp_spell_req(r, ""), (True{}, LoopEntry.lp_spell_reply(r))) : String & (Bool & String)}:
  %Equal.sym(Wr.Dec<FLp.Req>, FLp.get_req(s), Wr.Got{r, ""}, ed) : {(s, (LoopEntry.lp_req_fits(r), FLp.ffi.go(_))) == (LoopEntry.lp_spell_req(r, ""), (True{}, LoopEntry.lp_spell_reply(r))) : String & (Bool & String)}
  %Equal.sym(String, FLp.ffi.run(r), LoopEntry.lp_spell_reply(r), LALoopEntry.le.run(r)) : {(s, (LoopEntry.lp_req_fits(r), _)) == (LoopEntry.lp_spell_req(r, ""), (True{}, LoopEntry.lp_spell_reply(r))) : String & (Bool & String)}
  %Equal.sym(Bool, LoopEntry.lp_req_fits(r), True{}, e2) : {(s, (_, LoopEntry.lp_spell_reply(r))) == (LoopEntry.lp_spell_req(r, ""), (True{}, LoopEntry.lp_spell_reply(r))) : String & (Bool & String)}
  %Equal.sym(String, s, LoopEntry.lp_spell_req(r, ""), e1) : {(_, (True{}, LoopEntry.lp_spell_reply(r))) == (LoopEntry.lp_spell_req(r, ""), (True{}, LoopEntry.lp_spell_reply(r))) : String & (Bool & String)}
  {==}

def lro_rest(+s: String, +r: FLp.Req, rest: String, ed: {FLp.get_req(s) == Wr.Got{r, rest} : Wr.Dec<FLp.Req>},
  e1: {s == LoopEntry.lp_spell_req(r, rest) : String}, e2: {LoopEntry.lp_req_fits(r) == True{} : Bool},
  ok: {LawsBase.wire_opens_err(FLp.ffi.whole(r, String.is_empty(rest))) == False{} : Bool}) -> lro_goal(s):
  match rest:
    case SNil{}:
      (r, lro_eq(s, r, ed, e1, e2))
    case SCon{c, more}:
      LAWireSpell.ws_absurd(lro_goal(s), ok)

def lro_main(+s: String, d: Wr.Dec<FLp.Req>, ed: {FLp.get_req(s) == d : Wr.Dec<FLp.Req>}, inv: LALoopReads.le.ci_req(s, d),
  ok: {LawsBase.wire_opens_err(FLp.ffi.go(d)) == False{} : Bool}) -> lro_goal(s):
  match d:
    case Wr.Got{+r, +rest}:
      (e1, e2) = inv
      lro_rest(s, r, rest, ed, e1, e2, ok)
    case Wr.Bad{}:
      LAWireSpell.ws_absurd(lro_goal(s), ok)

def LoopEntry.loop_ffi_reads_only_requests(s, ok):
  lro_main(s, FLp.get_req(s), {==}, LALoopReads.le.ci_req_all(s), ok)
