# eukhe: the proof of LAW tools_ffi_malformed_unless_request
#
# PROOF: the decoder reads only spelled paths that fit, the rest after
# them untouched (tro.req of tools_ffi_reads_only_requests); when it reads
# none the entry answers the malformed error, which the premise excludes.

import Base
import ../../bend/ffi_tools.bend as FTl
import ../../bend/tools.bend as Tl
import ../../bend/wire.bend as Wr
import ../../laws/tools.bend as Tools
import ../wire/base/spell.bend as LAWireSpell
import ./tools_ffi_reads_only_requests.bend as PToolsFfiReadsOnlyRequests

def tmu.goal(+s: String) -> Type:
  &gs: List<&2, Tl.Seg> -> &rest: String -> {(s, Tools.tools_req_fits(gs)) == (Tools.tools_spell_req(gs, rest), True{}) : String & Bool}

def tmu.eq(+s: String, +gs: List<&2, Tl.Seg>, +rest: String, e1: {s == Tools.tools_spell_req(gs, rest) : String}, e2: {Tools.tools_req_fits(gs) == True{} : Bool}) -> {(s, Tools.tools_req_fits(gs)) == (Tools.tools_spell_req(gs, rest), True{}) : String & Bool}:
  %Equal.sym(String, s, Tools.tools_spell_req(gs, rest), e1) : {(_, Tools.tools_req_fits(gs)) == (Tools.tools_spell_req(gs, rest), True{}) : String & Bool}
  %Equal.sym(Bool, Tools.tools_req_fits(gs), True{}, e2) : {(Tools.tools_spell_req(gs, rest), _) == (Tools.tools_spell_req(gs, rest), True{}) : String & Bool}
  {==}

def tmu.main(+s: String, d: Wr.Dec<List<&2, Tl.Seg>>, inv: PToolsFfiReadsOnlyRequests.tro.Req(s, d), other: {String.eq(FTl.answer(d), Wr.err("tools: malformed request")) == False{} : Bool}) -> tmu.goal(s):
  match d:
    case Wr.Got{+gs, +rest}:
      (e1, e2) = inv
      (gs, (rest, tmu.eq(s, gs, rest, e1, e2)))
    case Wr.Bad{}:
      LAWireSpell.ws_absurd(tmu.goal(s), other)

def Tools.tools_ffi_malformed_unless_request(s, other):
  tmu.main(s, FTl.get_req(s), PToolsFfiReadsOnlyRequests.tro.req(s), other)
