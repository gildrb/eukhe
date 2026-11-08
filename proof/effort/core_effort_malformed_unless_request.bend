# eukhe: the proof of LAW core_effort_malformed_unless_request
#
# PROOF: the decoder reads only spelled requests that fit, the rest after
# them untouched (EX.ex.req); when it reads none the entry answers the
# malformed error, which the premise excludes.

import Base
import ../../bend/ffi_effort.bend as FEf
import ../../bend/wire.bend as Wr
import ../../laws/effort/ladder.bend as EffortLadder
import ../wire/base/spell.bend as LAWireSpell
import ./core_effort_reads_only_requests/exact.bend as EX

def emu.goal(+s: String) -> Type:
  &q: FEf.Req -> &rest: String -> {(s, EffortLadder.core_effort_fits(q)) == (EffortLadder.core_effort_spell_req(q, rest), True{}) : String & Bool}

def emu.eq(+s: String, +q: FEf.Req, +rest: String, e1: {s == EffortLadder.core_effort_spell_req(q, rest) : String}, e2: {EffortLadder.core_effort_fits(q) == True{} : Bool}) -> {(s, EffortLadder.core_effort_fits(q)) == (EffortLadder.core_effort_spell_req(q, rest), True{}) : String & Bool}:
  %Equal.sym(String, s, EffortLadder.core_effort_spell_req(q, rest), e1) : {(_, EffortLadder.core_effort_fits(q)) == (EffortLadder.core_effort_spell_req(q, rest), True{}) : String & Bool}
  %Equal.sym(Bool, EffortLadder.core_effort_fits(q), True{}, e2) : {(EffortLadder.core_effort_spell_req(q, rest), _) == (EffortLadder.core_effort_spell_req(q, rest), True{}) : String & Bool}
  {==}

def emu.main(+s: String, d: Wr.Dec<FEf.Req>, inv: EX.ex.Req(s, d), other: {String.eq(FEf.ffi.go(d), Wr.err("ladder request: malformed")) == False{} : Bool}) -> emu.goal(s):
  match d:
    case Wr.Got{+q, +rest}:
      (e1, e2) = inv
      (q, (rest, emu.eq(s, q, rest, e1, e2)))
    case Wr.Bad{}:
      LAWireSpell.ws_absurd(emu.goal(s), other)

def EffortLadder.core_effort_malformed_unless_request(s, other):
  emu.main(s, FEf.get_req(s), EX.ex.req(s), other)
