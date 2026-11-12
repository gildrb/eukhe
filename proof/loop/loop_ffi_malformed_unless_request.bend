# eukhe: the proof of LAW loop_ffi_malformed_unless_request
#
# PROOF: the decoder reads only spelled requests that fit, the rest after
# them untouched (le.ci_req_all of proof/loop/base/reads.bend); when it
# reads none the entry answers the malformed error, which the premise
# excludes.

import Base
import ../../bend/ffi_loop.bend as FLp
import ../../bend/wire.bend as Wr
import ../../laws/loop/entry.bend as LoopEntry
import ../wire/base/spell.bend as LAWireSpell
import ./base/reads.bend as LALoopReads

def lmu_goal(+s: String) -> Type:
  &r: FLp.Req -> &rest: String -> {(s, LoopEntry.lp_req_fits(r)) == (LoopEntry.lp_spell_req(r, rest), True{}) : String & Bool}

def lmu_eq(+s: String, +r: FLp.Req, +rest: String, e1: {s == LoopEntry.lp_spell_req(r, rest) : String}, e2: {LoopEntry.lp_req_fits(r) == True{} : Bool}) -> {(s, LoopEntry.lp_req_fits(r)) == (LoopEntry.lp_spell_req(r, rest), True{}) : String & Bool}:
  %Equal.sym(String, s, LoopEntry.lp_spell_req(r, rest), e1) : {(_, LoopEntry.lp_req_fits(r)) == (LoopEntry.lp_spell_req(r, rest), True{}) : String & Bool}
  %Equal.sym(Bool, LoopEntry.lp_req_fits(r), True{}, e2) : {(LoopEntry.lp_spell_req(r, rest), _) == (LoopEntry.lp_spell_req(r, rest), True{}) : String & Bool}
  {==}

def lmu_main(+s: String, d: Wr.Dec<FLp.Req>, inv: LALoopReads.le.ci_req(s, d), other: {String.eq(FLp.ffi.go(d), Wr.err("loop: malformed request")) == False{} : Bool}) -> lmu_goal(s):
  match d:
    case Wr.Got{+r, +rest}:
      (e1, e2) = inv
      (r, (rest, lmu_eq(s, r, rest, e1, e2)))
    case Wr.Bad{}:
      LAWireSpell.ws_absurd(lmu_goal(s), other)

def LoopEntry.loop_ffi_malformed_unless_request(s, other):
  lmu_main(s, FLp.get_req(s), LALoopReads.le.ci_req_all(s), other)
