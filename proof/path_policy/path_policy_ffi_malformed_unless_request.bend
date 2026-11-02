# eukhe: the proof of LAW path_policy_ffi_malformed_unless_request
#
# PROOF of LAW path_policy_ffi_malformed_unless_request: the decoder reads
# only spelled requests that fit, the rest after them untouched (pe.dec);
# when it reads none the entry answers the malformed error, which the
# premise excludes.

import Base
import ../../bend/ffi_path_policy.bend as FPp
import ../../bend/wire.bend as Wr
import ../../laws/path_policy.bend as PathPolicy
import ../wire/base/spell.bend as LAWireSpell
import ./base/entry.bend as LAPathPolicyEntry

def pmu.goal(+s: String) -> Type:
  &q: FPp.Req -> &rest: String -> {(s, PathPolicy.pp_req_fits(q)) == (PathPolicy.pp_spell_req(q, rest), True{}) : String & Bool}

def pmu.eq(+s: String, +q: FPp.Req, +rest: String, e1: {s == PathPolicy.pp_spell_req(q, rest) : String}, e2: {PathPolicy.pp_req_fits(q) == True{} : Bool}) -> {(s, PathPolicy.pp_req_fits(q)) == (PathPolicy.pp_spell_req(q, rest), True{}) : String & Bool}:
  %Equal.sym(String, s, PathPolicy.pp_spell_req(q, rest), e1) : {(_, PathPolicy.pp_req_fits(q)) == (PathPolicy.pp_spell_req(q, rest), True{}) : String & Bool}
  %Equal.sym(Bool, PathPolicy.pp_req_fits(q), True{}, e2) : {(PathPolicy.pp_spell_req(q, rest), _) == (PathPolicy.pp_spell_req(q, rest), True{}) : String & Bool}
  {==}

def pmu.main(+s: String, d: Wr.Dec<FPp.Req>, inv: LAPathPolicyEntry.pe.RP(s, d), other: {String.eq(FPp.answer(d), Wr.err("path_policy: malformed request")) == False{} : Bool}) -> pmu.goal(s):
  match d:
    case Wr.Got{+q, +rest}:
      (e1, e2) = inv
      (q, (rest, pmu.eq(s, q, rest, e1, e2)))
    case Wr.Bad{}:
      LAWireSpell.ws_absurd(pmu.goal(s), other)

def PathPolicy.path_policy_ffi_malformed_unless_request(s, other):
  pmu.main(s, FPp.get_req(s), LAPathPolicyEntry.pe.dec(s), other)
