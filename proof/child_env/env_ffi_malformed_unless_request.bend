# eukhe: the proof of LAW env_ffi_malformed_unless_request
#
# PROOF: the decoder reads only spelled requests that fit, the rest after
# them untouched (pex.req); when it reads none the entry answers the
# malformed error, which the premise excludes.

import Base
import ../../bend/ffi_child_env.bend as FEnv
import ../../bend/wire.bend as Wr
import ../../laws/child_env.bend as ChildEnv
import ../wire/base/spell.bend as LAWireSpell
import ./env_ffi_reads_only_requests/exact.bend as LX

def pemu.goal(+s: String) -> Type:
  &q: FEnv.Req -> &rest: String -> {(s, ChildEnv.env_req_fits(q)) == (ChildEnv.env_spell_req(q, rest), True{}) : String & Bool}

def pemu.eq(+s: String, +q: FEnv.Req, +rest: String, e1: {s == ChildEnv.env_spell_req(q, rest) : String}, e2: {ChildEnv.env_req_fits(q) == True{} : Bool}) -> {(s, ChildEnv.env_req_fits(q)) == (ChildEnv.env_spell_req(q, rest), True{}) : String & Bool}:
  %Equal.sym(String, s, ChildEnv.env_spell_req(q, rest), e1) : {(_, ChildEnv.env_req_fits(q)) == (ChildEnv.env_spell_req(q, rest), True{}) : String & Bool}
  %Equal.sym(Bool, ChildEnv.env_req_fits(q), True{}, e2) : {(ChildEnv.env_spell_req(q, rest), _) == (ChildEnv.env_spell_req(q, rest), True{}) : String & Bool}
  {==}

def pemu.main(+s: String, d: Wr.Dec<FEnv.Req>, inv: LX.pex.RP(s, d), other: {String.eq(FEnv.ffi.go(d), Wr.err("child_env: malformed request")) == False{} : Bool}) -> pemu.goal(s):
  match d:
    case Wr.Got{+q, +rest}:
      (e1, e2) = inv
      (q, (rest, pemu.eq(s, q, rest, e1, e2)))
    case Wr.Bad{}:
      LAWireSpell.ws_absurd(pemu.goal(s), other)

def ChildEnv.env_ffi_malformed_unless_request(s, other):
  pemu.main(s, FEnv.get_req(s), LX.pex.req(s), other)
