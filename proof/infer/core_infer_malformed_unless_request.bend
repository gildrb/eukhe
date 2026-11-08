# eukhe: the proof of LAW core_infer_malformed_unless_request
#
# PROOF: the decoder reads only spelled requests that fit, the rest after
# them untouched (IX.ix.req); when it reads none the entry answers the
# malformed error, which the premise excludes.

import Base
import ../../bend/ffi_infer.bend as FIn
import ../../bend/wire.bend as Wr
import ../../laws/infer.bend as Infer
import ../wire/base/spell.bend as LAWireSpell
import ./core_infer_reads_only_requests/exact.bend as IX

def imu.goal(+s: String) -> Type:
  &q: FIn.Req -> &rest: String -> {(s, Infer.core_infer_fits(q)) == (Infer.core_infer_spell_req(q, rest), True{}) : String & Bool}

def imu.eq(+s: String, +q: FIn.Req, +rest: String, e1: {s == Infer.core_infer_spell_req(q, rest) : String}, e2: {Infer.core_infer_fits(q) == True{} : Bool}) -> {(s, Infer.core_infer_fits(q)) == (Infer.core_infer_spell_req(q, rest), True{}) : String & Bool}:
  %Equal.sym(String, s, Infer.core_infer_spell_req(q, rest), e1) : {(_, Infer.core_infer_fits(q)) == (Infer.core_infer_spell_req(q, rest), True{}) : String & Bool}
  %Equal.sym(Bool, Infer.core_infer_fits(q), True{}, e2) : {(Infer.core_infer_spell_req(q, rest), _) == (Infer.core_infer_spell_req(q, rest), True{}) : String & Bool}
  {==}

def imu.main(+s: String, d: Wr.Dec<FIn.Req>, inv: IX.ix.Req(s, d), other: {String.eq(FIn.ffi.go(d), Wr.err("strict plan request: malformed")) == False{} : Bool}) -> imu.goal(s):
  match d:
    case Wr.Got{+q, +rest}:
      (e1, e2) = inv
      (q, (rest, imu.eq(s, q, rest, e1, e2)))
    case Wr.Bad{}:
      LAWireSpell.ws_absurd(imu.goal(s), other)

def Infer.core_infer_malformed_unless_request(s, other):
  imu.main(s, FIn.get_req(s), IX.ix.req(s), other)
