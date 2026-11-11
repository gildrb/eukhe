# eukhe: the proof of LAW restart_ffi_malformed_unless_request
#
# PROOF: the entry's reader reads only spelled requests that fit, the rest
# after them untouched (LAE.rse.ro); when it reads none the entry answers
# the malformed error, which the premise excludes.

import Base
import ../../bend/ffi_supervise.bend as FS
import ../../bend/wire.bend as Wr
import ../../laws/supervise.bend as Supervise
import ../wire/base/spell.bend as LAWireSpell
import ./base/entry.bend as LAE

def rmu.goal(+s: String) -> Type:
  &q: FS.Req -> &rest: String -> {(s, Supervise.rs_req_fits(q)) == (Supervise.rs_spell_req(q, rest), True{}) : String & Bool}

def rmu.eq(+s: String, +q: FS.Req, +rest: String, e1: {s == Supervise.rs_spell_req(q, rest) : String}, e2: {Supervise.rs_req_fits(q) == True{} : Bool}) -> {(s, Supervise.rs_req_fits(q)) == (Supervise.rs_spell_req(q, rest), True{}) : String & Bool}:
  %Equal.sym(String, s, Supervise.rs_spell_req(q, rest), e1) : {(_, Supervise.rs_req_fits(q)) == (Supervise.rs_spell_req(q, rest), True{}) : String & Bool}
  %Equal.sym(Bool, Supervise.rs_req_fits(q), True{}, e2) : {(Supervise.rs_spell_req(q, rest), _) == (Supervise.rs_spell_req(q, rest), True{}) : String & Bool}
  {==}

def rmu.main(+s: String, d: Wr.Dec<FS.Req>, inv: LAE.rse.RQ(s, d), other: {String.eq(FS.ffi.go(d), Supervise.rs_malformed()) == False{} : Bool}) -> rmu.goal(s):
  match d:
    case Wr.Got{+q, +rest}:
      (e1, e2) = inv
      (q, (rest, rmu.eq(s, q, rest, e1, e2)))
    case Wr.Bad{}:
      LAWireSpell.ws_absurd(rmu.goal(s), other)

def Supervise.restart_ffi_malformed_unless_request(s, other):
  rmu.main(s, FS.get_req(s), LAE.rse.ro(s), other)
