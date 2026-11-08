# eukhe: the proof of LAW dmw_ffi_malformed_unless_request
#
# PROOF: the decoder reads only spelled requests that fit, the rest after
# them untouched (dmc.in of dmw_ffi_reads_only_requests); when it reads
# none the entry answers the malformed error, which the premise excludes.

import Base
import ../../bend/default_model.bend as Dm
import ../../bend/ffi_default_model.bend as FDm
import ../../bend/wire.bend as Wr
import ../../laws/default_model.bend as DefaultModel
import ../wire/base/spell.bend as LAWireSpell
import ./dmw_ffi_reads_only_requests.bend as PDmwFfiReadsOnlyRequests

def dmu.goal(+s: String) -> Type:
  &x: Dm.In -> &rest: String -> {(s, DefaultModel.dmw_in_fits(x)) == (DefaultModel.dmw_spell_req(x, rest), True{}) : String & Bool}

def dmu.eq(+s: String, +x: Dm.In, +rest: String, e1: {s == DefaultModel.dmw_spell_req(x, rest) : String}, e2: {DefaultModel.dmw_in_fits(x) == True{} : Bool}) -> {(s, DefaultModel.dmw_in_fits(x)) == (DefaultModel.dmw_spell_req(x, rest), True{}) : String & Bool}:
  %Equal.sym(String, s, DefaultModel.dmw_spell_req(x, rest), e1) : {(_, DefaultModel.dmw_in_fits(x)) == (DefaultModel.dmw_spell_req(x, rest), True{}) : String & Bool}
  %Equal.sym(Bool, DefaultModel.dmw_in_fits(x), True{}, e2) : {(DefaultModel.dmw_spell_req(x, rest), _) == (DefaultModel.dmw_spell_req(x, rest), True{}) : String & Bool}
  {==}

def dmu.main(+s: String, d: Wr.Dec<Dm.In>, inv: PDmwFfiReadsOnlyRequests.dmc.In(s, d), other: {String.eq(FDm.ffi.go(d), Wr.err("default_model: malformed request")) == False{} : Bool}) -> dmu.goal(s):
  match d:
    case Wr.Got{+x, +rest}:
      (e1, e2) = inv
      (x, (rest, dmu.eq(s, x, rest, e1, e2)))
    case Wr.Bad{}:
      LAWireSpell.ws_absurd(dmu.goal(s), other)

def DefaultModel.dmw_ffi_malformed_unless_request(s, other):
  dmu.main(s, FDm.get_in(s), PDmwFfiReadsOnlyRequests.dmc.in(s), other)
