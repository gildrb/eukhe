# eukhe: the proof of LAW staging_entry_malformed_unless_request
#
# PROOF: the decoder reads only spelled requests that fit, the rest after
# them untouched (ex.req of staging_entry_exact); when it reads none the
# entry answers the malformed error, which the premise excludes.

import Base
import ../../bend/ffi_staging.bend as FSg
import ../../bend/wire.bend as Wr
import ../../laws/staging.bend as Staging
import ./staging_entry_exact.bend as PStagingEntryExact

def smu.goal(+s: String) -> Type:
  &r: FSg.Req -> &rest: String -> {(s, Staging.sp_fit_req(r)) == (Staging.sp_w_req(r, rest), True{}) : String & Bool}

def smu.eq(+s: String, +r: FSg.Req, +rest: String, e1: {s == Staging.sp_w_req(r, rest) : String}, e2: {Staging.sp_fit_req(r) == True{} : Bool}) -> {(s, Staging.sp_fit_req(r)) == (Staging.sp_w_req(r, rest), True{}) : String & Bool}:
  %Equal.sym(String, s, Staging.sp_w_req(r, rest), e1) : {(_, Staging.sp_fit_req(r)) == (Staging.sp_w_req(r, rest), True{}) : String & Bool}
  %Equal.sym(Bool, Staging.sp_fit_req(r), True{}, e2) : {(Staging.sp_w_req(r, rest), _) == (Staging.sp_w_req(r, rest), True{}) : String & Bool}
  {==}

def smu.main(+s: String, d: Wr.Dec<FSg.Req>, rp: PStagingEntryExact.ex.RP(s, d), other: {String.eq(FSg.answer(d), Wr.err("staging: malformed request")) == False{} : Bool}) -> smu.goal(s):
  match d:
    case Wr.Got{+r, +rest}:
      (e1, e2) = rp
      (r, (rest, smu.eq(s, r, rest, e1, e2)))
    case Wr.Bad{}:
      PStagingEntryExact.ex.tf(smu.goal(s), other)

def Staging.staging_entry_malformed_unless_request(s, other):
  smu.main(s, FSg.get_req(s), PStagingEntryExact.ex.req(s), other)
