# eukhe: the proof of LAW shape_entry_malformed_unless_request
#
# PROOF: the Bad arm answers exactly the malformed error, which contradicts
# the premise; a request read is the spelling of a request that fits, then
# its rest (LE.she.rp_all).

import Base
import ../../bend/shape.bend as S
import ../../bend/ffi_shape.bend as FS
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/shape/entry.bend as ShapeEntry
import ../wire/base/spell.bend as LAWireSpell
import ./base/entry.bend as LE

def srm.MuG(s: String) -> Type:
  Sigma<&1, &1, FS.Req, q => Sigma<&1, &1, String, rest => {(s, ShapeEntry.sp_fit_req(q)) == (ShapeEntry.sp_w_req(q, rest), True{}) : String & Bool}>>

def srm.mu_eq(+s: String, +q: FS.Req, +rest: String, e: {s == ShapeEntry.sp_w_req(q, rest) : String}, f: {ShapeEntry.sp_fit_req(q) == True{} : Bool}) -> {(s, ShapeEntry.sp_fit_req(q)) == (ShapeEntry.sp_w_req(q, rest), True{}) : String & Bool}:
  %Equal.sym(String, s, ShapeEntry.sp_w_req(q, rest), e) : {(_, ShapeEntry.sp_fit_req(q)) == (ShapeEntry.sp_w_req(q, rest), True{}) : String & Bool}
  %Equal.sym(Bool, ShapeEntry.sp_fit_req(q), True{}, f) : {(ShapeEntry.sp_w_req(q, rest), _) == (ShapeEntry.sp_w_req(q, rest), True{}) : String & Bool}
  {==}

def srm.mu(+s: String, d: Wr.Dec<FS.Req>, rp: LE.she.RP(s, d), other: {String.eq(FS.ffi.got(d), ShapeEntry.sp_err()) == False{} : Bool}) -> srm.MuG(s):
  match d:
    case Wr.Got{+q, +rest}:
      (e, f) = rp
      (q, (rest, srm.mu_eq(s, q, rest, e, f)))
    case Wr.Bad{}:
      LAWireSpell.ws_absurd(srm.MuG(s), other)

def ShapeEntry.shape_entry_malformed_unless_request(s, other):
  srm.mu(s, FS.get_req(s), LE.she.rp_all(s), other)
