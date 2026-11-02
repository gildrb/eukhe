# eukhe: the proof of LAW shape_entry_reads_only_requests
#
# PROOF: whatever the decoder reads is the spelling of a request that fits,
# then its rest (LE.she.rp_all); an answer that is not the error form comes
# from a request read with nothing left, answered with the spelled spec
# answer (LE.she.answer); the Bad and left-over arms answer the error.

import Base
import ../../bend/shape.bend as S
import ../../bend/ffi_shape.bend as FS
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/shape/entry.bend as ShapeEntry
import ../wire/base/spell.bend as LAWireSpell
import ./base/entry.bend as LE

def sro.top_eq(+s: String, +q: FS.Req, e: {s == ShapeEntry.sp_w_req(q, "") : String}, f: {ShapeEntry.sp_fit_req(q) == True{} : Bool}) -> {(s, (ShapeEntry.sp_fit_req(q), FS.answer(q))) == (ShapeEntry.sp_w_req(q, ""), (True{}, ShapeEntry.sp_w_reply(q))) : String & (Bool & String)}:
  %Equal.sym(String, s, ShapeEntry.sp_w_req(q, ""), e) : {(_, (ShapeEntry.sp_fit_req(q), FS.answer(q))) == (ShapeEntry.sp_w_req(q, ""), (True{}, ShapeEntry.sp_w_reply(q))) : String & (Bool & String)}
  %Equal.sym(Bool, ShapeEntry.sp_fit_req(q), True{}, f) : {(ShapeEntry.sp_w_req(q, ""), (_, FS.answer(q))) == (ShapeEntry.sp_w_req(q, ""), (True{}, ShapeEntry.sp_w_reply(q))) : String & (Bool & String)}
  %Equal.sym(String, FS.answer(q), ShapeEntry.sp_w_reply(q), LE.she.answer(q)) : {(ShapeEntry.sp_w_req(q, ""), (True{}, _)) == (ShapeEntry.sp_w_req(q, ""), (True{}, ShapeEntry.sp_w_reply(q))) : String & (Bool & String)}
  {==}

def sro.TopG(s: String, a: String) -> Type:
  Sigma<&1, &1, FS.Req, q => {(s, (ShapeEntry.sp_fit_req(q), a)) == (ShapeEntry.sp_w_req(q, ""), (True{}, ShapeEntry.sp_w_reply(q))) : String & (Bool & String)}>

def sro.top(+s: String, d: Wr.Dec<FS.Req>, rp: LE.she.RP(s, d), ok: {LawsBase.wire_opens_err(FS.ffi.got(d)) == False{} : Bool}) -> sro.TopG(s, FS.ffi.got(d)):
  match d:
    case Wr.Got{+q, rest}:
      match rest:
        case SNil{}:
          (e, f) = rp
          (q, sro.top_eq(s, q, e, f))
        case SCon{x, y}:
          LAWireSpell.ws_absurd(sro.TopG(s, Wr.err("shape: malformed request")), ok)
    case Wr.Bad{}:
      LAWireSpell.ws_absurd(sro.TopG(s, Wr.err("shape: malformed request")), ok)

def ShapeEntry.shape_entry_reads_only_requests(s, ok):
  sro.top(s, FS.get_req(s), LE.she.rp_all(s), ok)
