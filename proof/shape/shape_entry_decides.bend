# eukhe: the proof of LAW shape_entry_decides
#
# PROOF: the encoding of a request that fits reads back with nothing left
# (LE.she.req_rt), so the entry answers the request; the answer is the
# spelled spec answer (LE.she.answer).

import Base
import ../../bend/shape.bend as S
import ../../bend/ffi_shape.bend as FS
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/shape/entry.bend as ShapeEntry
import ../wire/base/spell.bend as LAWireSpell
import ./base/entry.bend as LE

def ShapeEntry.shape_entry_decides(q, h):
  %Equal.sym(Wr.Dec<FS.Req>, FS.get_req(ShapeEntry.sp_w_req(q, "")), Wr.Got{q, ""}, LE.she.req_rt(q, "", h)) : {FS.ffi.got(_) == ShapeEntry.sp_w_reply(q) : String}
  LE.she.answer(q)
