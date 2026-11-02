# eukhe: the proof of LAW shape_entry_left_over
#
# PROOF: the request reads back with the rest after it (LE.she.req_rt); a rest
# that is not empty is the error.

import Base
import ../../bend/shape.bend as S
import ../../bend/ffi_shape.bend as FS
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/shape/entry.bend as ShapeEntry
import ../wire/base/spell.bend as LAWireSpell
import ./base/entry.bend as LE

def ShapeEntry.shape_entry_left_over(q, rest, h, more):
  %Equal.sym(Wr.Dec<FS.Req>, FS.get_req(ShapeEntry.sp_w_req(q, rest)), Wr.Got{q, rest}, LE.she.req_rt(q, rest, h)) : {FS.ffi.got(_) == ShapeEntry.sp_err() : String}
  %Equal.sym(Bool, String.is_empty(rest), False{}, more) : {FS.ffi.done(q, _) == ShapeEntry.sp_err() : String}
  {==}
