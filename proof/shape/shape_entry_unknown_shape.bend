# eukhe: the proof of LAW shape_entry_unknown_shape
#
# PROOF: both requests are answered as decided (shape_entry_decides); the
# spelled reply of an unknown id is the error.

import Base
import ../../bend/shape.bend as S
import ../../bend/ffi_shape.bend as FS
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/shape/entry.bend as ShapeEntry
import ../wire/base/spell.bend as LAWireSpell
import ./base/entry.bend as LE

import ./shape_entry_decides.bend as PDecides

def ShapeEntry.shape_entry_unknown_shape(id, ids, text, no, h1, h2):
  %Equal.sym(String, FS.ffi(ShapeEntry.sp_w_req(FS.QAll{id, text}, "")), ShapeEntry.sp_w_reply(FS.QAll{id, text}), ShapeEntry.shape_entry_decides(FS.QAll{id, text}, h1)) : {(_, FS.ffi(ShapeEntry.sp_w_req(FS.QFirst{id <> ids, text}, ""))) == (ShapeEntry.sp_err(), ShapeEntry.sp_err()) : String & String}
  %Equal.sym(String, FS.ffi(ShapeEntry.sp_w_req(FS.QFirst{id <> ids, text}, "")), ShapeEntry.sp_w_reply(FS.QFirst{id <> ids, text}), ShapeEntry.shape_entry_decides(FS.QFirst{id <> ids, text}, h2)) : {(ShapeEntry.sp_w_reply(FS.QAll{id, text}), _) == (ShapeEntry.sp_err(), ShapeEntry.sp_err()) : String & String}
  %Equal.sym(Maybe<&2, S.Shape>, ShapeEntry.sp_shape_of(id), None{}, no) : {(ShapeEntry.sp_w_all(_, text), ShapeEntry.sp_w_first(ShapeEntry.sp_shapes.cons(_, ShapeEntry.sp_shapes(ids)), text)) == (ShapeEntry.sp_err(), ShapeEntry.sp_err()) : String & String}
  {==}
