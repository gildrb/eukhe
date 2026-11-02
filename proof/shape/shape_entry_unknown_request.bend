# eukhe: the proof of LAW shape_entry_unknown_request
#
# PROOF: the request tag 2 + n reads as itself when it fits and as Bad when
# too long (ws_nat_read); both ways the request is Bad.

import Base
import ../../bend/shape.bend as S
import ../../bend/ffi_shape.bend as FS
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/shape/entry.bend as ShapeEntry
import ../wire/base/spell.bend as LAWireSpell
import ./base/entry.bend as LE

def sru.bad(b: Bool, -n: Nat, -rest: String) -> {FS.get_req.tag(LAWireSpell.ws_nat_answer(b, 2n+n, rest)) == Wr.Bad{} : Wr.Dec<FS.Req>}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def ShapeEntry.shape_entry_unknown_request(n, rest):
  +x = Wr.put_nat(2n+n, rest)
  %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(x), LAWireSpell.ws_nat_answer(LawsBase.wire_fits(2n+n), 2n+n, rest), LAWireSpell.ws_nat_read(2n+n, rest)) : {FS.ffi.got(FS.get_req.tag(_)) == ShapeEntry.sp_err() : String}
  %Equal.sym(Wr.Dec<FS.Req>, FS.get_req.tag(LAWireSpell.ws_nat_answer(LawsBase.wire_fits(2n+n), 2n+n, rest)), Wr.Bad{}, sru.bad(LawsBase.wire_fits(2n+n), n, rest)) : {FS.ffi.got(_) == ShapeEntry.sp_err() : String}
  {==}
