# eukhe: the proof of LAW strength_entry_refuses
#
# PROOF: the entry answers the error form for every input but a request
# read whole with nothing left, and its answer to such a request never
# opens with 'E' (SX.sx.answer_ok).

import Base
import ../../bend/verify.bend as V
import ../../bend/strength.bend as St
import ../../bend/ffi_strength.bend as FS
import ../../bend/wire.bend as Wr
import ../../spec/verified/strength_wire.bend as SW
import ../../laws/base.bend as LawsBase
import ../../laws/strength.bend as Strength
import ./base/exact.bend as SX

def sxr.refuse(d: Wr.Dec<FS.Req>, bad: {LawsBase.wire_opens_err(FS.ffi.got(d)) == True{} : Bool}) -> {FS.ffi.got(d) == Wr.err("strength: malformed request") : String}:
  match d:
    case Wr.Got{+q, rest}:
      match rest:
        case SNil{}:
          SX.sx.absurdT({FS.answer(q) == Wr.err("strength: malformed request") : String}, Equal.trans(Bool, True{}, LawsBase.wire_opens_err(FS.answer(q)), False{}, Equal.sym(Bool, LawsBase.wire_opens_err(FS.answer(q)), True{}, bad), SX.sx.answer_ok(q)))
        case SCon{x, y}:
          {==}
    case Wr.Bad{}:
      {==}

def Strength.strength_entry_refuses(s, bad):
  sxr.refuse(FS.get_req(Wr.get_nat(s)), bad)
