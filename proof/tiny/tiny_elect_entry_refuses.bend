# eukhe: the proof of LAW tiny_elect_entry_refuses
#
# PROOF: the entry answers either a request's choice, a Nat that never
# opens with 'E' (wire_nat_not_err), or the one error form; so an answer
# that opens with 'E' is that error form.

import Base
import ../../bend/tiny.bend as Tn
import ../../bend/ffi_tiny_elect.bend as FTe
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/tiny.bend as Tiny
import ../../laws/wire.bend as Wire
import ../wire/wire_nat_not_err.bend as PWireNatNotErr
import ./base.bend as LA

# a request's choice is a value, never the error form
def te.answer_ok(q: FTe.Req) -> {LawsBase.wire_opens_err(FTe.answer(q)) == False{} : Bool}:
  match q:
    case FTe.QElect{p, m}:
      Wire.wire_nat_not_err(FTe.act.tag(Tn.elect(p, m)), "")
    case FTe.QShut{hd}:
      Wire.wire_nat_not_err(FTe.shut.tag(Tn.shut(hd)), "")
    case FTe.QLaunched{f, l}:
      Wire.wire_nat_not_err(FTe.got.tag(Tn.launched(f, l)), "")
    case FTe.QConfirm{p, m}:
      Wire.wire_nat_not_err(FTe.check.tag(Tn.confirm(p, m)), "")
    case FTe.QBind{p}:
      Wire.wire_nat_not_err(FTe.seat.tag(Tn.bind(p)), "")

def te.refuse(d: Wr.Dec<FTe.Req>, bad: {LawsBase.wire_opens_err(FTe.ffi.got(d)) == True{} : Bool}) -> {FTe.ffi.got(d) == Wr.err("tiny_elect: malformed request") : String}:
  match d:
    case Wr.Got{+q, rest}:
      match rest:
        case SNil{}:
          LA.te.tf({FTe.answer(q) == Wr.err("tiny_elect: malformed request") : String}, Equal.trans(Bool, True{}, LawsBase.wire_opens_err(FTe.answer(q)), False{}, Equal.sym(Bool, LawsBase.wire_opens_err(FTe.answer(q)), True{}, bad), te.answer_ok(q)))
        case SCon{x, y}:
          {==}
    case Wr.Bad{}:
      {==}

def Tiny.tiny_elect_entry_refuses(s, bad):
  te.refuse(FTe.get_req(s), bad)
