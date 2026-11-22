# eukhe: the proof of LAW attack_entry_refuses
#
# PROOF: the entry answers the error form for every input but a request
# read whole with nothing left, and its answer to such a request never
# opens with 'E' (LX.axe.answer_ok).

import Base
import ../../bend/verify.bend as V
import ../../bend/strength.bend as St
import ../../bend/attack.bend as At
import ../../bend/ffi_attack.bend as FA
import ../../bend/wire.bend as Wr
import ../../spec/verified/attack_wire.bend as SAW
import ../../laws/base.bend as LawsBase
import ../../laws/attack.bend as Attack
import ./base/entry.bend as LE
import ../strength/base/exact.bend as SX
import ./base/exact.bend as LX

def afr.refuse(d: Wr.Dec<FA.Req>, bad: {LawsBase.wire_opens_err(FA.ffi.got(d)) == True{} : Bool}) -> {FA.ffi.got(d) == Wr.err("attack: malformed request") : String}:
  match d:
    case Wr.Got{+q, rest}:
      match rest:
        case SNil{}:
          SX.sx.absurdT({FA.answer(q) == Wr.err("attack: malformed request") : String}, Equal.trans(Bool, True{}, LawsBase.wire_opens_err(FA.answer(q)), False{}, Equal.sym(Bool, LawsBase.wire_opens_err(FA.answer(q)), True{}, bad), LX.axe.answer_ok(q)))
        case SCon{x, y}:
          {==}
    case Wr.Bad{}:
      {==}

def Attack.attack_entry_refuses(s, bad):
  afr.refuse(FA.get_req(Wr.get_nat(s)), bad)
