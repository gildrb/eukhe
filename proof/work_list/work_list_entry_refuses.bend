# eukhe: the proof of LAW work_list_entry_refuses
#
# PROOF: the entry answers either a hand-back, which opens with its tag
# (never 'E': wire_nat_not_err), or the one error form; so an answer that
# opens with 'E' is that error form.

import Base
import ../../bend/work_list.bend as Wl
import ../../bend/ffi_work_list.bend as FWl
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../../laws/work_list.bend as WorkList
import ../wire/wire_nat_not_err.bend as PWireNatNotErr
import ../base/staging.bend as LStg

def wlr.answer_ok(o: Wl.Outcome) -> {LawsBase.wire_opens_err(FWl.put_outcome(o)) == False{} : Bool}:
  match o:
    case Wl.Finished{}:
      Wire.wire_nat_not_err(0n, "")
    case Wl.Stopped{xs}:
      Wire.wire_nat_not_err(1n, Wr.put_list(~Nat, ~Wr.put_nat, xs, ""))

def wlr.refuse(d: Wr.Dec<List<&2, Bool>>, bad: {LawsBase.wire_opens_err(FWl.ffi.got(d)) == True{} : Bool}) -> {FWl.ffi.got(d) == Wr.err("work_list: malformed request") : String}:
  match d:
    case Wr.Got{+q, rest}:
      match rest:
        case SNil{}:
          LStg.stg.absurd({FWl.answer(q) == Wr.err("work_list: malformed request") : String}, Equal.trans(Bool, True{}, LawsBase.wire_opens_err(FWl.answer(q)), False{}, Equal.sym(Bool, LawsBase.wire_opens_err(FWl.answer(q)), True{}, bad), wlr.answer_ok(Wl.outcome(q))))
        case SCon{x, y}:
          {==}
    case Wr.Bad{}:
      {==}

def WorkList.work_list_entry_refuses(s, bad):
  wlr.refuse(FWl.get_req(s), bad)
