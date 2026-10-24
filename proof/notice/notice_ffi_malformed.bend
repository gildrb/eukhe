# eukhe: the proof of LAW notice_ffi_malformed

import Base
import ../../bend/notice.bend as No
import ../../bend/ffi_notice.bend as FNo
import ../../bend/wire.bend as Wr
import ../../laws/notice.bend as Notice
import ../../laws/wire.bend as Wire
import ../../laws/base.bend as LawsBase
import ../wire/wire_bool_not_err.bend as PWireBoolNotErr
import ./base.bend as LA

# A step answers the error form only when its ask is malformed or has
# input left over: an answer of the rule is a Bool (wire_bool_not_err) or
# nothing, neither the error form. Both refusals keep the record.

# the reply to an ask the entry read whole is not the error form
def nm.ans_ok(+rs: List<&2, No.Seen>, q: No.Ask) -> {LawsBase.wire_opens_err(Notice.nt_out(FNo.step.ans(No.answer(rs, q)))) == False{} : Bool}:
  match q:
    case No.Shows{sid, m}:
      Wire.wire_bool_not_err(No.visible(rs, sid, m), "")
    case No.Notes{sid, ms}:
      {==}

def nm.got(rest: String, +rs: List<&2, No.Seen>, +q: No.Ask, h: {LawsBase.wire_opens_err(Notice.nt_out(FNo.step.end(Wr.end(rest), rs, q))) == True{} : Bool}) -> {FNo.step.end(Wr.end(rest), rs, q) == (FNo.Live{rs}, Wr.err("notice: malformed ask")) : FNo.St & String}:
  match rest:
    case SNil{}:
      +x = LawsBase.wire_opens_err(Notice.nt_out(FNo.step.ans(No.answer(rs, q))))
      LA.notice.pn.absurdF({FNo.step.ans(No.answer(rs, q)) == (FNo.Live{rs}, Wr.err("notice: malformed ask")) : FNo.St & String}, Equal.trans(Bool, False{}, x, True{}, Equal.sym(Bool, x, False{}, nm.ans_ok(rs, q)), h))
    case SCon{c, t}:
      {==}

def nm.at(+rs: List<&2, No.Seen>, d: Wr.Dec<No.Ask>, h: {LawsBase.wire_opens_err(Notice.nt_out(FNo.step.ask(rs, d))) == True{} : Bool}) -> {FNo.step.ask(rs, d) == (FNo.Live{rs}, Wr.err("notice: malformed ask")) : FNo.St & String}:
  match d:
    case Wr.Got{+q, +rest}:
      nm.got(rest, rs, q, h)
    case Wr.Bad{}:
      {==}

def Notice.notice_ffi_malformed(rs, s, h):
  nm.at(rs, FNo.get_ask(s), h)
