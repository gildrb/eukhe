# eukhe: the proof of LAW job_notice_entry_refuses
#
# PROOF: the entry answers either a notice, which opens with a digit (never
# 'E'), or the one error form; so an answer that opens with 'E' is that
# error form.

import Base
import ../../bend/job_notice.bend as JN
import ../../laws/job_notice.bend as JobNotice
import ../../bend/ffi_job_notice.bend as FJn
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ./base.bend as LA

def jre.notice_ok(n: JN.Notice) -> {LawsBase.wire_opens_err(FJn.put_notice(n)) == False{} : Bool}:
  match n:
    case JN.Drops{}:
      {==}
    case JN.Wakes{}:
      {==}

def jre.answer_ok(q: FJn.Req) -> {LawsBase.wire_opens_err(FJn.answer(q)) == False{} : Bool}:
  match q:
    case FJn.Req{by, t}:
      jre.notice_ok(JN.notice(by, t))

def jre.refuse(d: Wr.Dec<FJn.Req>, bad: {LawsBase.wire_opens_err(FJn.ffi.got(d)) == True{} : Bool}) -> {FJn.ffi.got(d) == Wr.err("job_notice: malformed request") : String}:
  match d:
    case Wr.Got{+q, rest}:
      match rest:
        case SNil{}:
          LA.jnb.absurd_tf({FJn.answer(q) == Wr.err("job_notice: malformed request") : String}, Equal.trans(Bool, True{}, LawsBase.wire_opens_err(FJn.answer(q)), False{}, Equal.sym(Bool, LawsBase.wire_opens_err(FJn.answer(q)), True{}, bad), jre.answer_ok(q)))
        case SCon{x, y}:
          {==}
    case Wr.Bad{}:
      {==}

def JobNotice.job_notice_entry_refuses(s, bad):
  jre.refuse(FJn.get_req(s), bad)
