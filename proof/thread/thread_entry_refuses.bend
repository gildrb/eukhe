# eukhe: the proof of LAW thread_entry_refuses
#
# PROOF: the entry answers either the count, which opens with a Nat (never
# 'E': wire_nat_not_err), or the one error form; so an answer that opens
# with 'E' is that error form.

import Base
import ../../bend/thread.bend as Th
import ../../bend/ffi_thread.bend as FTh
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../../laws/thread.bend as Thread
import ../wire/wire_nat_not_err.bend as PWireNatNotErr
import ./base.bend as LA

def tef.answer_ok(q: FTh.Req) -> {LawsBase.wire_opens_err(FTh.answer(q)) == False{} : Bool}:
  match q:
    case FTh.Req{t, v, xs}:
      Wire.wire_nat_not_err(Th.history_lines(t, v, xs), "")

def tef.refuse(d: Wr.Dec<FTh.Req>, bad: {LawsBase.wire_opens_err(FTh.ffi.got(d)) == True{} : Bool}) -> {FTh.ffi.got(d) == Wr.err("thread: malformed request") : String}:
  match d:
    case Wr.Got{+q, rest}:
      match rest:
        case SNil{}:
          LA.thb.absurd_tf({FTh.answer(q) == Wr.err("thread: malformed request") : String}, Equal.trans(Bool, True{}, LawsBase.wire_opens_err(FTh.answer(q)), False{}, Equal.sym(Bool, LawsBase.wire_opens_err(FTh.answer(q)), True{}, bad), tef.answer_ok(q)))
        case SCon{x, y}:
          {==}
    case Wr.Bad{}:
      {==}

def Thread.thread_entry_refuses(s, bad):
  tef.refuse(FTh.get_req(s), bad)
