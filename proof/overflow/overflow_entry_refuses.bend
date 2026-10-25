# eukhe: the proof of LAW overflow_entry_refuses
#
# PROOF: the entry answers either a Bool (T or F, never 'E') or the one
# error form; so an answer that opens with 'E' is that error form.

import Base
import ../../bend/text_pat.bend as Tp
import ../../bend/overflow.bend as O
import ../../bend/ffi_overflow.bend as FO
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../../laws/text_pat.bend as TextPat
import ../../laws/overflow.bend as Overflow
import ../base/staging.bend as LStg

def ovf.bool_ok(b: Bool) -> {LawsBase.wire_opens_err(Wr.put_bool(b, "")) == False{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def ovf.answer_ok(q: FO.Req) -> {LawsBase.wire_opens_err(FO.answer(q)) == False{} : Bool}:
  match q:
    case FO.QOverflow{st, m, p, w, i, c, o}:
      ovf.bool_ok(O.overflow(st, m, p, w, i, c, o))
    case FO.QRecoverable{st, d, o}:
      ovf.bool_ok(O.recoverable(st, d, o))

def ovf.refuse(d: Wr.Dec<FO.Req>, bad: {LawsBase.wire_opens_err(FO.ffi.got(d)) == True{} : Bool}) -> {FO.ffi.got(d) == Wr.err("overflow: malformed request") : String}:
  match d:
    case Wr.Got{+q, rest}:
      match rest:
        case SNil{}:
          LStg.stg.absurd({FO.answer(q) == Wr.err("overflow: malformed request") : String}, Equal.trans(Bool, True{}, LawsBase.wire_opens_err(FO.answer(q)), False{}, Equal.sym(Bool, LawsBase.wire_opens_err(FO.answer(q)), True{}, bad), ovf.answer_ok(q)))
        case SCon{x, y}:
          {==}
    case Wr.Bad{}:
      {==}

def Overflow.overflow_entry_refuses(s, bad):
  ovf.refuse(FO.get_req(s), bad)
