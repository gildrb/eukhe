# eukhe: the proof of LAW overflow_entry_answers
#
# PROOF: the spelled request reads back whole with nothing left
# (overflow_entry_reads), so the entry answers the code's decision, which
# is the spec's (overflow_decides, overflow_recoverable).

import Base
import ../../bend/text_pat.bend as Tp
import ../../bend/overflow.bend as O
import ../../bend/ffi_overflow.bend as FO
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../../laws/text_pat.bend as TextPat
import ../../laws/overflow.bend as Overflow
import ./overflow_decides.bend as POverflowDecides
import ./overflow_recoverable.bend as POverflowRecoverable
import ./overflow_entry_reads.bend as POverflowEntryReads

def ova.reply(q: FO.Req) -> {FO.answer(q) == Overflow.sp_w_reply(q) : String}:
  match q:
    case FO.QOverflow{+st, +m, +p, +w, +i, +c, +o}:
      %Equal.sym(Bool, O.overflow(st, m, p, w, i, c, o), Overflow.sp_overflow(st, m, p, w, i, c, o), Overflow.overflow_decides(st, m, p, w, i, c, o)) : {Wr.put_bool(_, "") == Wr.put_bool(Overflow.sp_overflow(st, m, p, w, i, c, o), "") : String}
      {==}
    case FO.QRecoverable{+st, +d, +o}:
      %Equal.sym(Bool, O.recoverable(st, d, o), Overflow.sp_recoverable(st, d, o), Overflow.overflow_recoverable(st, d, o)) : {Wr.put_bool(_, "") == Wr.put_bool(Overflow.sp_recoverable(st, d, o), "") : String}
      {==}

def Overflow.overflow_entry_answers(q, h):
  %Equal.sym(Wr.Dec<FO.Req>, FO.get_req(Overflow.sp_w_req(q, "")), Wr.Got{q, ""}, Overflow.overflow_entry_reads(q, "", h)) : {FO.ffi.got(_) == Overflow.sp_w_reply(q) : String}
  ova.reply(q)
