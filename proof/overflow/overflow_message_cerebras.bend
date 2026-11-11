# eukhe: the proof of LAW overflow_message_cerebras
#
# PROOF: the code's message test is its strict form (LA.ovb.message); the premises make the message non-empty, nothing calm and Cerebras' pattern found, and the provider is "cerebras", so the overflow arm or the Cerebras arm holds (ocb.or_true).

import Base
import ../../bend/text_pat.bend as Tp
import ../../bend/overflow.bend as O
import ../../bend/ffi_overflow.bend as FO
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../../laws/text_pat.bend as TextPat
import ../../laws/overflow.bend as Overflow
import ./base.bend as LA

def ocb.or_true(a: Bool) -> {Bool.or(a, True{}) == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

def Overflow.overflow_message_cerebras(msg, hn, hc, hx):
  +f = TextPat.sp_fold(msg)
  %Equal.sym(Bool, O.message_overflow(msg, "cerebras"), LA.ovb.strict(msg, "cerebras"), LA.ovb.message(msg, "cerebras")) : {_ == True{} : Bool}
  %Equal.sym(Bool, String.is_empty(msg), False{}, hn) : {Bool.and(Bool.not(_), Bool.and(Bool.not(TextPat.sp_any(f, Overflow.sp_calm_pats())), Bool.or(TextPat.sp_any(f, Overflow.sp_overflow_pats()), Bool.and(String.eq("cerebras", "cerebras"), TextPat.sp_any(f, [Overflow.sp_cerebras()]))))) == True{} : Bool}
  %Equal.sym(Bool, TextPat.sp_any(f, Overflow.sp_calm_pats()), False{}, hc) : {Bool.and(Bool.not(False{}), Bool.and(Bool.not(_), Bool.or(TextPat.sp_any(f, Overflow.sp_overflow_pats()), Bool.and(String.eq("cerebras", "cerebras"), TextPat.sp_any(f, [Overflow.sp_cerebras()]))))) == True{} : Bool}
  %Equal.sym(Bool, TextPat.sp_any(f, [Overflow.sp_cerebras()]), True{}, hx) : {Bool.and(Bool.not(False{}), Bool.and(Bool.not(False{}), Bool.or(TextPat.sp_any(f, Overflow.sp_overflow_pats()), Bool.and(String.eq("cerebras", "cerebras"), _)))) == True{} : Bool}
  ocb.or_true(TextPat.sp_any(f, Overflow.sp_overflow_pats()))
