# eukhe: the proof of LAW overflow_message_needs_pattern
#
# PROOF: the code's message test is its strict form (LA.ovb.message), whose overflow arm and Cerebras arm the premises make false, so the test is false whatever its other conjuncts (onp.pick).

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

def onp.pick(e: Bool, c: Bool) -> {Bool.and(e, Bool.and(c, Bool.or(False{}, False{}))) == False{} : Bool}:
  match e:
    case True{}:
      match c:
        case True{}:
          {==}
        case False{}:
          {==}
    case False{}:
      {==}

def Overflow.overflow_message_needs_pattern(msg, provider, ho, hx):
  +f = TextPat.sp_fold(msg)
  %Equal.sym(Bool, O.message_overflow(msg, provider), LA.ovb.strict(msg, provider), LA.ovb.message(msg, provider)) : {_ == False{} : Bool}
  %Equal.sym(Bool, TextPat.sp_any(f, Overflow.sp_overflow_pats()), False{}, ho) : {Bool.and(Bool.not(String.is_empty(msg)), Bool.and(Bool.not(TextPat.sp_any(f, Overflow.sp_calm_pats())), Bool.or(_, Bool.and(String.eq(provider, "cerebras"), TextPat.sp_any(f, [Overflow.sp_cerebras()]))))) == False{} : Bool}
  %Equal.sym(Bool, Bool.and(String.eq(provider, "cerebras"), TextPat.sp_any(f, [Overflow.sp_cerebras()])), False{}, hx) : {Bool.and(Bool.not(String.is_empty(msg)), Bool.and(Bool.not(TextPat.sp_any(f, Overflow.sp_calm_pats())), Bool.or(False{}, _))) == False{} : Bool}
  onp.pick(Bool.not(String.is_empty(msg)), Bool.not(TextPat.sp_any(f, Overflow.sp_calm_pats())))
