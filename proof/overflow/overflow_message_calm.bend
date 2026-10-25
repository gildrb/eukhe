# eukhe: the proof of LAW overflow_message_calm
#
# PROOF: the code's message test is the spec's (LA.ovb.message), whose
# second conjunct is false when a calm pattern is found.

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

def omc.BD(b: Bool, t: Type, f: Type) -> Type:
  match b:
    case True{}:
      t
    case False{}:
      f

def omc.absurd(-A: Type, e: {False{} == True{} : Bool}) -> A:
  %e : omc.BD(_, A, Unit)
  Unit{}

def omc.calm(c: Bool, e: Bool, -o: Bool, hc: {c == True{} : Bool}) -> {Bool.and(Bool.not(e), Bool.and(Bool.not(c), o)) == False{} : Bool}:
  match c:
    case True{}:
      LA.ovb.and_false(Bool.not(e))
    case False{}:
      omc.absurd({Bool.and(Bool.not(e), Bool.and(Bool.not(False{}), o)) == False{} : Bool}, hc)

def Overflow.overflow_message_calm(msg, provider, hc):
  +f = TextPat.sp_fold(msg)
  %Equal.sym(Bool, O.message_overflow(msg, provider), Overflow.sp_message(msg, provider), LA.ovb.message(msg, provider)) : {_ == False{} : Bool}
  omc.calm(TextPat.sp_any(f, Overflow.sp_calm_pats()), String.is_empty(msg), Bool.or(TextPat.sp_any(f, Overflow.sp_overflow_pats()), Bool.and(String.eq(provider, "cerebras"), TextPat.sp_any(f, [Overflow.sp_cerebras()]))), hc)
