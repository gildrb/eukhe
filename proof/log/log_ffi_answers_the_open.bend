# eukhe: the proof of LAW log_ffi_answers_the_open
#
# The length reads back (the wire's Nat round trip), then the last newline
# (pl.last_rt), nothing is left, and the entry spells the rule's decision
# as the spec does (pl.tail_spell).

import Base
import ../../bend/log.bend as Lr
import ../../bend/wire.bend as Wr
import ../../bend/ffi_log.bend as FLg
import ../../laws/base.bend as LawsBase
import ../../laws/log.bend as Log
import ../base/logic/bool.bend as LLogicBool
import ../base/wire.bend as LWire

def pl.last_rt(last: Maybe<&2, Nat>, h: {Log.log_last_fits(last) == True{} : Bool}) -> {Wr.Got{last, ""} == FLg.get_last(Log.log_spell_last(last, "")) : Wr.Dec<Maybe<&2, Nat>>}:
  match last:
    case None{}:
      {==}
    case Some{+i}:
      %LWire.pc.nat(i, "", h) : {Wr.Got{Some{i}, ""} == FLg.get_last.some(_) : Wr.Dec<Maybe<&2, Nat>>}
      {==}

def pl.tail_spell(t: Lr.Tail) -> {FLg.put_tail(t, "") == Log.log_spell_tail(t) : String}:
  match t:
    case Lr.Whole{}:
      {==}
    case Lr.Torn{to}:
      {==}
    case Lr.Odd{}:
      {==}

def Log.log_ffi_answers_the_open(len, last, fits):
  +f = fits
  +hl = LLogicBool.wr_and_l(LawsBase.wire_fits(len), Log.log_last_fits(last), f)
  +hm = LLogicBool.wr_and_r(LawsBase.wire_fits(len), Log.log_last_fits(last), f)
  %LWire.pc.nat(len, Log.log_spell_last(last, ""), hl) : {FLg.ffi.go(FLg.get_req.len(_)) == Log.log_spell_tail(Lr.tail(len, last)) : String}
  %pl.last_rt(last, hm) : {FLg.ffi.go(FLg.get_req.last(len, _)) == Log.log_spell_tail(Lr.tail(len, last)) : String}
  %pl.tail_spell(Lr.tail(len, last)) : {FLg.put_tail(Lr.tail(len, last), "") == _ : String}
  {==}
