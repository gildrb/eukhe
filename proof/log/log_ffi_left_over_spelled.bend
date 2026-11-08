# eukhe: the proof of LAW log_ffi_left_over_spelled
#
# The length reads back (the wire's Nat round trip), then the last newline
# (llo.last_rt), the rest untouched; the end check sees the char left and
# answers the left-over error.

import Base
import ../../bend/wire.bend as Wr
import ../../bend/ffi_log.bend as FLg
import ../../laws/base.bend as LawsBase
import ../../laws/log.bend as Log
import ../base/logic/bool.bend as LLogicBool
import ../base/wire.bend as LWire

# a last newline that fits reads back, the rest untouched
def llo.last_rt(last: Maybe<&2, Nat>, +rest: String, h: {Log.log_last_fits(last) == True{} : Bool}) -> {Wr.Got{last, rest} == FLg.get_last(Log.log_spell_last(last, rest)) : Wr.Dec<Maybe<&2, Nat>>}:
  match last:
    case None{}:
      {==}
    case Some{+i}:
      %LWire.pc.nat(i, rest, h) : {Wr.Got{Some{i}, rest} == FLg.get_last.some(_) : Wr.Dec<Maybe<&2, Nat>>}
      {==}

def Log.log_ffi_left_over_spelled(len, last, fits, c, t):
  +f = fits
  +hl = LLogicBool.wr_and_l(LawsBase.wire_fits(len), Log.log_last_fits(last), f)
  +hm = LLogicBool.wr_and_r(LawsBase.wire_fits(len), Log.log_last_fits(last), f)
  %LWire.pc.nat(len, Log.log_spell_last(last, SCon{c, t}), hl) : {FLg.ffi.go(FLg.get_req.len(_)) == Wr.err("log: input left over") : String}
  %llo.last_rt(last, SCon{c, t}, hm) : {FLg.ffi.go(FLg.get_req.last(len, _)) == Wr.err("log: input left over") : String}
  {==}
