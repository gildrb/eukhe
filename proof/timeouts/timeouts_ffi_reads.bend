# eukhe: the proof of LAW timeouts_ffi_reads
# The entry reads every input as the laws' reader does (LTm.tmo.read.snap);
# where that reader finds one whole request, the entry answers the laws'
# reply (LTm.tmo.answer).

import Base
import ../../bend/ffi_timeouts.bend as FT
import ../../bend/supervise.bend as Su
import ../../bend/wire.bend as Wr
import ../../laws/timeouts.bend as Timeouts
import ./base.bend as LTm

# the answer to u, when Some{u} is m
def tfr.at(u: Su.Tm, m: Maybe<&2, Su.Tm>) -> Type:
  match m:
    case None{}:
      Unit
    case Some{x}:
      {FT.answer(u) == Timeouts.tw_reply(x) : String}

def tfr.end(b: Bool, +u: Su.Tm, +t: Su.Tm, got: {Timeouts.tw_read.end(b, u) == Some{t} : Maybe<&2, Su.Tm>}) -> {FT.ffi.fin(b, u) == Timeouts.tw_reply(t) : String}:
  match b:
    case True{}:
      %got : tfr.at(u, _)
      LTm.tmo.answer(u)
    case False{}:
      LTm.tmo.none_some(Su.Tm, t, {FT.ffi.fin(False{}, u) == Timeouts.tw_reply(t) : String}, got)

def tfr.whole(r: Wr.Dec<Su.Tm>, +t: Su.Tm, got: {Timeouts.tw_read.whole(r) == Some{t} : Maybe<&2, Su.Tm>}) -> {FT.ffi.go(r) == Timeouts.tw_reply(t) : String}:
  match r:
    case Wr.Got{u, s}:
      tfr.end(Wr.end(s), u, t, got)
    case Wr.Bad{}:
      LTm.tmo.none_some(Su.Tm, t, {FT.ffi.go(Wr.Bad{}) == Timeouts.tw_reply(t) : String}, got)

def Timeouts.timeouts_ffi_reads(s, t, got):
  %LTm.tmo.read.snap(Wr.get_nat(s)) : {FT.ffi.go(_) == Timeouts.tw_reply(t) : String}
  tfr.whole(Timeouts.tw_read.snap(Wr.get_nat(s)), t, got)
