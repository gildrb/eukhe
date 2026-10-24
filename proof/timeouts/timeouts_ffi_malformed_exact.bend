# eukhe: the proof of LAW timeouts_ffi_malformed_exact
# The entry reads every input as the laws' reader does (LTm.tmo.read.snap);
# where that reader finds no whole request, the entry answers its error
# form.

import Base
import ../../bend/ffi_timeouts.bend as FT
import ../../bend/supervise.bend as Su
import ../../bend/wire.bend as Wr
import ../../laws/timeouts.bend as Timeouts
import ./base.bend as LTm

def tfm.end(b: Bool, -u: Su.Tm, no: {Timeouts.tw_read.end(b, u) == None{} : Maybe<&2, Su.Tm>}) -> {FT.ffi.fin(b, u) == SCon{'E', SCon{' ', "timeouts: malformed request"}} : String}:
  match b:
    case True{}:
      LTm.tmo.some_none(Su.Tm, u, {FT.ffi.fin(True{}, u) == SCon{'E', SCon{' ', "timeouts: malformed request"}} : String}, no)
    case False{}:
      {==}

def tfm.whole(r: Wr.Dec<Su.Tm>, no: {Timeouts.tw_read.whole(r) == None{} : Maybe<&2, Su.Tm>}) -> {FT.ffi.go(r) == SCon{'E', SCon{' ', "timeouts: malformed request"}} : String}:
  match r:
    case Wr.Got{u, s}:
      tfm.end(Wr.end(s), u, no)
    case Wr.Bad{}:
      {==}

def Timeouts.timeouts_ffi_malformed_exact(s, no):
  %LTm.tmo.read.snap(Wr.get_nat(s)) : {FT.ffi.go(_) == SCon{'E', SCon{' ', "timeouts: malformed request"}} : String}
  tfm.whole(Timeouts.tw_read.snap(Wr.get_nat(s)), no)
