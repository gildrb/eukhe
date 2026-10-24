# eukhe: the proof of LAW revive_ffi_malformed_exact
# The entry reads every input as the spec's reader does (LRv.rvb.failed);
# where that reader finds no whole request, the entry answers its error
# form.

import Base
import ../../bend/ffi_revive.bend as FR
import ../../bend/revive.bend as Rv
import ../../bend/wire.bend as Wr
import ../../laws/revive.bend as Revive
import ./base.bend as LRv

def rfm.end(b: Bool, -g: Rv.Facts, no: {Revive.rv_read.end(b, g) == None{} : Maybe<&2, Rv.Facts>}) -> {FR.ffi.fin(b, g) == SCon{'E', SCon{' ', "revive: malformed request"}} : String}:
  match b:
    case True{}:
      LRv.rvb.some_none(Rv.Facts, g, {FR.ffi.fin(True{}, g) == SCon{'E', SCon{' ', "revive: malformed request"}} : String}, no)
    case False{}:
      {==}

def rfm.whole(r: Wr.Dec<Rv.Facts>, no: {Revive.rv_read.whole(r) == None{} : Maybe<&2, Rv.Facts>}) -> {FR.ffi.go(r) == SCon{'E', SCon{' ', "revive: malformed request"}} : String}:
  match r:
    case Wr.Got{g, s}:
      rfm.end(Wr.end(s), g, no)
    case Wr.Bad{}:
      {==}

def Revive.revive_ffi_malformed_exact(s, no):
  %LRv.rvb.failed(Wr.get_bool(s)) : {FR.ffi.go(_) == SCon{'E', SCon{' ', "revive: malformed request"}} : String}
  rfm.whole(Revive.rv_read.failed(Wr.get_bool(s)), no)
