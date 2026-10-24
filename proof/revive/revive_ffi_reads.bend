# eukhe: the proof of LAW revive_ffi_reads
# The entry reads every input as the spec's reader does (LRv.rvb.failed);
# where that reader finds one whole request, the entry puts the veto on its
# facts, which is the spec's reply (LRv.rvb.reply).

import Base
import ../../bend/ffi_revive.bend as FR
import ../../bend/revive.bend as Rv
import ../../bend/wire.bend as Wr
import ../../laws/revive.bend as Revive
import ./base.bend as LRv

def rfr.end(b: Bool, +g: Rv.Facts, -f: Rv.Facts, got: {Revive.rv_read.end(b, g) == Some{f} : Maybe<&2, Rv.Facts>}) -> {FR.ffi.fin(b, g) == Revive.rv_reply(f) : String}:
  match b:
    case True{}:
      %LRv.rvb.some_inj(g, f, got) : {FR.put_veto(Rv.veto(g)) == Revive.rv_reply(_) : String}
      LRv.rvb.reply(g)
    case False{}:
      LRv.rvb.none_some(Rv.Facts, f, {FR.ffi.fin(False{}, g) == Revive.rv_reply(f) : String}, got)

def rfr.whole(r: Wr.Dec<Rv.Facts>, -f: Rv.Facts, got: {Revive.rv_read.whole(r) == Some{f} : Maybe<&2, Rv.Facts>}) -> {FR.ffi.go(r) == Revive.rv_reply(f) : String}:
  match r:
    case Wr.Got{g, s}:
      rfr.end(Wr.end(s), g, f, got)
    case Wr.Bad{}:
      LRv.rvb.none_some(Rv.Facts, f, {FR.ffi.go(Wr.Bad{}) == Revive.rv_reply(f) : String}, got)

def Revive.revive_ffi_reads(s, f, got):
  %LRv.rvb.failed(Wr.get_bool(s)) : {FR.ffi.go(_) == Revive.rv_reply(f) : String}
  rfr.whole(Revive.rv_read.failed(Wr.get_bool(s)), f, got)
