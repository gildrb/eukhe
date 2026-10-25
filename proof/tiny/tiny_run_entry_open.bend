# eukhe: the proof of LAW tiny_run_entry_open
#
# PROOF: the spelled open reads back whole with nothing left (tre.open),
# so the entry opens the model's run of it (Tn.need, Tn.seat compute to
# the spec's sp_open) and spells its first reply as the spec does
# (tre.reply).

import Base
import ../../bend/tiny.bend as Tn
import ../../bend/ffi_tiny_run.bend as FTr
import ../../bend/wire.bend as Wr
import ../../laws/tiny/run.bend as TinyRun
import ./base/run_entry.bend as LTre

def tro.of(o: FTr.Open) -> {FTr.open.of(o) == TinyRun.sp_reply(TinyRun.sp_open(o)) : FTr.St & String}:
  match o:
    case FTr.ONeed{m}:
      LTre.tre.reply(Tn.need(m))
    case FTr.OSeat{}:
      LTre.tre.reply(Tn.seat())

def TinyRun.tiny_run_entry_open(o, h):
  %Equal.sym(Wr.Dec<FTr.Open>, FTr.get_open(TinyRun.sp_w_open(o, "")), Wr.Got{o, ""}, LTre.tre.open(o, "", h)) : {FTr.open.got(_) == TinyRun.sp_reply(TinyRun.sp_open(o)) : FTr.St & String}
  tro.of(o)
