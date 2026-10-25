# eukhe: the proof of LAW tiny_run_entry_open_refuses
#
# PROOF: the entry opens either the run of an open read whole, whose
# first reply never opens with 'E' (tre.reply_ok), or the refused state
# with the one error form; so an answer that opens with 'E' is that.

import Base
import ../../bend/tiny.bend as Tn
import ../../bend/ffi_tiny_run.bend as FTr
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/tiny/run.bend as TinyRun
import ./base.bend as LA
import ./base/run_entry.bend as LTre

def trf.of_ok(o: FTr.Open) -> {LawsBase.wire_opens_err(TinyRun.tr_snd(FTr.open.of(o))) == False{} : Bool}:
  match o:
    case FTr.ONeed{m}:
      LTre.tre.reply_ok(Tn.need(m))
    case FTr.OSeat{}:
      LTre.tre.reply_ok(Tn.seat())

def trf.refuse(d: Wr.Dec<FTr.Open>, bad: {LawsBase.wire_opens_err(TinyRun.tr_snd(FTr.open.got(d))) == True{} : Bool}) -> {FTr.open.got(d) == (FTr.Refused{}, Wr.err("tiny_run: malformed open")) : FTr.St & String}:
  match d:
    case Wr.Got{+o, rest}:
      match rest:
        case SNil{}:
          LA.te.tf({FTr.open.of(o) == (FTr.Refused{}, Wr.err("tiny_run: malformed open")) : FTr.St & String}, Equal.trans(Bool, True{}, LawsBase.wire_opens_err(TinyRun.tr_snd(FTr.open.of(o))), False{}, Equal.sym(Bool, LawsBase.wire_opens_err(TinyRun.tr_snd(FTr.open.of(o))), True{}, bad), trf.of_ok(o)))
        case SCon{c, y}:
          {==}
    case Wr.Bad{}:
      {==}

def TinyRun.tiny_run_entry_open_refuses(s, bad):
  trf.refuse(FTr.get_open(s), bad)
