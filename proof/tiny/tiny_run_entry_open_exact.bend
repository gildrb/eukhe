# eukhe: the proof of LAW tiny_run_entry_open_exact
#
# PROOF: the open decoder answers Got{o, rest} only for an input that is
# the spec's spelling of o before rest, with o within the wire
# (tx.open); the entry opens a run, not the refused state, only for an
# open read whole with nothing left: that input is the spelled open.

import Base
import ../../bend/tiny.bend as Tn
import ../../bend/ffi_tiny_run.bend as FTr
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/tiny/run.bend as TinyRun
import ./base.bend as LA
import ./base/run_entry.bend as LTre

def trq.top(-s: String, d: Wr.Dec<FTr.Open>, op: LTre.tx.OP(s, d), ok: {LawsBase.wire_opens_err(TinyRun.tr_snd(FTr.open.got(d))) == False{} : Bool}) -> Sigma<&1, &1, FTr.Open, o => {s == TinyRun.sp_w_open(o, "") : String} & {TinyRun.sp_fit_open(o) == True{} : Bool}>:
  match d:
    case Wr.Got{+o, rest}:
      match rest:
        case SNil{}:
          (o, op)
        case SCon{c, y}:
          LA.te.tf(Sigma<&1, &1, FTr.Open, o2 => {s == TinyRun.sp_w_open(o2, "") : String} & {TinyRun.sp_fit_open(o2) == True{} : Bool}>, ok)
    case Wr.Bad{}:
      LA.te.tf(Sigma<&1, &1, FTr.Open, o2 => {s == TinyRun.sp_w_open(o2, "") : String} & {TinyRun.sp_fit_open(o2) == True{} : Bool}>, ok)

def TinyRun.tiny_run_entry_open_exact(s, ok):
  trq.top(s, FTr.get_open(s), LTre.tx.open(s), ok)
