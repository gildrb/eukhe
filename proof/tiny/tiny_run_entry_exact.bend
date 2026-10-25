# eukhe: the proof of LAW tiny_run_entry_exact
#
# PROOF: the outcome decoder answers Got{e, rest} only for an input that
# is the spec's spelling of e before rest, with e within the wire
# (tx.seen); the entry answers a reply, not the error form, only for an
# outcome read whole with nothing left: that input is the spelled
# outcome.

import Base
import ../../bend/tiny.bend as Tn
import ../../bend/ffi_tiny_run.bend as FTr
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/tiny/run.bend as TinyRun
import ./base.bend as LA
import ./base/run_entry.bend as LTre

def trx.top(+x: Tn.Run, -s: String, d: Wr.Dec<Tn.Seen>, ep: LTre.tx.EP(s, d), ok: {LawsBase.wire_opens_err(TinyRun.tr_snd(FTr.step.got(x, d))) == False{} : Bool}) -> Sigma<&1, &1, Tn.Seen, e => {s == TinyRun.sp_w_seen(e, "") : String} & {TinyRun.sp_fit_seen(e) == True{} : Bool}>:
  match d:
    case Wr.Got{+e, rest}:
      match rest:
        case SNil{}:
          (e, ep)
        case SCon{c, y}:
          LA.te.tf(Sigma<&1, &1, Tn.Seen, e2 => {s == TinyRun.sp_w_seen(e2, "") : String} & {TinyRun.sp_fit_seen(e2) == True{} : Bool}>, ok)
    case Wr.Bad{}:
      LA.te.tf(Sigma<&1, &1, Tn.Seen, e2 => {s == TinyRun.sp_w_seen(e2, "") : String} & {TinyRun.sp_fit_seen(e2) == True{} : Bool}>, ok)

def TinyRun.tiny_run_entry_exact(x, s, ok):
  trx.top(x, s, FTr.get_seen(s), LTre.tx.seen(s), ok)
