# eukhe: the proof of LAW tiny_run_entry_refuses
#
# PROOF: the entry answers either the reply of an outcome read whole,
# which never opens with 'E' (tre.reply_ok), or the one error form with
# the run kept; so an answer that opens with 'E' is that error form.

import Base
import ../../bend/tiny.bend as Tn
import ../../bend/ffi_tiny_run.bend as FTr
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/tiny/run.bend as TinyRun
import ./base.bend as LA
import ./base/run_entry.bend as LTre

def trr.refuse(+x: Tn.Run, d: Wr.Dec<Tn.Seen>, bad: {LawsBase.wire_opens_err(TinyRun.tr_snd(FTr.step.got(x, d))) == True{} : Bool}) -> {FTr.step.got(x, d) == (FTr.Live{x}, Wr.err("tiny_run: malformed event")) : FTr.St & String}:
  match d:
    case Wr.Got{+e, rest}:
      match rest:
        case SNil{}:
          LA.te.tf({FTr.reply(Tn.step_run(x, e)) == (FTr.Live{x}, Wr.err("tiny_run: malformed event")) : FTr.St & String}, Equal.trans(Bool, True{}, LawsBase.wire_opens_err(TinyRun.tr_snd(FTr.reply(Tn.step_run(x, e)))), False{}, Equal.sym(Bool, LawsBase.wire_opens_err(TinyRun.tr_snd(FTr.reply(Tn.step_run(x, e)))), True{}, bad), LTre.tre.reply_ok(Tn.step_run(x, e))))
        case SCon{c, y}:
          {==}
    case Wr.Bad{}:
      {==}

def TinyRun.tiny_run_entry_refuses(x, s, bad):
  trr.refuse(x, FTr.get_seen(s), bad)
