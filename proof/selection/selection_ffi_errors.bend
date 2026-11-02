# eukhe: the proof of LAW selection_ffi_errors: a live stepper answers the
# malformed error form (the decoder failed), the left-over error form
# (input after the event), or the model's answer, which never opens with
# 'E' (se.res_ok)

import Base
import ../../bend/selection.bend as M
import ../../bend/ffi_selection.bend as F
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/selection/reply.bend as SelectionReply
import ./base.bend as LS
import ./base/errors.bend as LSE

def se.errs(d: Wr.Dec<M.Ev>, +s: M.St, e: {LawsBase.wire_opens_err(Pair.snd(F.St, String, F.step.ev(s, d))) == True{} : Bool}) -> {Bool.or(LawsBase.text_same(Pair.snd(F.St, String, F.step.ev(s, d)), Wr.err("selection: malformed event")), LawsBase.text_same(Pair.snd(F.St, String, F.step.ev(s, d)), Wr.err("selection: input left over"))) == True{} : Bool}:
  match d:
    case Wr.Bad{}:
      {==}
    case Wr.Got{+ev, r}:
      match r:
        case SNil{}:
          +x = Pair.snd(F.St, String, F.step.res(M.step(s, ev)))
          LS.ls.absurd({Bool.or(LawsBase.text_same(x, Wr.err("selection: malformed event")), LawsBase.text_same(x, Wr.err("selection: input left over"))) == True{} : Bool}, Equal.trans(Bool, False{}, LawsBase.wire_opens_err(x), True{}, Equal.sym(Bool, LawsBase.wire_opens_err(x), False{}, LSE.se.res_ok(M.step(s, ev))), e))
        case SCon{h, t}:
          {==}

def SelectionReply.selection_ffi_errors(s, str, e):
  se.errs(F.get_ev(str), s, e)
