# eukhe: the proof of LAW selection_ffi_left_over_exact: the left-over
# error form comes only from an event the decoder read with input after
# it; what it read is spelled and fits (ro.ev of
# selection_ffi_reads_only_events). A malformed input answers another
# text, and a whole event the model's answer, never an error form
# (se.res_ok).

import Base
import ../../bend/selection.bend as M
import ../../bend/ffi_selection.bend as F
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/selection.bend as Selection
import ../../laws/selection/reply.bend as SelectionReply
import ./base.bend as LS
import ./base/errors.bend as LSE
import ./selection_ffi_reads_only_events.bend as RO

def se.lo(d: Wr.Dec<M.Ev>, +s: M.St, -str: String, p: RO.ro.Pev(str, d), e: {Pair.snd(F.St, String, F.step.ev(s, d)) == Wr.err("selection: input left over") : String}) -> Sigma<&1, &1, SelectionReply.SlLeftOver, w => {str == SelectionReply.sl_spell_left_over(w) : String} & {Selection.sl_ev_fits(SelectionReply.sl_left_ev(w)) == True{} : Bool}>:
  match d:
    case Wr.Bad{}:
      LS.ls.absurd(Sigma<&1, &1, SelectionReply.SlLeftOver, w => {str == SelectionReply.sl_spell_left_over(w) : String} & {Selection.sl_ev_fits(SelectionReply.sl_left_ev(w)) == True{} : Bool}>, Equal.cong(String, Bool, z => LawsBase.text_same(z, Wr.err("selection: input left over")), Wr.err("selection: malformed event"), Wr.err("selection: input left over"), e))
    case Wr.Got{+ev, r}:
      match r:
        case SNil{}:
          +x = Pair.snd(F.St, String, F.step.res(M.step(s, ev)))
          LS.ls.absurd(Sigma<&1, &1, SelectionReply.SlLeftOver, w => {str == SelectionReply.sl_spell_left_over(w) : String} & {Selection.sl_ev_fits(SelectionReply.sl_left_ev(w)) == True{} : Bool}>, Equal.trans(Bool, False{}, LawsBase.wire_opens_err(x), True{}, Equal.sym(Bool, LawsBase.wire_opens_err(x), False{}, LSE.se.res_ok(M.step(s, ev))), Equal.cong(String, Bool, z => LawsBase.wire_opens_err(z), x, Wr.err("selection: input left over"), e)))
        case SCon{+h, +t}:
          (SelectionReply.SlLeftOver{ev, h, t}, p)

def SelectionReply.selection_ffi_left_over_exact(s, str, e):
  se.lo(F.get_ev(str), s, str, RO.ro.ev(str, Wr.get_nat(str), RO.ro.nat(str)), e)
