# eukhe: the proof of LAW work_entry_reads_only_events
#
# PROOF: whatever the decoder reads is a spelled event that fits, then its
# rest (wre.ev); a step answered other than with the error form read an
# event whole, nothing left (wro.fin).

import Base
import ../../bend/ffi_work.bend as FW
import ../../bend/progress.bend as Pr
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/work.bend as Work
import ../wire/base/spell.bend as LAWireSpell
import ./base/exact.bend as LAWorkExact

def wro.G(s: String) -> Type:
  &e: Pr.Ev -> {(s, Work.wk_ev_fits(e)) == (Work.wk_spell_ev(e, ""), True{}) : String & Bool}

def wro.top(-s: String, +e: Pr.Ev, eq: {s == Work.wk_spell_ev(e, "") : String}, f: {Work.wk_ev_fits(e) == True{} : Bool}) -> {(s, Work.wk_ev_fits(e)) == (Work.wk_spell_ev(e, ""), True{}) : String & Bool}:
  %eq : {(s, Work.wk_ev_fits(e)) == (_, True{}) : String & Bool}
  %f : {(s, Work.wk_ev_fits(e)) == (s, _) : String & Bool}
  {==}

def wro.fin(+s: String, +l: Pr.Led, +e: Pr.Ev, r: String, pre: {s == Work.wk_spell_ev(e, r) : String}, f: {Work.wk_ev_fits(e) == True{} : Bool}, ok: {LawsBase.wire_opens_err(Work.wk_reply(FW.step.end(Wr.end(r), l, e))) == False{} : Bool}) -> wro.G(s):
  match r:
    case SNil{}:
      (e, wro.top(s, e, pre, f))
    case SCon{c, t}:
      LAWireSpell.ws_absurd(wro.G(s), ok)

def wro.main(+s: String, +l: Pr.Led, d: Wr.Dec<Pr.Ev>, inv: LAWorkExact.wre.VP(s, d), ok: {LawsBase.wire_opens_err(Work.wk_reply(FW.step.ev(l, d))) == False{} : Bool}) -> wro.G(s):
  match d:
    case Wr.Got{+e, +r}:
      (eq, f) = inv
      wro.fin(s, l, e, r, eq, f, ok)
    case Wr.Bad{}:
      LAWireSpell.ws_absurd(wro.G(s), ok)

def Work.work_entry_reads_only_events(l, s, ok):
  wro.main(s, l, FW.get_ev(s), LAWorkExact.wre.ev(s), ok)
