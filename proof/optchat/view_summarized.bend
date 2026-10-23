# eukhe: the proof of LAW view_summarized

import Base
import ../../bend/optchat.bend as O
import ../../bend/spec.bend as S
import ../../laws/optchat.bend as Optchat
import ./base.bend as LA

def view_summarized(+cfg: O.Cfg, +evs: List<&2, O.Ev>) -> S.Summarized(O.St.info(O.run(cfg, evs)), S.view.of(cfg, evs)):
  Pair.fst(S.Summarized(O.St.info(O.run(cfg, evs)), S.view.of(cfg, evs)), S.Summarized(O.St.info(O.run(cfg, evs)), S.cview.of(cfg, evs)), LA.pf.run_summ(cfg, evs))

def Optchat.view_summarized(cfg, evs):
  view_summarized(cfg, evs)
