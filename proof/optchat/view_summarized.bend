# eukhe: the proof of LAW view_summarized

import Base
import ../../bend/optchat/state.bend as OState
import ../../bend/optchat/step.bend as OStep
import ../../spec/memory/optchat.bend as S
import ../../laws/optchat.bend as Optchat
import ./base/step.bend as LA

def view_summarized(+cfg: OState.Cfg, +evs: List<&2, OState.Ev>) -> S.Summarized(OState.St.info(OStep.run(cfg, evs)), S.view.of(cfg, evs)):
  Pair.fst(S.Summarized(OState.St.info(OStep.run(cfg, evs)), S.view.of(cfg, evs)), S.Summarized(OState.St.info(OStep.run(cfg, evs)), S.cview.of(cfg, evs)), LA.pf.run_summ(cfg, evs))

def Optchat.view_summarized(cfg, evs):
  view_summarized(cfg, evs)
