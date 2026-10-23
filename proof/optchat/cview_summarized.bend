# eukhe: the proof of LAW cview_summarized

import Base
import ../../bend/optchat.bend as O
import ../../bend/spec.bend as S
import ../../laws/optchat.bend as Optchat
import ./base.bend as LA

def cview_summarized(+cfg: O.Cfg, +evs: List<&2, O.Ev>) -> S.Summarized(O.St.info(O.run(cfg, evs)), S.cview.of(cfg, evs)):
  Pair.snd(S.Summarized(O.St.info(O.run(cfg, evs)), S.view.of(cfg, evs)), S.Summarized(O.St.info(O.run(cfg, evs)), S.cview.of(cfg, evs)), LA.pf.run_summ(cfg, evs))

def Optchat.cview_summarized(cfg, evs):
  cview_summarized(cfg, evs)
