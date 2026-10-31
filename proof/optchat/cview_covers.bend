# eukhe: the proof of LAW cview_covers

import Base
import ../../bend/optchat/bits.bend as OBits
import ../../bend/optchat/state.bend as OState
import ../../bend/optchat/step.bend as OStep
import ../../spec/memory/optchat.bend as S
import ../../laws/optchat.bend as Optchat
import ./base/step.bend as LA

def cover.inv_cview(-s: OState.St, inv: LA.cover.Inv(s)) -> S.Tiles(0n, OState.St.cview(s), OBits.Bits.val(OState.St.t(s))):
  (a, b) = inv
  b

def cview_covers(+cfg: OState.Cfg, +evs: List<&2, OState.Ev>) -> S.Tiles(0n, S.cview.of(cfg, evs), S.total.of(cfg, evs)):
  cover.inv_cview(OStep.run(cfg, evs), LA.cover.all(cfg, evs))

def Optchat.cview_covers(cfg, evs):
  cview_covers(cfg, evs)
