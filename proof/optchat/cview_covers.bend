# eukhe: the proof of LAW cview_covers

import Base
import ../../bend/optchat.bend as O
import ../../bend/spec.bend as S
import ../../LAWS.bend as Laws
import ./base.bend as LA

def cover.inv_cview(-s: O.St, inv: LA.cover.Inv(s)) -> S.Tiles(0n, O.St.cview(s), O.Bits.val(O.St.t(s))):
  (a, b) = inv
  b

def cview_covers(+cfg: O.Cfg, +evs: List<&2, O.Ev>) -> S.Tiles(0n, S.cview.of(cfg, evs), S.total.of(cfg, evs)):
  cover.inv_cview(O.run(cfg, evs), LA.cover.all(cfg, evs))

def Laws.cview_covers(cfg, evs):
  cview_covers(cfg, evs)
