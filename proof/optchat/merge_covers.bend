# eukhe: the proof of LAW merge_covers

import Base
import ../../bend/optchat.bend as O
import ../../bend/spec.bend as S
import ../../LAWS.bend as Laws
import ./base.bend as LA

def merge_covers(+info: O.Info, +s: Nat, +v: List<&2, O.Node>, +w: List<&2, O.Node>, +e: Nat, tiles: S.Tiles(s, v, e), merged: S.Merged(info, v, w)) -> S.Tiles(s, w, e):
  LA.cover.merged(v, w, info, s, e, tiles, merged)

def Laws.merge_covers(info, s, v, w, e, tiles, merged):
  merge_covers(info, s, v, w, e, tiles, merged)
