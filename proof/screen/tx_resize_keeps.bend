# eukhe: the proof of LAW tx_resize_keeps

import Base
import ../../bend/screen.bend as Sc
import ../../LAWS.bend as Laws

def ps.tx_resize_keeps(+t: Sc.Tx, +w: Nat) -> {Sc.Tx.blocks(Sc.step(t, Sc.Resize{w})) == Sc.Tx.blocks(t) : List<&2, Sc.Blk>}:
  match t:
    case Sc.Tx{bs, n, v}:
      {==}

def Laws.tx_resize_keeps(t, w):
  ps.tx_resize_keeps(t, w)
