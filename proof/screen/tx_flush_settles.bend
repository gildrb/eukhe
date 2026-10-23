# eukhe: the proof of LAW tx_flush_settles

import Base
import ../../bend/screen.bend as Sc
import ../../laws/screen.bend as Screen

def ps.flushed_flush(bs: List<&2, Sc.Blk>) -> {Sc.flushed(Sc.flush(bs)) == True{} : Bool}:
  match bs:
    case Nil{}:
      {==}
    case b <> rest:
      match b:
        case Sc.Blk{i, s, l}:
          match s:
            case Sc.Comm{}:
              ps.flushed_flush(rest)
            case Sc.Final{}:
              ps.flushed_flush(rest)
            case Sc.Active{}:
              {==}

def ps.tx_flush_settles(+t: Sc.Tx) -> {Sc.flushed(Sc.Tx.blocks(Sc.step(t, Sc.Flush{}))) == True{} : Bool}:
  match t:
    case Sc.Tx{bs, n, w}:
      ps.flushed_flush(bs)

def Screen.tx_flush_settles(t):
  ps.tx_flush_settles(t)
