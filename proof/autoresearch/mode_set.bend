# eukhe: the proof of LAW mode_set

import Base
import ../../bend/autoresearch/state.bend as ArS
import ../../laws/autoresearch/events.bend as AutoresearchEvents

def AutoresearchEvents.mode_set(s, m):
  match s:
    case ArS.St{cfg, seg, mode, runs, pend}:
      ({==}, ({==}, ({==}, ({==}, {==}))))
