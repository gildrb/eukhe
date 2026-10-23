# eukhe: the proof of LAW wfw_sts_round_trip

import Base
import ../../bend/workflow.bend as W
import ../../LAWS.bend as Laws

def Laws.wfw_sts_round_trip(s, rest):
  match s:
    case W.Queued{}:
      {==}
    case W.Running{}:
      {==}
    case W.Finished{}:
      {==}
    case W.Erred{}:
      {==}
    case W.Cancelled{}:
      {==}
    case W.Cached{}:
      {==}
