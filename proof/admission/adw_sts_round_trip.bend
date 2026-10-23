# eukhe: the proof of LAW adw_sts_round_trip

import Base
import ../../bend/admission.bend as Ad
import ../../LAWS.bend as Laws

def Laws.adw_sts_round_trip(s, rest):
  match s:
    case Ad.Queued{}:
      {==}
    case Ad.Granted{}:
      {==}
    case Ad.Held{}:
      {==}
    case Ad.Preempted{}:
      {==}
    case Ad.Ended{}:
      {==}
