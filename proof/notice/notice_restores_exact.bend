# eukhe: the proof of LAW notice_restores_exact

import Base
import ../../bend/notice.bend as No
import ../../laws/notice.bend as Notice

# the model's restores are the spec's, event by event
def nre.go(evs: List<&2, No.Ev>) -> {No.restores(evs) == Notice.nt_restores(evs) : Nat}:
  match evs:
    case Nil{}:
      {==}
    case e <> +rest:
      match e:
        case No.Restore{}:
          %nre.go(rest) : {1n+No.restores(rest) == 1n+_ : Nat}
          {==}
        case No.Live{}:
          nre.go(rest)
        case No.Reconnect{}:
          nre.go(rest)

def Notice.notice_restores_exact(evs):
  nre.go(evs)
