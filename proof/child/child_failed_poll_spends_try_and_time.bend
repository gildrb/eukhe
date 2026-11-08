# eukhe: the proof of LAW child_failed_poll_spends_try_and_time
#
# PROOF: by the tries left: none or one is unreachable; two or more spend
# a try and the elapsed ms off the clock (LA.pc.spends).

import Base
import ../../bend/child.bend as Ch
import ../../laws/child.bend as Child
import ./base.bend as LA

def Child.child_failed_poll_spends_try_and_time(cfg, w, e):
  match w:
    case Ch.W{+tok, +l, +n}:
      match n:
        case 0n:
          {==}
        case 1n+q:
          match q:
            case 0n:
              {==}
            case 1n+u:
              LA.pc.spends(l, e, tok, 1n+u)
