# eukhe: the proof of LAW throttle_stop_ends

import Base
import ../../bend/throttle.bend as Th
import ../../bend/ffi_throttle.bend as FTh
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../wire/wire_nat_exact.bend as PWireNatExact
import ../wire/wire_nat_not_err.bend as PWireNatNotErr
import ../wire/wire_bool_exact.bend as PWireBoolExact
import ../wire/wire_bool_round_trip.bend as PWireBoolRoundTrip
import ../base/wire.bend as LWire
import ../../laws/throttle.bend as Throttle
import ./base.bend as LAThrottle

# PROOF of LAW throttle_stop_ends: every state computes, for the stop and for a drop.


def tse2.go(p: Bool, t: Bool, f: Bool, s: Bool) -> {Throttle.ends(Th.step(Th.Gate{p, t, f, s}, Th.Finish{})) == True{} : Bool} & {Throttle.ends(Th.step(Th.Gate{p, t, f, s}, Th.Quit{})) == True{} : Bool}:
  match p:
    case True{}:
      match t:
        case True{}:
          match f:
            case True{}:
              match s:
                case True{}:
                  ({==}, {==})
                case False{}:
                  ({==}, {==})
            case False{}:
              match s:
                case True{}:
                  ({==}, {==})
                case False{}:
                  ({==}, {==})
        case False{}:
          match f:
            case True{}:
              match s:
                case True{}:
                  ({==}, {==})
                case False{}:
                  ({==}, {==})
            case False{}:
              match s:
                case True{}:
                  ({==}, {==})
                case False{}:
                  ({==}, {==})
    case False{}:
      match t:
        case True{}:
          match f:
            case True{}:
              match s:
                case True{}:
                  ({==}, {==})
                case False{}:
                  ({==}, {==})
            case False{}:
              match s:
                case True{}:
                  ({==}, {==})
                case False{}:
                  ({==}, {==})
        case False{}:
          match f:
            case True{}:
              match s:
                case True{}:
                  ({==}, {==})
                case False{}:
                  ({==}, {==})
            case False{}:
              match s:
                case True{}:
                  ({==}, {==})
                case False{}:
                  ({==}, {==})

def Throttle.throttle_stop_ends(g):
  match g:
    case Th.Gate{p, t, f, s}:
      tse2.go(p, t, f, s)
