# eukhe: the proof of LAW throttle_empty_ignored

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

# PROOF of LAW throttle_empty_ignored: every state computes.


def tei.go(p: Bool, t: Bool, f: Bool, s: Bool) -> {Th.step(Th.Gate{p, t, f, s}, Th.Part{False{}}) == Th.Moved{Th.Gate{p, t, f, s}, []} : Th.Moved}:
  match p:
    case True{}:
      match t:
        case True{}:
          match f:
            case True{}:
              match s:
                case True{}:
                  {==}
                case False{}:
                  {==}
            case False{}:
              match s:
                case True{}:
                  {==}
                case False{}:
                  {==}
        case False{}:
          match f:
            case True{}:
              match s:
                case True{}:
                  {==}
                case False{}:
                  {==}
            case False{}:
              match s:
                case True{}:
                  {==}
                case False{}:
                  {==}
    case False{}:
      match t:
        case True{}:
          match f:
            case True{}:
              match s:
                case True{}:
                  {==}
                case False{}:
                  {==}
            case False{}:
              match s:
                case True{}:
                  {==}
                case False{}:
                  {==}
        case False{}:
          match f:
            case True{}:
              match s:
                case True{}:
                  {==}
                case False{}:
                  {==}
            case False{}:
              match s:
                case True{}:
                  {==}
                case False{}:
                  {==}

def Throttle.throttle_empty_ignored(g):
  match g:
    case Th.Gate{p, t, f, s}:
      tei.go(p, t, f, s)
