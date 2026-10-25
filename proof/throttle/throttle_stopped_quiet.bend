# eukhe: the proof of LAW throttle_stopped_quiet

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

# PROOF of LAW throttle_stopped_quiet: every stopped state computes; the others contradict the premise.


def tsq.part(p: Bool, t: Bool, f: Bool, s: Bool, shows: Bool, st: {Throttle.stopped(Th.Gate{p, t, f, s}) == True{} : Bool}) -> {Throttle.quiet(Th.step(Th.Gate{p, t, f, s}, Th.Part{shows})) == True{} : Bool}:
  match p:
    case True{}:
      match t:
        case True{}:
          match f:
            case True{}:
              match s:
                case True{}:
                  match shows:
                    case True{}:
                      {==}
                    case False{}:
                      {==}
                case False{}:
                  match shows:
                    case True{}:
                      LAThrottle.th.absurd({Throttle.quiet(Th.step(Th.Gate{True{}, True{}, True{}, False{}}, Th.Part{True{}})) == True{} : Bool}, st)
                    case False{}:
                      LAThrottle.th.absurd({Throttle.quiet(Th.step(Th.Gate{True{}, True{}, True{}, False{}}, Th.Part{False{}})) == True{} : Bool}, st)
            case False{}:
              match s:
                case True{}:
                  match shows:
                    case True{}:
                      {==}
                    case False{}:
                      {==}
                case False{}:
                  match shows:
                    case True{}:
                      LAThrottle.th.absurd({Throttle.quiet(Th.step(Th.Gate{True{}, True{}, False{}, False{}}, Th.Part{True{}})) == True{} : Bool}, st)
                    case False{}:
                      LAThrottle.th.absurd({Throttle.quiet(Th.step(Th.Gate{True{}, True{}, False{}, False{}}, Th.Part{False{}})) == True{} : Bool}, st)
        case False{}:
          match f:
            case True{}:
              match s:
                case True{}:
                  match shows:
                    case True{}:
                      {==}
                    case False{}:
                      {==}
                case False{}:
                  match shows:
                    case True{}:
                      LAThrottle.th.absurd({Throttle.quiet(Th.step(Th.Gate{True{}, False{}, True{}, False{}}, Th.Part{True{}})) == True{} : Bool}, st)
                    case False{}:
                      LAThrottle.th.absurd({Throttle.quiet(Th.step(Th.Gate{True{}, False{}, True{}, False{}}, Th.Part{False{}})) == True{} : Bool}, st)
            case False{}:
              match s:
                case True{}:
                  match shows:
                    case True{}:
                      {==}
                    case False{}:
                      {==}
                case False{}:
                  match shows:
                    case True{}:
                      LAThrottle.th.absurd({Throttle.quiet(Th.step(Th.Gate{True{}, False{}, False{}, False{}}, Th.Part{True{}})) == True{} : Bool}, st)
                    case False{}:
                      LAThrottle.th.absurd({Throttle.quiet(Th.step(Th.Gate{True{}, False{}, False{}, False{}}, Th.Part{False{}})) == True{} : Bool}, st)
    case False{}:
      match t:
        case True{}:
          match f:
            case True{}:
              match s:
                case True{}:
                  match shows:
                    case True{}:
                      {==}
                    case False{}:
                      {==}
                case False{}:
                  match shows:
                    case True{}:
                      LAThrottle.th.absurd({Throttle.quiet(Th.step(Th.Gate{False{}, True{}, True{}, False{}}, Th.Part{True{}})) == True{} : Bool}, st)
                    case False{}:
                      LAThrottle.th.absurd({Throttle.quiet(Th.step(Th.Gate{False{}, True{}, True{}, False{}}, Th.Part{False{}})) == True{} : Bool}, st)
            case False{}:
              match s:
                case True{}:
                  match shows:
                    case True{}:
                      {==}
                    case False{}:
                      {==}
                case False{}:
                  match shows:
                    case True{}:
                      LAThrottle.th.absurd({Throttle.quiet(Th.step(Th.Gate{False{}, True{}, False{}, False{}}, Th.Part{True{}})) == True{} : Bool}, st)
                    case False{}:
                      LAThrottle.th.absurd({Throttle.quiet(Th.step(Th.Gate{False{}, True{}, False{}, False{}}, Th.Part{False{}})) == True{} : Bool}, st)
        case False{}:
          match f:
            case True{}:
              match s:
                case True{}:
                  match shows:
                    case True{}:
                      {==}
                    case False{}:
                      {==}
                case False{}:
                  match shows:
                    case True{}:
                      LAThrottle.th.absurd({Throttle.quiet(Th.step(Th.Gate{False{}, False{}, True{}, False{}}, Th.Part{True{}})) == True{} : Bool}, st)
                    case False{}:
                      LAThrottle.th.absurd({Throttle.quiet(Th.step(Th.Gate{False{}, False{}, True{}, False{}}, Th.Part{False{}})) == True{} : Bool}, st)
            case False{}:
              match s:
                case True{}:
                  match shows:
                    case True{}:
                      {==}
                    case False{}:
                      {==}
                case False{}:
                  match shows:
                    case True{}:
                      LAThrottle.th.absurd({Throttle.quiet(Th.step(Th.Gate{False{}, False{}, False{}, False{}}, Th.Part{True{}})) == True{} : Bool}, st)
                    case False{}:
                      LAThrottle.th.absurd({Throttle.quiet(Th.step(Th.Gate{False{}, False{}, False{}, False{}}, Th.Part{False{}})) == True{} : Bool}, st)

def tsq.fire(p: Bool, t: Bool, f: Bool, s: Bool, st: {Throttle.stopped(Th.Gate{p, t, f, s}) == True{} : Bool}) -> {Throttle.quiet(Th.step(Th.Gate{p, t, f, s}, Th.Fire{})) == True{} : Bool}:
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
                  LAThrottle.th.absurd({Throttle.quiet(Th.step(Th.Gate{True{}, True{}, True{}, False{}}, Th.Fire{})) == True{} : Bool}, st)
            case False{}:
              match s:
                case True{}:
                  {==}
                case False{}:
                  LAThrottle.th.absurd({Throttle.quiet(Th.step(Th.Gate{True{}, True{}, False{}, False{}}, Th.Fire{})) == True{} : Bool}, st)
        case False{}:
          match f:
            case True{}:
              match s:
                case True{}:
                  {==}
                case False{}:
                  LAThrottle.th.absurd({Throttle.quiet(Th.step(Th.Gate{True{}, False{}, True{}, False{}}, Th.Fire{})) == True{} : Bool}, st)
            case False{}:
              match s:
                case True{}:
                  {==}
                case False{}:
                  LAThrottle.th.absurd({Throttle.quiet(Th.step(Th.Gate{True{}, False{}, False{}, False{}}, Th.Fire{})) == True{} : Bool}, st)
    case False{}:
      match t:
        case True{}:
          match f:
            case True{}:
              match s:
                case True{}:
                  {==}
                case False{}:
                  LAThrottle.th.absurd({Throttle.quiet(Th.step(Th.Gate{False{}, True{}, True{}, False{}}, Th.Fire{})) == True{} : Bool}, st)
            case False{}:
              match s:
                case True{}:
                  {==}
                case False{}:
                  LAThrottle.th.absurd({Throttle.quiet(Th.step(Th.Gate{False{}, True{}, False{}, False{}}, Th.Fire{})) == True{} : Bool}, st)
        case False{}:
          match f:
            case True{}:
              match s:
                case True{}:
                  {==}
                case False{}:
                  LAThrottle.th.absurd({Throttle.quiet(Th.step(Th.Gate{False{}, False{}, True{}, False{}}, Th.Fire{})) == True{} : Bool}, st)
            case False{}:
              match s:
                case True{}:
                  {==}
                case False{}:
                  LAThrottle.th.absurd({Throttle.quiet(Th.step(Th.Gate{False{}, False{}, False{}, False{}}, Th.Fire{})) == True{} : Bool}, st)

def tsq.settle(p: Bool, t: Bool, f: Bool, s: Bool, st: {Throttle.stopped(Th.Gate{p, t, f, s}) == True{} : Bool}) -> {Throttle.quiet(Th.step(Th.Gate{p, t, f, s}, Th.Settle{})) == True{} : Bool}:
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
                  LAThrottle.th.absurd({Throttle.quiet(Th.step(Th.Gate{True{}, True{}, True{}, False{}}, Th.Settle{})) == True{} : Bool}, st)
            case False{}:
              match s:
                case True{}:
                  {==}
                case False{}:
                  LAThrottle.th.absurd({Throttle.quiet(Th.step(Th.Gate{True{}, True{}, False{}, False{}}, Th.Settle{})) == True{} : Bool}, st)
        case False{}:
          match f:
            case True{}:
              match s:
                case True{}:
                  {==}
                case False{}:
                  LAThrottle.th.absurd({Throttle.quiet(Th.step(Th.Gate{True{}, False{}, True{}, False{}}, Th.Settle{})) == True{} : Bool}, st)
            case False{}:
              match s:
                case True{}:
                  {==}
                case False{}:
                  LAThrottle.th.absurd({Throttle.quiet(Th.step(Th.Gate{True{}, False{}, False{}, False{}}, Th.Settle{})) == True{} : Bool}, st)
    case False{}:
      match t:
        case True{}:
          match f:
            case True{}:
              match s:
                case True{}:
                  {==}
                case False{}:
                  LAThrottle.th.absurd({Throttle.quiet(Th.step(Th.Gate{False{}, True{}, True{}, False{}}, Th.Settle{})) == True{} : Bool}, st)
            case False{}:
              match s:
                case True{}:
                  {==}
                case False{}:
                  LAThrottle.th.absurd({Throttle.quiet(Th.step(Th.Gate{False{}, True{}, False{}, False{}}, Th.Settle{})) == True{} : Bool}, st)
        case False{}:
          match f:
            case True{}:
              match s:
                case True{}:
                  {==}
                case False{}:
                  LAThrottle.th.absurd({Throttle.quiet(Th.step(Th.Gate{False{}, False{}, True{}, False{}}, Th.Settle{})) == True{} : Bool}, st)
            case False{}:
              match s:
                case True{}:
                  {==}
                case False{}:
                  LAThrottle.th.absurd({Throttle.quiet(Th.step(Th.Gate{False{}, False{}, False{}, False{}}, Th.Settle{})) == True{} : Bool}, st)

def tsq.finish(p: Bool, t: Bool, f: Bool, s: Bool, st: {Throttle.stopped(Th.Gate{p, t, f, s}) == True{} : Bool}) -> {Throttle.quiet(Th.step(Th.Gate{p, t, f, s}, Th.Finish{})) == True{} : Bool}:
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
                  LAThrottle.th.absurd({Throttle.quiet(Th.step(Th.Gate{True{}, True{}, True{}, False{}}, Th.Finish{})) == True{} : Bool}, st)
            case False{}:
              match s:
                case True{}:
                  {==}
                case False{}:
                  LAThrottle.th.absurd({Throttle.quiet(Th.step(Th.Gate{True{}, True{}, False{}, False{}}, Th.Finish{})) == True{} : Bool}, st)
        case False{}:
          match f:
            case True{}:
              match s:
                case True{}:
                  {==}
                case False{}:
                  LAThrottle.th.absurd({Throttle.quiet(Th.step(Th.Gate{True{}, False{}, True{}, False{}}, Th.Finish{})) == True{} : Bool}, st)
            case False{}:
              match s:
                case True{}:
                  {==}
                case False{}:
                  LAThrottle.th.absurd({Throttle.quiet(Th.step(Th.Gate{True{}, False{}, False{}, False{}}, Th.Finish{})) == True{} : Bool}, st)
    case False{}:
      match t:
        case True{}:
          match f:
            case True{}:
              match s:
                case True{}:
                  {==}
                case False{}:
                  LAThrottle.th.absurd({Throttle.quiet(Th.step(Th.Gate{False{}, True{}, True{}, False{}}, Th.Finish{})) == True{} : Bool}, st)
            case False{}:
              match s:
                case True{}:
                  {==}
                case False{}:
                  LAThrottle.th.absurd({Throttle.quiet(Th.step(Th.Gate{False{}, True{}, False{}, False{}}, Th.Finish{})) == True{} : Bool}, st)
        case False{}:
          match f:
            case True{}:
              match s:
                case True{}:
                  {==}
                case False{}:
                  LAThrottle.th.absurd({Throttle.quiet(Th.step(Th.Gate{False{}, False{}, True{}, False{}}, Th.Finish{})) == True{} : Bool}, st)
            case False{}:
              match s:
                case True{}:
                  {==}
                case False{}:
                  LAThrottle.th.absurd({Throttle.quiet(Th.step(Th.Gate{False{}, False{}, False{}, False{}}, Th.Finish{})) == True{} : Bool}, st)

def tsq.quit(p: Bool, t: Bool, f: Bool, s: Bool, st: {Throttle.stopped(Th.Gate{p, t, f, s}) == True{} : Bool}) -> {Throttle.quiet(Th.step(Th.Gate{p, t, f, s}, Th.Quit{})) == True{} : Bool}:
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
                  LAThrottle.th.absurd({Throttle.quiet(Th.step(Th.Gate{True{}, True{}, True{}, False{}}, Th.Quit{})) == True{} : Bool}, st)
            case False{}:
              match s:
                case True{}:
                  {==}
                case False{}:
                  LAThrottle.th.absurd({Throttle.quiet(Th.step(Th.Gate{True{}, True{}, False{}, False{}}, Th.Quit{})) == True{} : Bool}, st)
        case False{}:
          match f:
            case True{}:
              match s:
                case True{}:
                  {==}
                case False{}:
                  LAThrottle.th.absurd({Throttle.quiet(Th.step(Th.Gate{True{}, False{}, True{}, False{}}, Th.Quit{})) == True{} : Bool}, st)
            case False{}:
              match s:
                case True{}:
                  {==}
                case False{}:
                  LAThrottle.th.absurd({Throttle.quiet(Th.step(Th.Gate{True{}, False{}, False{}, False{}}, Th.Quit{})) == True{} : Bool}, st)
    case False{}:
      match t:
        case True{}:
          match f:
            case True{}:
              match s:
                case True{}:
                  {==}
                case False{}:
                  LAThrottle.th.absurd({Throttle.quiet(Th.step(Th.Gate{False{}, True{}, True{}, False{}}, Th.Quit{})) == True{} : Bool}, st)
            case False{}:
              match s:
                case True{}:
                  {==}
                case False{}:
                  LAThrottle.th.absurd({Throttle.quiet(Th.step(Th.Gate{False{}, True{}, False{}, False{}}, Th.Quit{})) == True{} : Bool}, st)
        case False{}:
          match f:
            case True{}:
              match s:
                case True{}:
                  {==}
                case False{}:
                  LAThrottle.th.absurd({Throttle.quiet(Th.step(Th.Gate{False{}, False{}, True{}, False{}}, Th.Quit{})) == True{} : Bool}, st)
            case False{}:
              match s:
                case True{}:
                  {==}
                case False{}:
                  LAThrottle.th.absurd({Throttle.quiet(Th.step(Th.Gate{False{}, False{}, False{}, False{}}, Th.Quit{})) == True{} : Bool}, st)

def Throttle.throttle_stopped_quiet(g, e, st):
  match g:
    case Th.Gate{p, t, f, s}:
      match e:
        case Th.Part{shows}:
          tsq.part(p, t, f, s, shows, st)
        case Th.Fire{}:
          tsq.fire(p, t, f, s, st)
        case Th.Settle{}:
          tsq.settle(p, t, f, s, st)
        case Th.Finish{}:
          tsq.finish(p, t, f, s, st)
        case Th.Quit{}:
          tsq.quit(p, t, f, s, st)
