# eukhe: the proof of LAW throttle_progress

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

# PROOF of LAW throttle_progress: every good state that the event wakes computes; the others contradict a premise.


def tpg.part(p: Bool, t: Bool, f: Bool, s: Bool, shows: Bool, ok: {Throttle.good(Th.Gate{p, t, f, s}) == True{} : Bool}, w: {Throttle.wakes(Th.Gate{p, t, f, s}, Th.Part{shows}) == True{} : Bool}) -> {Throttle.moves(Throttle.actions(Th.step(Th.Gate{p, t, f, s}, Th.Part{shows}))) == True{} : Bool}:
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
                      LAThrottle.th.absurd({Throttle.moves(Throttle.actions(Th.step(Th.Gate{True{}, True{}, True{}, True{}}, Th.Part{True{}}))) == True{} : Bool}, ok)
                    case False{}:
                      LAThrottle.th.absurd({Throttle.moves(Throttle.actions(Th.step(Th.Gate{True{}, True{}, True{}, True{}}, Th.Part{False{}}))) == True{} : Bool}, ok)
                case False{}:
                  match shows:
                    case True{}:
                      LAThrottle.th.absurd({Throttle.moves(Throttle.actions(Th.step(Th.Gate{True{}, True{}, True{}, False{}}, Th.Part{True{}}))) == True{} : Bool}, ok)
                    case False{}:
                      LAThrottle.th.absurd({Throttle.moves(Throttle.actions(Th.step(Th.Gate{True{}, True{}, True{}, False{}}, Th.Part{False{}}))) == True{} : Bool}, ok)
            case False{}:
              match s:
                case True{}:
                  match shows:
                    case True{}:
                      LAThrottle.th.absurd({Throttle.moves(Throttle.actions(Th.step(Th.Gate{True{}, True{}, False{}, True{}}, Th.Part{True{}}))) == True{} : Bool}, w)
                    case False{}:
                      LAThrottle.th.absurd({Throttle.moves(Throttle.actions(Th.step(Th.Gate{True{}, True{}, False{}, True{}}, Th.Part{False{}}))) == True{} : Bool}, w)
                case False{}:
                  match shows:
                    case True{}:
                      LAThrottle.th.absurd({Throttle.moves(Throttle.actions(Th.step(Th.Gate{True{}, True{}, False{}, False{}}, Th.Part{True{}}))) == True{} : Bool}, w)
                    case False{}:
                      LAThrottle.th.absurd({Throttle.moves(Throttle.actions(Th.step(Th.Gate{True{}, True{}, False{}, False{}}, Th.Part{False{}}))) == True{} : Bool}, w)
        case False{}:
          match f:
            case True{}:
              match s:
                case True{}:
                  match shows:
                    case True{}:
                      LAThrottle.th.absurd({Throttle.moves(Throttle.actions(Th.step(Th.Gate{True{}, False{}, True{}, True{}}, Th.Part{True{}}))) == True{} : Bool}, w)
                    case False{}:
                      LAThrottle.th.absurd({Throttle.moves(Throttle.actions(Th.step(Th.Gate{True{}, False{}, True{}, True{}}, Th.Part{False{}}))) == True{} : Bool}, w)
                case False{}:
                  match shows:
                    case True{}:
                      LAThrottle.th.absurd({Throttle.moves(Throttle.actions(Th.step(Th.Gate{True{}, False{}, True{}, False{}}, Th.Part{True{}}))) == True{} : Bool}, w)
                    case False{}:
                      LAThrottle.th.absurd({Throttle.moves(Throttle.actions(Th.step(Th.Gate{True{}, False{}, True{}, False{}}, Th.Part{False{}}))) == True{} : Bool}, w)
            case False{}:
              match s:
                case True{}:
                  match shows:
                    case True{}:
                      LAThrottle.th.absurd({Throttle.moves(Throttle.actions(Th.step(Th.Gate{True{}, False{}, False{}, True{}}, Th.Part{True{}}))) == True{} : Bool}, w)
                    case False{}:
                      LAThrottle.th.absurd({Throttle.moves(Throttle.actions(Th.step(Th.Gate{True{}, False{}, False{}, True{}}, Th.Part{False{}}))) == True{} : Bool}, w)
                case False{}:
                  match shows:
                    case True{}:
                      LAThrottle.th.absurd({Throttle.moves(Throttle.actions(Th.step(Th.Gate{True{}, False{}, False{}, False{}}, Th.Part{True{}}))) == True{} : Bool}, ok)
                    case False{}:
                      LAThrottle.th.absurd({Throttle.moves(Throttle.actions(Th.step(Th.Gate{True{}, False{}, False{}, False{}}, Th.Part{False{}}))) == True{} : Bool}, ok)
    case False{}:
      match t:
        case True{}:
          match f:
            case True{}:
              match s:
                case True{}:
                  match shows:
                    case True{}:
                      LAThrottle.th.absurd({Throttle.moves(Throttle.actions(Th.step(Th.Gate{False{}, True{}, True{}, True{}}, Th.Part{True{}}))) == True{} : Bool}, ok)
                    case False{}:
                      LAThrottle.th.absurd({Throttle.moves(Throttle.actions(Th.step(Th.Gate{False{}, True{}, True{}, True{}}, Th.Part{False{}}))) == True{} : Bool}, ok)
                case False{}:
                  match shows:
                    case True{}:
                      LAThrottle.th.absurd({Throttle.moves(Throttle.actions(Th.step(Th.Gate{False{}, True{}, True{}, False{}}, Th.Part{True{}}))) == True{} : Bool}, ok)
                    case False{}:
                      LAThrottle.th.absurd({Throttle.moves(Throttle.actions(Th.step(Th.Gate{False{}, True{}, True{}, False{}}, Th.Part{False{}}))) == True{} : Bool}, ok)
            case False{}:
              match s:
                case True{}:
                  match shows:
                    case True{}:
                      LAThrottle.th.absurd({Throttle.moves(Throttle.actions(Th.step(Th.Gate{False{}, True{}, False{}, True{}}, Th.Part{True{}}))) == True{} : Bool}, w)
                    case False{}:
                      LAThrottle.th.absurd({Throttle.moves(Throttle.actions(Th.step(Th.Gate{False{}, True{}, False{}, True{}}, Th.Part{False{}}))) == True{} : Bool}, w)
                case False{}:
                  match shows:
                    case True{}:
                      LAThrottle.th.absurd({Throttle.moves(Throttle.actions(Th.step(Th.Gate{False{}, True{}, False{}, False{}}, Th.Part{True{}}))) == True{} : Bool}, w)
                    case False{}:
                      LAThrottle.th.absurd({Throttle.moves(Throttle.actions(Th.step(Th.Gate{False{}, True{}, False{}, False{}}, Th.Part{False{}}))) == True{} : Bool}, w)
        case False{}:
          match f:
            case True{}:
              match s:
                case True{}:
                  match shows:
                    case True{}:
                      LAThrottle.th.absurd({Throttle.moves(Throttle.actions(Th.step(Th.Gate{False{}, False{}, True{}, True{}}, Th.Part{True{}}))) == True{} : Bool}, w)
                    case False{}:
                      LAThrottle.th.absurd({Throttle.moves(Throttle.actions(Th.step(Th.Gate{False{}, False{}, True{}, True{}}, Th.Part{False{}}))) == True{} : Bool}, w)
                case False{}:
                  match shows:
                    case True{}:
                      LAThrottle.th.absurd({Throttle.moves(Throttle.actions(Th.step(Th.Gate{False{}, False{}, True{}, False{}}, Th.Part{True{}}))) == True{} : Bool}, w)
                    case False{}:
                      LAThrottle.th.absurd({Throttle.moves(Throttle.actions(Th.step(Th.Gate{False{}, False{}, True{}, False{}}, Th.Part{False{}}))) == True{} : Bool}, w)
            case False{}:
              match s:
                case True{}:
                  match shows:
                    case True{}:
                      LAThrottle.th.absurd({Throttle.moves(Throttle.actions(Th.step(Th.Gate{False{}, False{}, False{}, True{}}, Th.Part{True{}}))) == True{} : Bool}, w)
                    case False{}:
                      LAThrottle.th.absurd({Throttle.moves(Throttle.actions(Th.step(Th.Gate{False{}, False{}, False{}, True{}}, Th.Part{False{}}))) == True{} : Bool}, w)
                case False{}:
                  match shows:
                    case True{}:
                      LAThrottle.th.absurd({Throttle.moves(Throttle.actions(Th.step(Th.Gate{False{}, False{}, False{}, False{}}, Th.Part{True{}}))) == True{} : Bool}, w)
                    case False{}:
                      LAThrottle.th.absurd({Throttle.moves(Throttle.actions(Th.step(Th.Gate{False{}, False{}, False{}, False{}}, Th.Part{False{}}))) == True{} : Bool}, w)

def tpg.fire(p: Bool, t: Bool, f: Bool, s: Bool, ok: {Throttle.good(Th.Gate{p, t, f, s}) == True{} : Bool}, w: {Throttle.wakes(Th.Gate{p, t, f, s}, Th.Fire{}) == True{} : Bool}) -> {Throttle.moves(Throttle.actions(Th.step(Th.Gate{p, t, f, s}, Th.Fire{}))) == True{} : Bool}:
  match p:
    case True{}:
      match t:
        case True{}:
          match f:
            case True{}:
              match s:
                case True{}:
                  LAThrottle.th.absurd({Throttle.moves(Throttle.actions(Th.step(Th.Gate{True{}, True{}, True{}, True{}}, Th.Fire{}))) == True{} : Bool}, ok)
                case False{}:
                  LAThrottle.th.absurd({Throttle.moves(Throttle.actions(Th.step(Th.Gate{True{}, True{}, True{}, False{}}, Th.Fire{}))) == True{} : Bool}, ok)
            case False{}:
              match s:
                case True{}:
                  LAThrottle.th.absurd({Throttle.moves(Throttle.actions(Th.step(Th.Gate{True{}, True{}, False{}, True{}}, Th.Fire{}))) == True{} : Bool}, w)
                case False{}:
                  {==}
        case False{}:
          match f:
            case True{}:
              match s:
                case True{}:
                  LAThrottle.th.absurd({Throttle.moves(Throttle.actions(Th.step(Th.Gate{True{}, False{}, True{}, True{}}, Th.Fire{}))) == True{} : Bool}, w)
                case False{}:
                  LAThrottle.th.absurd({Throttle.moves(Throttle.actions(Th.step(Th.Gate{True{}, False{}, True{}, False{}}, Th.Fire{}))) == True{} : Bool}, w)
            case False{}:
              match s:
                case True{}:
                  LAThrottle.th.absurd({Throttle.moves(Throttle.actions(Th.step(Th.Gate{True{}, False{}, False{}, True{}}, Th.Fire{}))) == True{} : Bool}, w)
                case False{}:
                  LAThrottle.th.absurd({Throttle.moves(Throttle.actions(Th.step(Th.Gate{True{}, False{}, False{}, False{}}, Th.Fire{}))) == True{} : Bool}, ok)
    case False{}:
      match t:
        case True{}:
          match f:
            case True{}:
              match s:
                case True{}:
                  LAThrottle.th.absurd({Throttle.moves(Throttle.actions(Th.step(Th.Gate{False{}, True{}, True{}, True{}}, Th.Fire{}))) == True{} : Bool}, ok)
                case False{}:
                  LAThrottle.th.absurd({Throttle.moves(Throttle.actions(Th.step(Th.Gate{False{}, True{}, True{}, False{}}, Th.Fire{}))) == True{} : Bool}, ok)
            case False{}:
              match s:
                case True{}:
                  LAThrottle.th.absurd({Throttle.moves(Throttle.actions(Th.step(Th.Gate{False{}, True{}, False{}, True{}}, Th.Fire{}))) == True{} : Bool}, w)
                case False{}:
                  LAThrottle.th.absurd({Throttle.moves(Throttle.actions(Th.step(Th.Gate{False{}, True{}, False{}, False{}}, Th.Fire{}))) == True{} : Bool}, w)
        case False{}:
          match f:
            case True{}:
              match s:
                case True{}:
                  LAThrottle.th.absurd({Throttle.moves(Throttle.actions(Th.step(Th.Gate{False{}, False{}, True{}, True{}}, Th.Fire{}))) == True{} : Bool}, w)
                case False{}:
                  LAThrottle.th.absurd({Throttle.moves(Throttle.actions(Th.step(Th.Gate{False{}, False{}, True{}, False{}}, Th.Fire{}))) == True{} : Bool}, w)
            case False{}:
              match s:
                case True{}:
                  LAThrottle.th.absurd({Throttle.moves(Throttle.actions(Th.step(Th.Gate{False{}, False{}, False{}, True{}}, Th.Fire{}))) == True{} : Bool}, w)
                case False{}:
                  LAThrottle.th.absurd({Throttle.moves(Throttle.actions(Th.step(Th.Gate{False{}, False{}, False{}, False{}}, Th.Fire{}))) == True{} : Bool}, w)

def tpg.settle(p: Bool, t: Bool, f: Bool, s: Bool, ok: {Throttle.good(Th.Gate{p, t, f, s}) == True{} : Bool}, w: {Throttle.wakes(Th.Gate{p, t, f, s}, Th.Settle{}) == True{} : Bool}) -> {Throttle.moves(Throttle.actions(Th.step(Th.Gate{p, t, f, s}, Th.Settle{}))) == True{} : Bool}:
  match p:
    case True{}:
      match t:
        case True{}:
          match f:
            case True{}:
              match s:
                case True{}:
                  LAThrottle.th.absurd({Throttle.moves(Throttle.actions(Th.step(Th.Gate{True{}, True{}, True{}, True{}}, Th.Settle{}))) == True{} : Bool}, ok)
                case False{}:
                  LAThrottle.th.absurd({Throttle.moves(Throttle.actions(Th.step(Th.Gate{True{}, True{}, True{}, False{}}, Th.Settle{}))) == True{} : Bool}, ok)
            case False{}:
              match s:
                case True{}:
                  LAThrottle.th.absurd({Throttle.moves(Throttle.actions(Th.step(Th.Gate{True{}, True{}, False{}, True{}}, Th.Settle{}))) == True{} : Bool}, w)
                case False{}:
                  LAThrottle.th.absurd({Throttle.moves(Throttle.actions(Th.step(Th.Gate{True{}, True{}, False{}, False{}}, Th.Settle{}))) == True{} : Bool}, w)
        case False{}:
          match f:
            case True{}:
              match s:
                case True{}:
                  LAThrottle.th.absurd({Throttle.moves(Throttle.actions(Th.step(Th.Gate{True{}, False{}, True{}, True{}}, Th.Settle{}))) == True{} : Bool}, w)
                case False{}:
                  {==}
            case False{}:
              match s:
                case True{}:
                  LAThrottle.th.absurd({Throttle.moves(Throttle.actions(Th.step(Th.Gate{True{}, False{}, False{}, True{}}, Th.Settle{}))) == True{} : Bool}, w)
                case False{}:
                  LAThrottle.th.absurd({Throttle.moves(Throttle.actions(Th.step(Th.Gate{True{}, False{}, False{}, False{}}, Th.Settle{}))) == True{} : Bool}, ok)
    case False{}:
      match t:
        case True{}:
          match f:
            case True{}:
              match s:
                case True{}:
                  LAThrottle.th.absurd({Throttle.moves(Throttle.actions(Th.step(Th.Gate{False{}, True{}, True{}, True{}}, Th.Settle{}))) == True{} : Bool}, ok)
                case False{}:
                  LAThrottle.th.absurd({Throttle.moves(Throttle.actions(Th.step(Th.Gate{False{}, True{}, True{}, False{}}, Th.Settle{}))) == True{} : Bool}, ok)
            case False{}:
              match s:
                case True{}:
                  LAThrottle.th.absurd({Throttle.moves(Throttle.actions(Th.step(Th.Gate{False{}, True{}, False{}, True{}}, Th.Settle{}))) == True{} : Bool}, w)
                case False{}:
                  LAThrottle.th.absurd({Throttle.moves(Throttle.actions(Th.step(Th.Gate{False{}, True{}, False{}, False{}}, Th.Settle{}))) == True{} : Bool}, w)
        case False{}:
          match f:
            case True{}:
              match s:
                case True{}:
                  LAThrottle.th.absurd({Throttle.moves(Throttle.actions(Th.step(Th.Gate{False{}, False{}, True{}, True{}}, Th.Settle{}))) == True{} : Bool}, w)
                case False{}:
                  LAThrottle.th.absurd({Throttle.moves(Throttle.actions(Th.step(Th.Gate{False{}, False{}, True{}, False{}}, Th.Settle{}))) == True{} : Bool}, w)
            case False{}:
              match s:
                case True{}:
                  LAThrottle.th.absurd({Throttle.moves(Throttle.actions(Th.step(Th.Gate{False{}, False{}, False{}, True{}}, Th.Settle{}))) == True{} : Bool}, w)
                case False{}:
                  LAThrottle.th.absurd({Throttle.moves(Throttle.actions(Th.step(Th.Gate{False{}, False{}, False{}, False{}}, Th.Settle{}))) == True{} : Bool}, w)

def tpg.finish(p: Bool, t: Bool, f: Bool, s: Bool, ok: {Throttle.good(Th.Gate{p, t, f, s}) == True{} : Bool}, w: {Throttle.wakes(Th.Gate{p, t, f, s}, Th.Finish{}) == True{} : Bool}) -> {Throttle.moves(Throttle.actions(Th.step(Th.Gate{p, t, f, s}, Th.Finish{}))) == True{} : Bool}:
  match p:
    case True{}:
      match t:
        case True{}:
          match f:
            case True{}:
              match s:
                case True{}:
                  LAThrottle.th.absurd({Throttle.moves(Throttle.actions(Th.step(Th.Gate{True{}, True{}, True{}, True{}}, Th.Finish{}))) == True{} : Bool}, ok)
                case False{}:
                  LAThrottle.th.absurd({Throttle.moves(Throttle.actions(Th.step(Th.Gate{True{}, True{}, True{}, False{}}, Th.Finish{}))) == True{} : Bool}, ok)
            case False{}:
              match s:
                case True{}:
                  LAThrottle.th.absurd({Throttle.moves(Throttle.actions(Th.step(Th.Gate{True{}, True{}, False{}, True{}}, Th.Finish{}))) == True{} : Bool}, w)
                case False{}:
                  LAThrottle.th.absurd({Throttle.moves(Throttle.actions(Th.step(Th.Gate{True{}, True{}, False{}, False{}}, Th.Finish{}))) == True{} : Bool}, w)
        case False{}:
          match f:
            case True{}:
              match s:
                case True{}:
                  LAThrottle.th.absurd({Throttle.moves(Throttle.actions(Th.step(Th.Gate{True{}, False{}, True{}, True{}}, Th.Finish{}))) == True{} : Bool}, w)
                case False{}:
                  LAThrottle.th.absurd({Throttle.moves(Throttle.actions(Th.step(Th.Gate{True{}, False{}, True{}, False{}}, Th.Finish{}))) == True{} : Bool}, w)
            case False{}:
              match s:
                case True{}:
                  LAThrottle.th.absurd({Throttle.moves(Throttle.actions(Th.step(Th.Gate{True{}, False{}, False{}, True{}}, Th.Finish{}))) == True{} : Bool}, w)
                case False{}:
                  LAThrottle.th.absurd({Throttle.moves(Throttle.actions(Th.step(Th.Gate{True{}, False{}, False{}, False{}}, Th.Finish{}))) == True{} : Bool}, ok)
    case False{}:
      match t:
        case True{}:
          match f:
            case True{}:
              match s:
                case True{}:
                  LAThrottle.th.absurd({Throttle.moves(Throttle.actions(Th.step(Th.Gate{False{}, True{}, True{}, True{}}, Th.Finish{}))) == True{} : Bool}, ok)
                case False{}:
                  LAThrottle.th.absurd({Throttle.moves(Throttle.actions(Th.step(Th.Gate{False{}, True{}, True{}, False{}}, Th.Finish{}))) == True{} : Bool}, ok)
            case False{}:
              match s:
                case True{}:
                  LAThrottle.th.absurd({Throttle.moves(Throttle.actions(Th.step(Th.Gate{False{}, True{}, False{}, True{}}, Th.Finish{}))) == True{} : Bool}, w)
                case False{}:
                  LAThrottle.th.absurd({Throttle.moves(Throttle.actions(Th.step(Th.Gate{False{}, True{}, False{}, False{}}, Th.Finish{}))) == True{} : Bool}, w)
        case False{}:
          match f:
            case True{}:
              match s:
                case True{}:
                  LAThrottle.th.absurd({Throttle.moves(Throttle.actions(Th.step(Th.Gate{False{}, False{}, True{}, True{}}, Th.Finish{}))) == True{} : Bool}, w)
                case False{}:
                  LAThrottle.th.absurd({Throttle.moves(Throttle.actions(Th.step(Th.Gate{False{}, False{}, True{}, False{}}, Th.Finish{}))) == True{} : Bool}, w)
            case False{}:
              match s:
                case True{}:
                  LAThrottle.th.absurd({Throttle.moves(Throttle.actions(Th.step(Th.Gate{False{}, False{}, False{}, True{}}, Th.Finish{}))) == True{} : Bool}, w)
                case False{}:
                  LAThrottle.th.absurd({Throttle.moves(Throttle.actions(Th.step(Th.Gate{False{}, False{}, False{}, False{}}, Th.Finish{}))) == True{} : Bool}, w)

def tpg.quit(p: Bool, t: Bool, f: Bool, s: Bool, ok: {Throttle.good(Th.Gate{p, t, f, s}) == True{} : Bool}, w: {Throttle.wakes(Th.Gate{p, t, f, s}, Th.Quit{}) == True{} : Bool}) -> {Throttle.moves(Throttle.actions(Th.step(Th.Gate{p, t, f, s}, Th.Quit{}))) == True{} : Bool}:
  match p:
    case True{}:
      match t:
        case True{}:
          match f:
            case True{}:
              match s:
                case True{}:
                  LAThrottle.th.absurd({Throttle.moves(Throttle.actions(Th.step(Th.Gate{True{}, True{}, True{}, True{}}, Th.Quit{}))) == True{} : Bool}, ok)
                case False{}:
                  LAThrottle.th.absurd({Throttle.moves(Throttle.actions(Th.step(Th.Gate{True{}, True{}, True{}, False{}}, Th.Quit{}))) == True{} : Bool}, ok)
            case False{}:
              match s:
                case True{}:
                  LAThrottle.th.absurd({Throttle.moves(Throttle.actions(Th.step(Th.Gate{True{}, True{}, False{}, True{}}, Th.Quit{}))) == True{} : Bool}, w)
                case False{}:
                  LAThrottle.th.absurd({Throttle.moves(Throttle.actions(Th.step(Th.Gate{True{}, True{}, False{}, False{}}, Th.Quit{}))) == True{} : Bool}, w)
        case False{}:
          match f:
            case True{}:
              match s:
                case True{}:
                  LAThrottle.th.absurd({Throttle.moves(Throttle.actions(Th.step(Th.Gate{True{}, False{}, True{}, True{}}, Th.Quit{}))) == True{} : Bool}, w)
                case False{}:
                  LAThrottle.th.absurd({Throttle.moves(Throttle.actions(Th.step(Th.Gate{True{}, False{}, True{}, False{}}, Th.Quit{}))) == True{} : Bool}, w)
            case False{}:
              match s:
                case True{}:
                  LAThrottle.th.absurd({Throttle.moves(Throttle.actions(Th.step(Th.Gate{True{}, False{}, False{}, True{}}, Th.Quit{}))) == True{} : Bool}, w)
                case False{}:
                  LAThrottle.th.absurd({Throttle.moves(Throttle.actions(Th.step(Th.Gate{True{}, False{}, False{}, False{}}, Th.Quit{}))) == True{} : Bool}, ok)
    case False{}:
      match t:
        case True{}:
          match f:
            case True{}:
              match s:
                case True{}:
                  LAThrottle.th.absurd({Throttle.moves(Throttle.actions(Th.step(Th.Gate{False{}, True{}, True{}, True{}}, Th.Quit{}))) == True{} : Bool}, ok)
                case False{}:
                  LAThrottle.th.absurd({Throttle.moves(Throttle.actions(Th.step(Th.Gate{False{}, True{}, True{}, False{}}, Th.Quit{}))) == True{} : Bool}, ok)
            case False{}:
              match s:
                case True{}:
                  LAThrottle.th.absurd({Throttle.moves(Throttle.actions(Th.step(Th.Gate{False{}, True{}, False{}, True{}}, Th.Quit{}))) == True{} : Bool}, w)
                case False{}:
                  LAThrottle.th.absurd({Throttle.moves(Throttle.actions(Th.step(Th.Gate{False{}, True{}, False{}, False{}}, Th.Quit{}))) == True{} : Bool}, w)
        case False{}:
          match f:
            case True{}:
              match s:
                case True{}:
                  LAThrottle.th.absurd({Throttle.moves(Throttle.actions(Th.step(Th.Gate{False{}, False{}, True{}, True{}}, Th.Quit{}))) == True{} : Bool}, w)
                case False{}:
                  LAThrottle.th.absurd({Throttle.moves(Throttle.actions(Th.step(Th.Gate{False{}, False{}, True{}, False{}}, Th.Quit{}))) == True{} : Bool}, w)
            case False{}:
              match s:
                case True{}:
                  LAThrottle.th.absurd({Throttle.moves(Throttle.actions(Th.step(Th.Gate{False{}, False{}, False{}, True{}}, Th.Quit{}))) == True{} : Bool}, w)
                case False{}:
                  LAThrottle.th.absurd({Throttle.moves(Throttle.actions(Th.step(Th.Gate{False{}, False{}, False{}, False{}}, Th.Quit{}))) == True{} : Bool}, w)

def Throttle.throttle_progress(g, e, ok, w):
  match g:
    case Th.Gate{p, t, f, s}:
      match e:
        case Th.Part{shows}:
          tpg.part(p, t, f, s, shows, ok, w)
        case Th.Fire{}:
          tpg.fire(p, t, f, s, ok, w)
        case Th.Settle{}:
          tpg.settle(p, t, f, s, ok, w)
        case Th.Finish{}:
          tpg.finish(p, t, f, s, ok, w)
        case Th.Quit{}:
          tpg.quit(p, t, f, s, ok, w)
