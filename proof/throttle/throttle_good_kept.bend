# eukhe: the proof of LAW throttle_good_kept

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

# PROOF of LAW throttle_good_kept: every good state and event computes; the others contradict the premise.


def tgk.part(p: Bool, t: Bool, f: Bool, s: Bool, shows: Bool, ok: {Throttle.good(Th.Gate{p, t, f, s}) == True{} : Bool}) -> {Throttle.good(Throttle.after(Th.step(Th.Gate{p, t, f, s}, Th.Part{shows}))) == True{} : Bool}:
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
                      LAThrottle.th.absurd({Throttle.good(Throttle.after(Th.step(Th.Gate{True{}, True{}, True{}, True{}}, Th.Part{True{}}))) == True{} : Bool}, ok)
                    case False{}:
                      LAThrottle.th.absurd({Throttle.good(Throttle.after(Th.step(Th.Gate{True{}, True{}, True{}, True{}}, Th.Part{False{}}))) == True{} : Bool}, ok)
                case False{}:
                  match shows:
                    case True{}:
                      LAThrottle.th.absurd({Throttle.good(Throttle.after(Th.step(Th.Gate{True{}, True{}, True{}, False{}}, Th.Part{True{}}))) == True{} : Bool}, ok)
                    case False{}:
                      LAThrottle.th.absurd({Throttle.good(Throttle.after(Th.step(Th.Gate{True{}, True{}, True{}, False{}}, Th.Part{False{}}))) == True{} : Bool}, ok)
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
                      {==}
                    case False{}:
                      {==}
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
                      {==}
                    case False{}:
                      {==}
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
                      LAThrottle.th.absurd({Throttle.good(Throttle.after(Th.step(Th.Gate{True{}, False{}, False{}, False{}}, Th.Part{True{}}))) == True{} : Bool}, ok)
                    case False{}:
                      LAThrottle.th.absurd({Throttle.good(Throttle.after(Th.step(Th.Gate{True{}, False{}, False{}, False{}}, Th.Part{False{}}))) == True{} : Bool}, ok)
    case False{}:
      match t:
        case True{}:
          match f:
            case True{}:
              match s:
                case True{}:
                  match shows:
                    case True{}:
                      LAThrottle.th.absurd({Throttle.good(Throttle.after(Th.step(Th.Gate{False{}, True{}, True{}, True{}}, Th.Part{True{}}))) == True{} : Bool}, ok)
                    case False{}:
                      LAThrottle.th.absurd({Throttle.good(Throttle.after(Th.step(Th.Gate{False{}, True{}, True{}, True{}}, Th.Part{False{}}))) == True{} : Bool}, ok)
                case False{}:
                  match shows:
                    case True{}:
                      LAThrottle.th.absurd({Throttle.good(Throttle.after(Th.step(Th.Gate{False{}, True{}, True{}, False{}}, Th.Part{True{}}))) == True{} : Bool}, ok)
                    case False{}:
                      LAThrottle.th.absurd({Throttle.good(Throttle.after(Th.step(Th.Gate{False{}, True{}, True{}, False{}}, Th.Part{False{}}))) == True{} : Bool}, ok)
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
                      {==}
                    case False{}:
                      {==}
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
                      {==}
                    case False{}:
                      {==}
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
                      {==}
                    case False{}:
                      {==}

def tgk.fire(p: Bool, t: Bool, f: Bool, s: Bool, ok: {Throttle.good(Th.Gate{p, t, f, s}) == True{} : Bool}) -> {Throttle.good(Throttle.after(Th.step(Th.Gate{p, t, f, s}, Th.Fire{}))) == True{} : Bool}:
  match p:
    case True{}:
      match t:
        case True{}:
          match f:
            case True{}:
              match s:
                case True{}:
                  LAThrottle.th.absurd({Throttle.good(Throttle.after(Th.step(Th.Gate{True{}, True{}, True{}, True{}}, Th.Fire{}))) == True{} : Bool}, ok)
                case False{}:
                  LAThrottle.th.absurd({Throttle.good(Throttle.after(Th.step(Th.Gate{True{}, True{}, True{}, False{}}, Th.Fire{}))) == True{} : Bool}, ok)
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
                  LAThrottle.th.absurd({Throttle.good(Throttle.after(Th.step(Th.Gate{True{}, False{}, False{}, False{}}, Th.Fire{}))) == True{} : Bool}, ok)
    case False{}:
      match t:
        case True{}:
          match f:
            case True{}:
              match s:
                case True{}:
                  LAThrottle.th.absurd({Throttle.good(Throttle.after(Th.step(Th.Gate{False{}, True{}, True{}, True{}}, Th.Fire{}))) == True{} : Bool}, ok)
                case False{}:
                  LAThrottle.th.absurd({Throttle.good(Throttle.after(Th.step(Th.Gate{False{}, True{}, True{}, False{}}, Th.Fire{}))) == True{} : Bool}, ok)
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

def tgk.settle(p: Bool, t: Bool, f: Bool, s: Bool, ok: {Throttle.good(Th.Gate{p, t, f, s}) == True{} : Bool}) -> {Throttle.good(Throttle.after(Th.step(Th.Gate{p, t, f, s}, Th.Settle{}))) == True{} : Bool}:
  match p:
    case True{}:
      match t:
        case True{}:
          match f:
            case True{}:
              match s:
                case True{}:
                  LAThrottle.th.absurd({Throttle.good(Throttle.after(Th.step(Th.Gate{True{}, True{}, True{}, True{}}, Th.Settle{}))) == True{} : Bool}, ok)
                case False{}:
                  LAThrottle.th.absurd({Throttle.good(Throttle.after(Th.step(Th.Gate{True{}, True{}, True{}, False{}}, Th.Settle{}))) == True{} : Bool}, ok)
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
                  LAThrottle.th.absurd({Throttle.good(Throttle.after(Th.step(Th.Gate{True{}, False{}, False{}, False{}}, Th.Settle{}))) == True{} : Bool}, ok)
    case False{}:
      match t:
        case True{}:
          match f:
            case True{}:
              match s:
                case True{}:
                  LAThrottle.th.absurd({Throttle.good(Throttle.after(Th.step(Th.Gate{False{}, True{}, True{}, True{}}, Th.Settle{}))) == True{} : Bool}, ok)
                case False{}:
                  LAThrottle.th.absurd({Throttle.good(Throttle.after(Th.step(Th.Gate{False{}, True{}, True{}, False{}}, Th.Settle{}))) == True{} : Bool}, ok)
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

def tgk.finish(p: Bool, t: Bool, f: Bool, s: Bool, ok: {Throttle.good(Th.Gate{p, t, f, s}) == True{} : Bool}) -> {Throttle.good(Throttle.after(Th.step(Th.Gate{p, t, f, s}, Th.Finish{}))) == True{} : Bool}:
  match p:
    case True{}:
      match t:
        case True{}:
          match f:
            case True{}:
              match s:
                case True{}:
                  LAThrottle.th.absurd({Throttle.good(Throttle.after(Th.step(Th.Gate{True{}, True{}, True{}, True{}}, Th.Finish{}))) == True{} : Bool}, ok)
                case False{}:
                  LAThrottle.th.absurd({Throttle.good(Throttle.after(Th.step(Th.Gate{True{}, True{}, True{}, False{}}, Th.Finish{}))) == True{} : Bool}, ok)
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
                  LAThrottle.th.absurd({Throttle.good(Throttle.after(Th.step(Th.Gate{True{}, False{}, False{}, False{}}, Th.Finish{}))) == True{} : Bool}, ok)
    case False{}:
      match t:
        case True{}:
          match f:
            case True{}:
              match s:
                case True{}:
                  LAThrottle.th.absurd({Throttle.good(Throttle.after(Th.step(Th.Gate{False{}, True{}, True{}, True{}}, Th.Finish{}))) == True{} : Bool}, ok)
                case False{}:
                  LAThrottle.th.absurd({Throttle.good(Throttle.after(Th.step(Th.Gate{False{}, True{}, True{}, False{}}, Th.Finish{}))) == True{} : Bool}, ok)
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

def tgk.quit(p: Bool, t: Bool, f: Bool, s: Bool, ok: {Throttle.good(Th.Gate{p, t, f, s}) == True{} : Bool}) -> {Throttle.good(Throttle.after(Th.step(Th.Gate{p, t, f, s}, Th.Quit{}))) == True{} : Bool}:
  match p:
    case True{}:
      match t:
        case True{}:
          match f:
            case True{}:
              match s:
                case True{}:
                  LAThrottle.th.absurd({Throttle.good(Throttle.after(Th.step(Th.Gate{True{}, True{}, True{}, True{}}, Th.Quit{}))) == True{} : Bool}, ok)
                case False{}:
                  LAThrottle.th.absurd({Throttle.good(Throttle.after(Th.step(Th.Gate{True{}, True{}, True{}, False{}}, Th.Quit{}))) == True{} : Bool}, ok)
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
                  LAThrottle.th.absurd({Throttle.good(Throttle.after(Th.step(Th.Gate{True{}, False{}, False{}, False{}}, Th.Quit{}))) == True{} : Bool}, ok)
    case False{}:
      match t:
        case True{}:
          match f:
            case True{}:
              match s:
                case True{}:
                  LAThrottle.th.absurd({Throttle.good(Throttle.after(Th.step(Th.Gate{False{}, True{}, True{}, True{}}, Th.Quit{}))) == True{} : Bool}, ok)
                case False{}:
                  LAThrottle.th.absurd({Throttle.good(Throttle.after(Th.step(Th.Gate{False{}, True{}, True{}, False{}}, Th.Quit{}))) == True{} : Bool}, ok)
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

def Throttle.throttle_good_kept(g, e, ok):
  match g:
    case Th.Gate{p, t, f, s}:
      match e:
        case Th.Part{shows}:
          tgk.part(p, t, f, s, shows, ok)
        case Th.Fire{}:
          tgk.fire(p, t, f, s, ok)
        case Th.Settle{}:
          tgk.settle(p, t, f, s, ok)
        case Th.Finish{}:
          tgk.finish(p, t, f, s, ok)
        case Th.Quit{}:
          tgk.quit(p, t, f, s, ok)
