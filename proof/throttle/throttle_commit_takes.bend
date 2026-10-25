# eukhe: the proof of LAW throttle_commit_takes

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

# PROOF of LAW throttle_commit_takes: every state and event computes.


def tct.part(p: Bool, t: Bool, f: Bool, s: Bool, shows: Bool) -> {Throttle.takes(Th.Gate{p, t, f, s}, Th.step(Th.Gate{p, t, f, s}, Th.Part{shows})) == True{} : Bool}:
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

def tct.fire(p: Bool, t: Bool, f: Bool, s: Bool) -> {Throttle.takes(Th.Gate{p, t, f, s}, Th.step(Th.Gate{p, t, f, s}, Th.Fire{})) == True{} : Bool}:
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

def tct.settle(p: Bool, t: Bool, f: Bool, s: Bool) -> {Throttle.takes(Th.Gate{p, t, f, s}, Th.step(Th.Gate{p, t, f, s}, Th.Settle{})) == True{} : Bool}:
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

def tct.finish(p: Bool, t: Bool, f: Bool, s: Bool) -> {Throttle.takes(Th.Gate{p, t, f, s}, Th.step(Th.Gate{p, t, f, s}, Th.Finish{})) == True{} : Bool}:
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

def tct.quit(p: Bool, t: Bool, f: Bool, s: Bool) -> {Throttle.takes(Th.Gate{p, t, f, s}, Th.step(Th.Gate{p, t, f, s}, Th.Quit{})) == True{} : Bool}:
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

def Throttle.throttle_commit_takes(g, e):
  match g:
    case Th.Gate{p, t, f, s}:
      match e:
        case Th.Part{shows}:
          tct.part(p, t, f, s, shows)
        case Th.Fire{}:
          tct.fire(p, t, f, s)
        case Th.Settle{}:
          tct.settle(p, t, f, s)
        case Th.Finish{}:
          tct.finish(p, t, f, s)
        case Th.Quit{}:
          tct.quit(p, t, f, s)
