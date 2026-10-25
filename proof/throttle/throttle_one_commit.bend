# eukhe: the proof of LAW throttle_one_commit

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

# PROOF of LAW throttle_one_commit: every state and event computes.


def toc.part(p: Bool, t: Bool, f: Bool, s: Bool, shows: Bool) -> {Throttle.one_commit(Th.Gate{p, t, f, s}, Th.step(Th.Gate{p, t, f, s}, Th.Part{shows})) == True{} : Bool}:
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

def toc.fire(p: Bool, t: Bool, f: Bool, s: Bool) -> {Throttle.one_commit(Th.Gate{p, t, f, s}, Th.step(Th.Gate{p, t, f, s}, Th.Fire{})) == True{} : Bool}:
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

def toc.settle(p: Bool, t: Bool, f: Bool, s: Bool) -> {Throttle.one_commit(Th.Gate{p, t, f, s}, Th.step(Th.Gate{p, t, f, s}, Th.Settle{})) == True{} : Bool}:
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

def toc.finish(p: Bool, t: Bool, f: Bool, s: Bool) -> {Throttle.one_commit(Th.Gate{p, t, f, s}, Th.step(Th.Gate{p, t, f, s}, Th.Finish{})) == True{} : Bool}:
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

def toc.quit(p: Bool, t: Bool, f: Bool, s: Bool) -> {Throttle.one_commit(Th.Gate{p, t, f, s}, Th.step(Th.Gate{p, t, f, s}, Th.Quit{})) == True{} : Bool}:
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

def Throttle.throttle_one_commit(g, e):
  match g:
    case Th.Gate{p, t, f, s}:
      match e:
        case Th.Part{shows}:
          toc.part(p, t, f, s, shows)
        case Th.Fire{}:
          toc.fire(p, t, f, s)
        case Th.Settle{}:
          toc.settle(p, t, f, s)
        case Th.Finish{}:
          toc.finish(p, t, f, s)
        case Th.Quit{}:
          toc.quit(p, t, f, s)
