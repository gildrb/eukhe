# eukhe: the proof of LAW throttle_step_exact

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

# PROOF of LAW throttle_step_exact: every state and event computes both sides.


def tse.part(p: Bool, t: Bool, f: Bool, s: Bool, shows: Bool) -> {Th.step(Th.Gate{p, t, f, s}, Th.Part{shows}) == Throttle.step_spec(Th.Gate{p, t, f, s}, Th.Part{shows}) : Th.Moved}:
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

def tse.fire(p: Bool, t: Bool, f: Bool, s: Bool) -> {Th.step(Th.Gate{p, t, f, s}, Th.Fire{}) == Throttle.step_spec(Th.Gate{p, t, f, s}, Th.Fire{}) : Th.Moved}:
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

def tse.settle(p: Bool, t: Bool, f: Bool, s: Bool) -> {Th.step(Th.Gate{p, t, f, s}, Th.Settle{}) == Throttle.step_spec(Th.Gate{p, t, f, s}, Th.Settle{}) : Th.Moved}:
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

def tse.finish(p: Bool, t: Bool, f: Bool, s: Bool) -> {Th.step(Th.Gate{p, t, f, s}, Th.Finish{}) == Throttle.step_spec(Th.Gate{p, t, f, s}, Th.Finish{}) : Th.Moved}:
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

def tse.quit(p: Bool, t: Bool, f: Bool, s: Bool) -> {Th.step(Th.Gate{p, t, f, s}, Th.Quit{}) == Throttle.step_spec(Th.Gate{p, t, f, s}, Th.Quit{}) : Th.Moved}:
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

def Throttle.throttle_step_exact(g, e):
  match g:
    case Th.Gate{p, t, f, s}:
      match e:
        case Th.Part{shows}:
          tse.part(p, t, f, s, shows)
        case Th.Fire{}:
          tse.fire(p, t, f, s)
        case Th.Settle{}:
          tse.settle(p, t, f, s)
        case Th.Finish{}:
          tse.finish(p, t, f, s)
        case Th.Quit{}:
          tse.quit(p, t, f, s)
