# eukhe: the proof of LAW wait_any_step_counts_moves
#
# PROOF: by the event and the phase; a settle of a running job and an
# unwatch of a kept one place it by a route: either route's answer
# counts one delivery exactly when it sends (wsc.live, wsc.kept).

import Base
import ../../bend/wait_any.bend as Wa
import ../../spec/durable/wait_any.bend as WaSpec
import ../../laws/wait_any.bend as WaitAny

def wsc.live(r: Wa.Route, +w: Nat) -> {WaSpec.out_k(Wa.deliver(r, w)) == WaSpec.moved(Wa.Live{}, WaSpec.out_phase(Wa.deliver(r, w))) : Nat}:
  match r:
    case Wa.ToWaiter{}:
      {==}
    case Wa.ToNotice{}:
      {==}

def wsc.kept(r: Wa.Route, +w: Nat) -> {WaSpec.out_k(Wa.deliver(r, w)) == WaSpec.moved(Wa.Kept{}, WaSpec.out_phase(Wa.deliver(r, w))) : Nat}:
  match r:
    case Wa.ToWaiter{}:
      {==}
    case Wa.ToNotice{}:
      {==}

def WaitAny.wait_any_step_counts_moves(wake, d, e):
  match d:
    case Wa.D{+w, p}:
      match p:
        case Wa.Live{}:
          match e:
            case Wa.Watch{}:
              {==}
            case Wa.Unwatch{}:
              {==}
            case Wa.Settles{}:
              wsc.live(Wa.route(Wa.watched(w), wake), w)
            case Wa.Taken{}:
              {==}
        case Wa.Kept{}:
          match e:
            case Wa.Watch{}:
              {==}
            case Wa.Unwatch{}:
              wsc.kept(Wa.route(Wa.watched(Wa.unwatch.left(w)), wake), Wa.unwatch.left(w))
            case Wa.Settles{}:
              {==}
            case Wa.Taken{}:
              {==}
        case Wa.Sent{}:
          match e:
            case Wa.Watch{}:
              {==}
            case Wa.Unwatch{}:
              {==}
            case Wa.Settles{}:
              {==}
            case Wa.Taken{}:
              {==}
