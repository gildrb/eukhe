# eukhe: the proof of LAW wait_any_step_spec
#
# PROOF: by the event and the phase; an unwatch leaves the spec's watchers (wa.left_eq); a settle of a running job and an unwatch of a kept one place it by the route, which agrees for every wake path and none, one or more watchers (wa.live_at, wa.kept_at).

import Base
import ../../bend/wait_any.bend as Wa
import ../../spec/durable/wait_any.bend as WaSpec
import ../../laws/wait_any.bend as WaitAny
import ./base.bend as LW


# one watcher fewer, none staying none
def wa.left_eq(w: Nat) -> {Wa.unwatch.left(w) == Nat.sub(w, 1n) : Nat}:
  match w:
    case 0n:
      {==}
    case 1n+q:
      match q:
        case 0n:
          {==}
        case 1n+r:
          {==}

# a running job that settles with w watchers
def wa.live_at(+wake: Bool, +w: Nat) -> {Wa.deliver(Wa.route(Wa.watched(w), wake), w) == WaSpec.step.at(wake, w, Wa.Live{}, Wa.Settles{}) : Wa.Out}:
  match wake:
    case True{}:
      match w:
        case 0n:
          {==}
        case 1n+q:
          {==}
    case False{}:
      match w:
        case 0n:
          {==}
        case 1n+q:
          {==}

# a kept result whose watcher leaves, w watchers left
def wa.kept_at(+wake: Bool, +w: Nat) -> {Wa.deliver(Wa.route(Wa.watched(w), wake), w) == WaSpec.step.at(wake, w, Wa.Kept{}, Wa.Unwatch{}) : Wa.Out}:
  match wake:
    case True{}:
      match w:
        case 0n:
          {==}
        case 1n+q:
          {==}
    case False{}:
      match w:
        case 0n:
          {==}
        case 1n+q:
          {==}

def WaitAny.wait_any_step_spec(wake, d, e):
  match d:
    case Wa.D{+w, p}:
      match p:
        case Wa.Live{}:
          match e:
            case Wa.Watch{}:
              {==}
            case Wa.Unwatch{}:
              %wa.left_eq(w) : {Wa.Out{Wa.D{Wa.unwatch.left(w), Wa.Live{}}, 0n} == Wa.Out{Wa.D{_, Wa.Live{}}, 0n} : Wa.Out}
              {==}
            case Wa.Settles{}:
              wa.live_at(wake, w)
            case Wa.Taken{}:
              {==}
        case Wa.Kept{}:
          match e:
            case Wa.Watch{}:
              {==}
            case Wa.Unwatch{}:
              %wa.left_eq(w) : {Wa.deliver(Wa.route(Wa.watched(Wa.unwatch.left(w)), wake), Wa.unwatch.left(w)) == WaSpec.step.at(wake, _, Wa.Kept{}, Wa.Unwatch{}) : Wa.Out}
              wa.kept_at(wake, Wa.unwatch.left(w))
            case Wa.Settles{}:
              {==}
            case Wa.Taken{}:
              {==}
        case Wa.Sent{}:
          match e:
            case Wa.Watch{}:
              {==}
            case Wa.Unwatch{}:
              %wa.left_eq(w) : {Wa.Out{Wa.D{Wa.unwatch.left(w), Wa.Sent{}}, 0n} == Wa.Out{Wa.D{_, Wa.Sent{}}, 0n} : Wa.Out}
              {==}
            case Wa.Settles{}:
              {==}
            case Wa.Taken{}:
              {==}
