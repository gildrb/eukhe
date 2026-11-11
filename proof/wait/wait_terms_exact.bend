# eukhe: the proof of LAW wait_terms_exact
# Each term by induction on the signals; stops and exits from their parts.

import Base
import ../../bend/wait.bend as Wt
import ../../laws/wait.bend as WaitLaws

def wt.arrive(xs: List<&2, Wt.Sig>) -> {WaitLaws.arrive_spec(xs) == Wt.has_arrive(xs) : Bool}:
  match xs:
    case Nil{}:
      {==}
    case s <> rest:
      match s:
        case Wt.Arrive{}:
          {==}
        case Wt.Tick{}:
          wt.arrive(rest)
        case Wt.Cancel{}:
          wt.arrive(rest)

def wt.cancel(xs: List<&2, Wt.Sig>) -> {WaitLaws.cancel_spec(xs) == Wt.has_cancel(xs) : Bool}:
  match xs:
    case Nil{}:
      {==}
    case s <> rest:
      match s:
        case Wt.Arrive{}:
          wt.cancel(rest)
        case Wt.Tick{}:
          wt.cancel(rest)
        case Wt.Cancel{}:
          {==}

def wt.ticks(xs: List<&2, Wt.Sig>) -> {WaitLaws.ticks_spec(xs) == Wt.ticks(xs) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case s <> rest:
      match s:
        case Wt.Arrive{}:
          wt.ticks(rest)
        case Wt.Tick{}:
          %wt.ticks(rest) : {1n+WaitLaws.ticks_spec(rest) == 1n+_ : Nat}
          {==}
        case Wt.Cancel{}:
          wt.ticks(rest)

def wt.reached(dl: Maybe<&2, Nat>, k: Nat) -> {WaitLaws.reached_spec(dl, k) == Wt.reached(dl, k) : Bool}:
  match dl:
    case None{}:
      {==}
    case Some{d}:
      {==}

def wt.stops(+dl: Maybe<&2, Nat>, +xs: List<&2, Wt.Sig>) -> {Wt.stops(dl, xs) == Bool.or(WaitLaws.cancel_spec(xs), WaitLaws.reached_spec(dl, WaitLaws.ticks_spec(xs))) : Bool}:
  %wt.cancel(xs) : {Bool.or(_, Wt.reached(dl, Wt.ticks(xs))) == Bool.or(WaitLaws.cancel_spec(xs), WaitLaws.reached_spec(dl, WaitLaws.ticks_spec(xs))) : Bool}
  %wt.ticks(xs) : {Bool.or(WaitLaws.cancel_spec(xs), Wt.reached(dl, _)) == Bool.or(WaitLaws.cancel_spec(xs), WaitLaws.reached_spec(dl, WaitLaws.ticks_spec(xs))) : Bool}
  %wt.reached(dl, WaitLaws.ticks_spec(xs)) : {Bool.or(WaitLaws.cancel_spec(xs), _) == Bool.or(WaitLaws.cancel_spec(xs), WaitLaws.reached_spec(dl, WaitLaws.ticks_spec(xs))) : Bool}
  {==}

def wt.exits(+dl: Maybe<&2, Nat>, +xs: List<&2, Wt.Sig>) -> {Wt.exits(dl, xs) == Bool.or(WaitLaws.arrive_spec(xs), Bool.or(WaitLaws.cancel_spec(xs), WaitLaws.reached_spec(dl, WaitLaws.ticks_spec(xs)))) : Bool}:
  %wt.arrive(xs) : {Bool.or(_, Wt.stops(dl, xs)) == Bool.or(WaitLaws.arrive_spec(xs), Bool.or(WaitLaws.cancel_spec(xs), WaitLaws.reached_spec(dl, WaitLaws.ticks_spec(xs)))) : Bool}
  %Equal.sym(Bool, Wt.stops(dl, xs), Bool.or(WaitLaws.cancel_spec(xs), WaitLaws.reached_spec(dl, WaitLaws.ticks_spec(xs))), wt.stops(dl, xs)) : {Bool.or(WaitLaws.arrive_spec(xs), _) == Bool.or(WaitLaws.arrive_spec(xs), Bool.or(WaitLaws.cancel_spec(xs), WaitLaws.reached_spec(dl, WaitLaws.ticks_spec(xs)))) : Bool}
  {==}

def wt.once(b: Bool) -> {Wt.once(b) == WaitLaws.once_spec(b) : Nat}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def WaitLaws.wait_terms_exact(dl, xs, k, b):
  (Equal.sym(Bool, WaitLaws.arrive_spec(xs), Wt.has_arrive(xs), wt.arrive(xs)), (Equal.sym(Bool, WaitLaws.cancel_spec(xs), Wt.has_cancel(xs), wt.cancel(xs)), (Equal.sym(Nat, WaitLaws.ticks_spec(xs), Wt.ticks(xs), wt.ticks(xs)), (Equal.sym(Bool, WaitLaws.reached_spec(dl, k), Wt.reached(dl, k), wt.reached(dl, k)), (wt.stops(dl, xs), (wt.exits(dl, xs), wt.once(b)))))))
