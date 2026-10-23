# eukhe: the proof of LAW wait_ends_once

import Base
import ../../bend/wait.bend as Wt
import ../../LAWS.bend as Laws
import ./base.bend as LA

# Exactly once
# ------------

def pw.once(xs: List<&2, Wt.Sig>, +l: Maybe<&2, Nat>) -> {List.length(&2, Wt.End, Wt.go(xs, Wt.Open{l})) == Wt.once(Wt.exits(LA.pw.up(l), xs)) : Nat}:
  match xs:
    case Nil{}:
      match l:
        case None{}:
          {==}
        case Some{m}:
          {==}
    case s <> +rest:
      match s:
        case Wt.Arrive{}:
          %LA.pw.over(rest) : {1n+List.length(&2, Wt.End, _) == 1n : Nat}
          {==}
        case Wt.Cancel{}:
          %LA.pw.over(rest) : {1n+List.length(&2, Wt.End, _) == Wt.once(Bool.or(Wt.has_arrive(rest), True{})) : Nat}
          %LA.pw.or_true(Wt.has_arrive(rest)) : {1n == Wt.once(_) : Nat}
          {==}
        case Wt.Tick{}:
          match l:
            case None{}:
              pw.once(rest, None{})
            case Some{m}:
              match m:
                case 0n:
                  %LA.pw.over(rest) : {1n+List.length(&2, Wt.End, _) == Wt.once(Bool.or(Wt.has_arrive(rest), Bool.or(Wt.has_cancel(rest), Nat.is_le(0n, Wt.ticks(rest))))) : Nat}
                  %LA.pw.reached0(Wt.has_arrive(rest), Wt.has_cancel(rest), Wt.ticks(rest)) : {1n == Wt.once(_) : Nat}
                  {==}
                case 1n+q:
                  pw.once(rest, Some{q})

# The laws
# --------

def wait_ends_once(+dl: Maybe<&2, Nat>, +xs: List<&2, Wt.Sig>) -> {List.length(&2, Wt.End, Wt.run(dl, xs)) == Wt.once(Wt.exits(dl, xs)) : Nat}:
  match dl:
    case None{}:
      pw.once(xs, None{})
    case Some{d}:
      match d:
        case 0n:
          %LA.pw.reached0(Wt.has_arrive(xs), Wt.has_cancel(xs), Wt.ticks(xs)) : {1n == Wt.once(_) : Nat}
          {==}
        case 1n+m:
          pw.once(xs, Some{m})

# (H6) Every other wait has an exit

def Laws.wait_ends_once(dl, xs):
  wait_ends_once(dl, xs)
