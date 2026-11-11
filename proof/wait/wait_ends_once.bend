# eukhe: the proof of LAW wait_ends_once

import Base
import ../../bend/wait.bend as Wt
import ../../laws/wait.bend as WaitLaws
import ./base.bend as LA

# Exactly once
# ------------

def pw.once(xs: List<&2, Wt.Sig>, +l: Maybe<&2, Nat>) -> {List.length(&2, Wt.End, Wt.go(xs, Wt.Open{l})) == WaitLaws.ww_bit(WaitLaws.ww_exits(LA.pw.up(l), xs)) : Nat}:
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
          %LA.pw.over(rest) : {1n+List.length(&2, Wt.End, _) == WaitLaws.ww_bit(Bool.or(WaitLaws.ww_has(Wt.Arrive{}, rest), True{})) : Nat}
          %LA.pw.or_true(WaitLaws.ww_has(Wt.Arrive{}, rest)) : {1n == WaitLaws.ww_bit(_) : Nat}
          {==}
        case Wt.Tick{}:
          match l:
            case None{}:
              pw.once(rest, None{})
            case Some{m}:
              match m:
                case 0n:
                  %LA.pw.over(rest) : {1n+List.length(&2, Wt.End, _) == WaitLaws.ww_bit(Bool.or(WaitLaws.ww_has(Wt.Arrive{}, rest), Bool.or(WaitLaws.ww_has(Wt.Cancel{}, rest), Nat.is_le(0n, WaitLaws.ww_count(Wt.Tick{}, rest))))) : Nat}
                  %LA.pw.reached0(WaitLaws.ww_has(Wt.Arrive{}, rest), WaitLaws.ww_has(Wt.Cancel{}, rest), WaitLaws.ww_count(Wt.Tick{}, rest)) : {1n == WaitLaws.ww_bit(_) : Nat}
                  {==}
                case 1n+q:
                  pw.once(rest, Some{q})

# The laws
# --------

def wait_ends_once(+dl: Maybe<&2, Nat>, +xs: List<&2, Wt.Sig>) -> {List.length(&2, Wt.End, Wt.run(dl, xs)) == WaitLaws.ww_bit(WaitLaws.ww_exits(dl, xs)) : Nat}:
  match dl:
    case None{}:
      pw.once(xs, None{})
    case Some{d}:
      match d:
        case 0n:
          %LA.pw.reached0(WaitLaws.ww_has(Wt.Arrive{}, xs), WaitLaws.ww_has(Wt.Cancel{}, xs), WaitLaws.ww_count(Wt.Tick{}, xs)) : {1n == WaitLaws.ww_bit(_) : Nat}
          {==}
        case 1n+m:
          pw.once(xs, Some{m})

# (D4) Every wait has an exit

def WaitLaws.wait_ends_once(dl, xs):
  wait_ends_once(dl, xs)
