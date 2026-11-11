# eukhe: the proof of LAW wait_arrival_wins

import Base
import ../../bend/wait.bend as Wt
import ../../laws/wait.bend as WaitLaws
import ./base.bend as LA

# The first exit wins
# -------------------

def pw.arrive(pre: List<&2, Wt.Sig>, +post: List<&2, Wt.Sig>, +l: Maybe<&2, Nat>, calm: {WaitLaws.ww_exits(LA.pw.up(l), pre) == False{} : Bool}) -> {Wt.go(List.append(&2, Wt.Sig, pre, Wt.Arrive{} <> post), Wt.Open{l}) == [Wt.Arrived{}] : List<&2, Wt.End>}:
  match pre:
    case Nil{}:
      %LA.pw.over(post) : {Wt.Arrived{} <> _ == [Wt.Arrived{}] : List<&2, Wt.End>}
      {==}
    case s <> +rest:
      match s:
        case Wt.Arrive{}:
          LA.pw.absurd({Wt.go(List.append(&2, Wt.Sig, Wt.Arrive{} <> rest, Wt.Arrive{} <> post), Wt.Open{l}) == [Wt.Arrived{}] : List<&2, Wt.End>}, calm)
        case Wt.Cancel{}:
          LA.pw.absurd({Wt.go(List.append(&2, Wt.Sig, Wt.Cancel{} <> rest, Wt.Arrive{} <> post), Wt.Open{l}) == [Wt.Arrived{}] : List<&2, Wt.End>}, Equal.trans(Bool, True{}, Bool.or(WaitLaws.ww_has(Wt.Arrive{}, rest), True{}), False{}, LA.pw.or_true(WaitLaws.ww_has(Wt.Arrive{}, rest)), calm))
        case Wt.Tick{}:
          match l:
            case None{}:
              pw.arrive(rest, post, None{}, calm)
            case Some{m}:
              match m:
                case 0n:
                  LA.pw.absurd({Wt.go(List.append(&2, Wt.Sig, Wt.Tick{} <> rest, Wt.Arrive{} <> post), Wt.Open{Some{0n}}) == [Wt.Arrived{}] : List<&2, Wt.End>}, Equal.trans(Bool, True{}, Bool.or(WaitLaws.ww_has(Wt.Arrive{}, rest), Bool.or(WaitLaws.ww_has(Wt.Cancel{}, rest), Nat.is_le(0n, WaitLaws.ww_count(Wt.Tick{}, rest)))), False{}, LA.pw.reached0(WaitLaws.ww_has(Wt.Arrive{}, rest), WaitLaws.ww_has(Wt.Cancel{}, rest), WaitLaws.ww_count(Wt.Tick{}, rest)), calm))
                case 1n+q:
                  pw.arrive(rest, post, Some{q}, calm)

def wait_arrival_wins(+dl: Maybe<&2, Nat>, +pre: List<&2, Wt.Sig>, +post: List<&2, Wt.Sig>, calm: {WaitLaws.ww_exits(dl, pre) == False{} : Bool}) -> {Wt.run(dl, List.append(&2, Wt.Sig, pre, Wt.Arrive{} <> post)) == [Wt.Arrived{}] : List<&2, Wt.End>}:
  match dl:
    case None{}:
      pw.arrive(pre, post, None{}, calm)
    case Some{d}:
      match d:
        case 0n:
          LA.pw.absurd({[Wt.Expired{}] == [Wt.Arrived{}] : List<&2, Wt.End>}, Equal.trans(Bool, True{}, Bool.or(WaitLaws.ww_has(Wt.Arrive{}, pre), Bool.or(WaitLaws.ww_has(Wt.Cancel{}, pre), Nat.is_le(0n, WaitLaws.ww_count(Wt.Tick{}, pre)))), False{}, LA.pw.reached0(WaitLaws.ww_has(Wt.Arrive{}, pre), WaitLaws.ww_has(Wt.Cancel{}, pre), WaitLaws.ww_count(Wt.Tick{}, pre)), calm))
        case 1n+m:
          pw.arrive(pre, post, Some{m}, calm)

def WaitLaws.wait_arrival_wins(dl, pre, post, calm):
  wait_arrival_wins(dl, pre, post, calm)
