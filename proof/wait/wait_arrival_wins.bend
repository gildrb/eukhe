# eukhe: the proof of LAW wait_arrival_wins

import Base
import ../../bend/wait.bend as Wt
import ../../LAWS.bend as Laws
import ./base.bend as LA

# The first exit wins
# -------------------

def pw.arrive(pre: List<&2, Wt.Sig>, +post: List<&2, Wt.Sig>, +l: Maybe<&2, Nat>, calm: {Wt.exits(LA.pw.up(l), pre) == False{} : Bool}) -> {Wt.go(List.append(&2, Wt.Sig, pre, Wt.Arrive{} <> post), Wt.Open{l}) == [Wt.Arrived{}] : List<&2, Wt.End>}:
  match pre:
    case Nil{}:
      %LA.pw.over(post) : {Wt.Arrived{} <> _ == [Wt.Arrived{}] : List<&2, Wt.End>}
      {==}
    case s <> +rest:
      match s:
        case Wt.Arrive{}:
          LA.pw.absurd({Wt.go(List.append(&2, Wt.Sig, Wt.Arrive{} <> rest, Wt.Arrive{} <> post), Wt.Open{l}) == [Wt.Arrived{}] : List<&2, Wt.End>}, calm)
        case Wt.Cancel{}:
          LA.pw.absurd({Wt.go(List.append(&2, Wt.Sig, Wt.Cancel{} <> rest, Wt.Arrive{} <> post), Wt.Open{l}) == [Wt.Arrived{}] : List<&2, Wt.End>}, Equal.trans(Bool, True{}, Bool.or(Wt.has_arrive(rest), True{}), False{}, LA.pw.or_true(Wt.has_arrive(rest)), calm))
        case Wt.Tick{}:
          match l:
            case None{}:
              pw.arrive(rest, post, None{}, calm)
            case Some{m}:
              match m:
                case 0n:
                  LA.pw.absurd({Wt.go(List.append(&2, Wt.Sig, Wt.Tick{} <> rest, Wt.Arrive{} <> post), Wt.Open{Some{0n}}) == [Wt.Arrived{}] : List<&2, Wt.End>}, Equal.trans(Bool, True{}, Bool.or(Wt.has_arrive(rest), Bool.or(Wt.has_cancel(rest), Nat.is_le(0n, Wt.ticks(rest)))), False{}, LA.pw.reached0(Wt.has_arrive(rest), Wt.has_cancel(rest), Wt.ticks(rest)), calm))
                case 1n+q:
                  pw.arrive(rest, post, Some{q}, calm)

def wait_arrival_wins(+dl: Maybe<&2, Nat>, +pre: List<&2, Wt.Sig>, +post: List<&2, Wt.Sig>, calm: {Wt.exits(dl, pre) == False{} : Bool}) -> {Wt.run(dl, List.append(&2, Wt.Sig, pre, Wt.Arrive{} <> post)) == [Wt.Arrived{}] : List<&2, Wt.End>}:
  match dl:
    case None{}:
      pw.arrive(pre, post, None{}, calm)
    case Some{d}:
      match d:
        case 0n:
          LA.pw.absurd({[Wt.Expired{}] == [Wt.Arrived{}] : List<&2, Wt.End>}, Equal.trans(Bool, True{}, Bool.or(Wt.has_arrive(pre), Bool.or(Wt.has_cancel(pre), Nat.is_le(0n, Wt.ticks(pre)))), False{}, LA.pw.reached0(Wt.has_arrive(pre), Wt.has_cancel(pre), Wt.ticks(pre)), calm))
        case 1n+m:
          pw.arrive(pre, post, Some{m}, calm)

def Laws.wait_arrival_wins(dl, pre, post, calm):
  wait_arrival_wins(dl, pre, post, calm)
