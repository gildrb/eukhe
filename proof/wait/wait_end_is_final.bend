# eukhe: the proof of LAW wait_end_is_final

import Base
import ../../bend/wait.bend as Wt
import ../../LAWS.bend as Laws
import ./base.bend as LA

# No later than the deadline or the cancel
# ----------------------------------------

def pw.bound(pre: List<&2, Wt.Sig>, +post: List<&2, Wt.Sig>, +l: Maybe<&2, Nat>, stop: {Wt.stops(LA.pw.up(l), pre) == True{} : Bool}) -> {Wt.go(List.append(&2, Wt.Sig, pre, post), Wt.Open{l}) == Wt.go(pre, Wt.Open{l}) : List<&2, Wt.End>}:
  match pre:
    case Nil{}:
      match l:
        case None{}:
          LA.pw.absurd({Wt.go(post, Wt.Open{None{}}) == Nil{} : List<&2, Wt.End>}, Equal.sym(Bool, False{}, True{}, stop))
        case Some{m}:
          LA.pw.absurd({Wt.go(post, Wt.Open{Some{m}}) == Nil{} : List<&2, Wt.End>}, Equal.sym(Bool, False{}, True{}, stop))
    case s <> +rest:
      match s:
        case Wt.Arrive{}:
          %LA.pw.over(List.append(&2, Wt.Sig, rest, post)) : {Wt.Arrived{} <> _ == Wt.Arrived{} <> Wt.go(rest, Wt.Over{}) : List<&2, Wt.End>}
          %LA.pw.over(rest) : {[Wt.Arrived{}] == Wt.Arrived{} <> _ : List<&2, Wt.End>}
          {==}
        case Wt.Cancel{}:
          %LA.pw.over(List.append(&2, Wt.Sig, rest, post)) : {Wt.Cancelled{} <> _ == Wt.Cancelled{} <> Wt.go(rest, Wt.Over{}) : List<&2, Wt.End>}
          %LA.pw.over(rest) : {[Wt.Cancelled{}] == Wt.Cancelled{} <> _ : List<&2, Wt.End>}
          {==}
        case Wt.Tick{}:
          match l:
            case None{}:
              pw.bound(rest, post, None{}, stop)
            case Some{m}:
              match m:
                case 0n:
                  %LA.pw.over(List.append(&2, Wt.Sig, rest, post)) : {Wt.Expired{} <> _ == Wt.Expired{} <> Wt.go(rest, Wt.Over{}) : List<&2, Wt.End>}
                  %LA.pw.over(rest) : {[Wt.Expired{}] == Wt.Expired{} <> _ : List<&2, Wt.End>}
                  {==}
                case 1n+q:
                  pw.bound(rest, post, Some{q}, stop)

def wait_end_is_final(+dl: Maybe<&2, Nat>, +pre: List<&2, Wt.Sig>, +post: List<&2, Wt.Sig>, stop: {Wt.stops(dl, pre) == True{} : Bool}) -> {Wt.run(dl, List.append(&2, Wt.Sig, pre, post)) == Wt.run(dl, pre) : List<&2, Wt.End>}:
  match dl:
    case None{}:
      pw.bound(pre, post, None{}, stop)
    case Some{d}:
      match d:
        case 0n:
          {==}
        case 1n+m:
          pw.bound(pre, post, Some{m}, stop)

def Laws.wait_end_is_final(dl, pre, post, stop):
  wait_end_is_final(dl, pre, post, stop)
