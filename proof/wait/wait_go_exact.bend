# eukhe: the proof of LAW wait_go_exact
# By induction on the signals: an ended wait walks to nothing; an open one
# ends at its first event, cancel or passing tick, then walks ended.

import Base
import ../../bend/wait.bend as Wt
import ../../laws/wait.bend as WaitLaws

def wg.over(xs: List<&2, Wt.Sig>) -> {Nil{} == Wt.go(xs, Wt.Over{}) : List<&2, Wt.End>}:
  match xs:
    case Nil{}:
      {==}
    case s <> rest:
      wg.over(rest)

def wg.spec_over(xs: List<&2, Wt.Sig>) -> {Nil{} == WaitLaws.go_spec(xs, Wt.Over{}) : List<&2, Wt.End>}:
  match xs:
    case Nil{}:
      {==}
    case s <> rest:
      match s:
        case Wt.Arrive{}:
          {==}
        case Wt.Cancel{}:
          {==}
        case Wt.Tick{}:
          {==}

def wg.open(xs: List<&2, Wt.Sig>, left: Maybe<&2, Nat>) -> {Wt.go(xs, Wt.Open{left}) == WaitLaws.go_spec(xs, Wt.Open{left}) : List<&2, Wt.End>}:
  match xs:
    case Nil{}:
      {==}
    case s <> rest:
      match s:
        case Wt.Arrive{}:
          %wg.over(rest) : {Wt.Arrived{} <> _ == [Wt.Arrived{}] : List<&2, Wt.End>}
          {==}
        case Wt.Cancel{}:
          %wg.over(rest) : {Wt.Cancelled{} <> _ == [Wt.Cancelled{}] : List<&2, Wt.End>}
          {==}
        case Wt.Tick{}:
          match left:
            case None{}:
              wg.open(rest, None{})
            case Some{m}:
              match m:
                case 0n:
                  %wg.over(rest) : {Wt.Expired{} <> _ == [Wt.Expired{}] : List<&2, Wt.End>}
                  {==}
                case 1n+q:
                  wg.open(rest, Some{q})

def WaitLaws.wait_go_exact(xs, w):
  match w:
    case Wt.Over{}:
      %wg.spec_over(xs) : {Wt.go(xs, Wt.Over{}) == _ : List<&2, Wt.End>}
      Equal.sym(List<&2, Wt.End>, Nil{}, Wt.go(xs, Wt.Over{}), wg.over(xs))
    case Wt.Open{left}:
      wg.open(xs, left)
