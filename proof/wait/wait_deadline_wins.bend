# eukhe: the proof of LAW wait_deadline_wins
# By induction on the signals before the deadline: an event or a cancel
# among them contradicts the premise; a tick counts the deadline down;
# the tick that passes it ends the wait as expired, and an ended wait
# reports nothing more (LA.pw.over). A deadline of 0 has passed at once.

import Base
import ../../bend/wait.bend as Wt
import ../../laws/wait.bend as WaitLaws
import ./base.bend as LA

def pw.expire(pre: List<&2, Wt.Sig>, +post: List<&2, Wt.Sig>, +l: Maybe<&2, Nat>, quiet: {Bool.or(WaitLaws.ww_has(Wt.Arrive{}, pre), WaitLaws.ww_has(Wt.Cancel{}, pre)) == False{} : Bool}, due: {WaitLaws.ww_passed(LA.pw.up(l), WaitLaws.ww_count(Wt.Tick{}, pre)) == True{} : Bool}) -> {Wt.go(List.append(&2, Wt.Sig, pre, post), Wt.Open{l}) == [Wt.Expired{}] : List<&2, Wt.End>}:
  match pre:
    case Nil{}:
      match l:
        case None{}:
          LA.pw.absurd({Wt.go(post, Wt.Open{None{}}) == [Wt.Expired{}] : List<&2, Wt.End>}, Equal.sym(Bool, False{}, True{}, due))
        case Some{m}:
          LA.pw.absurd({Wt.go(post, Wt.Open{Some{m}}) == [Wt.Expired{}] : List<&2, Wt.End>}, Equal.sym(Bool, False{}, True{}, due))
    case s <> +rest:
      match s:
        case Wt.Arrive{}:
          LA.pw.absurd({Wt.go(List.append(&2, Wt.Sig, Wt.Arrive{} <> rest, post), Wt.Open{l}) == [Wt.Expired{}] : List<&2, Wt.End>}, quiet)
        case Wt.Cancel{}:
          LA.pw.absurd({Wt.go(List.append(&2, Wt.Sig, Wt.Cancel{} <> rest, post), Wt.Open{l}) == [Wt.Expired{}] : List<&2, Wt.End>}, Equal.trans(Bool, True{}, Bool.or(WaitLaws.ww_has(Wt.Arrive{}, rest), True{}), False{}, LA.pw.or_true(WaitLaws.ww_has(Wt.Arrive{}, rest)), quiet))
        case Wt.Tick{}:
          match l:
            case None{}:
              pw.expire(rest, post, None{}, quiet, due)
            case Some{m}:
              match m:
                case 0n:
                  %LA.pw.over(List.append(&2, Wt.Sig, rest, post)) : {Wt.Expired{} <> _ == [Wt.Expired{}] : List<&2, Wt.End>}
                  {==}
                case 1n+q:
                  pw.expire(rest, post, Some{q}, quiet, due)

def wait_deadline_wins(+dl: Maybe<&2, Nat>, +pre: List<&2, Wt.Sig>, +post: List<&2, Wt.Sig>, quiet: {Bool.or(WaitLaws.ww_has(Wt.Arrive{}, pre), WaitLaws.ww_has(Wt.Cancel{}, pre)) == False{} : Bool}, due: {WaitLaws.ww_passed(dl, WaitLaws.ww_count(Wt.Tick{}, pre)) == True{} : Bool}) -> {Wt.run(dl, List.append(&2, Wt.Sig, pre, post)) == [Wt.Expired{}] : List<&2, Wt.End>}:
  match dl:
    case None{}:
      pw.expire(pre, post, None{}, quiet, due)
    case Some{d}:
      match d:
        case 0n:
          {==}
        case 1n+m:
          pw.expire(pre, post, Some{m}, quiet, due)

def WaitLaws.wait_deadline_wins(dl, pre, post, quiet, due):
  wait_deadline_wins(dl, pre, post, quiet, due)
