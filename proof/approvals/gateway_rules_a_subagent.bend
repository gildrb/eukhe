# eukhe: the proof of LAW gateway_rules_a_subagent

import Base
import ../../bend/approvals.bend as Am
import ../../laws/approvals/route.bend as Approvals
import ../base/logic/logic.bend as LLogicLogic

# a step fares the same whichever session's end it is seen from
def pa.fate_up(+es: List<&2, Nat>, e: Am.End) -> {Am.fate(es, Am.End.up(e)) == Am.fate(es, e) : Am.Fate}:
  match e:
    case Am.Answered{a, y}:
      {==}
    case Am.Unanswered{}:
      {==}
    case Am.Ruled{a}:
      {==}

# so for a session that hands the question up
def pa.fate_up_is(+es: List<&2, Nat>, +o: Am.Out, -t: Am.Fate, h: {Am.fate(es, Am.Out.end(o)) == t : Am.Fate}) -> {Am.fate(es, Am.Out.end(Am.Out.up(o))) == t : Am.Fate}:
  match o:
    case Am.Out{s, e}:
      Equal.trans(Am.Fate, Am.fate(es, Am.End.up(e)), Am.fate(es, e), t, pa.fate_up(es, e), h)

# and for one that showed it first
def pa.fate_first_up_is(+es: List<&2, Nat>, +o: Am.Out, -t: Am.Fate, h: {Am.fate(es, Am.Out.end(o)) == t : Am.Fate}) -> {Am.fate(es, Am.Out.end(Am.Out.first(Am.Out.up(o)))) == t : Am.Fate}:
  match o:
    case Am.Out{s, e}:
      Equal.trans(Am.Fate, Am.fate(es, Am.End.up(e)), Am.fate(es, e), t, pa.fate_up(es, e), h)

def pa.subagent(+below: List<&2, Am.Desk>, quiet: {Am.quiet(below) == True{} : Bool}, +es: List<&2, Nat>, +above: List<&2, Am.Desk>) -> {Am.fate(es, Am.Out.end(Am.route(List.append(&2, Am.Desk, below, Am.Phone{} <> above)))) == Am.fate(es, Am.Out.end(Am.route([Am.Phone{}]))) : Am.Fate}:
  match below:
    case Nil{}:
      {==}
    case d <> rest:
      match d:
        case Am.Away{}:
          pa.fate_up_is(es, Am.route(List.append(&2, Am.Desk, rest, Am.Phone{} <> above)), Am.fate(es, Am.Out.end(Am.route([Am.Phone{}]))), pa.subagent(rest, quiet, es, above))
        case Am.Left{}:
          pa.fate_first_up_is(es, Am.route(List.append(&2, Am.Desk, rest, Am.Phone{} <> above)), Am.fate(es, Am.Out.end(Am.route([Am.Phone{}]))), pa.subagent(rest, quiet, es, above))
        case Am.Says{z}:
          LLogicLogic.approvals.pa.absurdF({Am.fate(es, Am.Out.end(Am.route(List.append(&2, Am.Desk, Am.Says{z} <> rest, Am.Phone{} <> above)))) == Am.fate(es, Am.Out.end(Am.route([Am.Phone{}]))) : Am.Fate}, quiet)
        case Am.Phone{}:
          LLogicLogic.approvals.pa.absurdF({Am.fate(es, Am.Out.end(Am.route(List.append(&2, Am.Desk, Am.Phone{} <> rest, Am.Phone{} <> above)))) == Am.fate(es, Am.Out.end(Am.route([Am.Phone{}]))) : Am.Fate}, quiet)
        case Am.PhoneLeft{}:
          LLogicLogic.approvals.pa.absurdF({Am.fate(es, Am.Out.end(Am.route(List.append(&2, Am.Desk, Am.PhoneLeft{} <> rest, Am.Phone{} <> above)))) == Am.fate(es, Am.Out.end(Am.route([Am.Phone{}]))) : Am.Fate}, quiet)

def Approvals.gateway_rules_a_subagent(below, quiet, es, above):
  pa.subagent(below, quiet, es, above)
