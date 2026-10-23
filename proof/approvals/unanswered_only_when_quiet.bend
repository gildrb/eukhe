# eukhe: the proof of LAW unanswered_only_when_quiet

import Base
import ../../bend/approvals.bend as Am
import ../../LAWS.bend as Laws
import ./base.bend as LA

# Unanswered{} is A, an answer or a ruling is Unit
def pa.ED(e: Am.End, a: Type, u: Type) -> Type:
  match e:
    case Am.Answered{x, y}:
      u
    case Am.Unanswered{}:
      a
    case Am.Ruled{x}:
      u

def pa.absurdE(-A: Type, -x: Nat, -y: Bool, e: {Am.Answered{x, y} == Am.Unanswered{} : Am.End}) -> A:
  %e : pa.ED(_, A, Unit)
  Unit{}

def pa.absurdR(-A: Type, -x: Nat, e: {Am.Ruled{x} == Am.Unanswered{} : Am.End}) -> A:
  %e : pa.ED(_, A, Unit)
  Unit{}

# a parent's end that is unanswered from its child is unanswered
def pa.up_unanswered(e: Am.End, h: {Am.End.up(e) == Am.Unanswered{} : Am.End}) -> {e == Am.Unanswered{} : Am.End}:
  match e:
    case Am.Answered{x, y}:
      pa.absurdE({Am.Answered{x, y} == Am.Unanswered{} : Am.End}, 1n+x, y, h)
    case Am.Unanswered{}:
      {==}
    case Am.Ruled{x}:
      pa.absurdR({Am.Ruled{x} == Am.Unanswered{} : Am.End}, 1n+x, h)

def pa.only_quiet(+ds: List<&2, Am.Desk>, none: {Am.Out.end(Am.route(ds)) == Am.Unanswered{} : Am.End}) -> {Am.quiet(ds) == True{} : Bool}:
  match ds:
    case Nil{}:
      {==}
    case d <> rest:
      match d:
        case Am.Away{}:
          pa.only_quiet(rest, pa.up_unanswered(Am.Out.end(Am.route(rest)), Equal.trans(Am.End, Am.End.up(Am.Out.end(Am.route(rest))), Am.Out.end(Am.Out.up(Am.route(rest))), Am.Unanswered{}, Equal.sym(Am.End, Am.Out.end(Am.Out.up(Am.route(rest))), Am.End.up(Am.Out.end(Am.route(rest))), LA.pa.end_up(Am.route(rest))), none)))
        case Am.Left{}:
          pa.only_quiet(rest, pa.up_unanswered(Am.Out.end(Am.route(rest)), Equal.trans(Am.End, Am.End.up(Am.Out.end(Am.route(rest))), Am.Out.end(Am.Out.first(Am.Out.up(Am.route(rest)))), Am.Unanswered{}, Equal.sym(Am.End, Am.Out.end(Am.Out.first(Am.Out.up(Am.route(rest)))), Am.End.up(Am.Out.end(Am.route(rest))), Equal.trans(Am.End, Am.Out.end(Am.Out.first(Am.Out.up(Am.route(rest)))), Am.Out.end(Am.Out.up(Am.route(rest))), Am.End.up(Am.Out.end(Am.route(rest))), LA.pa.end_first(Am.Out.up(Am.route(rest))), LA.pa.end_up(Am.route(rest)))), none)))
        case Am.Says{y}:
          pa.absurdE({Am.quiet(Am.Says{y} <> rest) == True{} : Bool}, 0n, y, none)
        case Am.Phone{}:
          pa.absurdR({Am.quiet(Am.Phone{} <> rest) == True{} : Bool}, 0n, none)
        case Am.PhoneLeft{}:
          pa.absurdR({Am.quiet(Am.PhoneLeft{} <> rest) == True{} : Bool}, 0n, none)

def Laws.unanswered_only_when_quiet(ds, none):
  pa.only_quiet(ds, none)
