# eukhe: lemmas the proofs of area approvals share

import Base
import ../../bend/approvals.bend as Am
import ../base.bend as L

# Outcomes
# --------

def pa.end_up(o: Am.Out) -> {Am.Out.end(Am.Out.up(o)) == Am.End.up(Am.Out.end(o)) : Am.End}:
  match o:
    case Am.Out{s, e}:
      {==}

def pa.end_first(o: Am.Out) -> {Am.Out.end(Am.Out.first(o)) == Am.Out.end(o) : Am.End}:
  match o:
    case Am.Out{s, e}:
      {==}

# the end of a parent's outcome seen from its child, by the parent's end
def pa.end_up_is(+o: Am.Out, -e: Am.End, h: {Am.Out.end(o) == e : Am.End}) -> {Am.Out.end(Am.Out.up(o)) == Am.End.up(e) : Am.End}:
  Equal.trans(Am.End, Am.Out.end(Am.Out.up(o)), Am.End.up(Am.Out.end(o)), Am.End.up(e), pa.end_up(o), Equal.cong(Am.End, Am.End, x => Am.End.up(x), Am.Out.end(o), e, h))

# so for a session that showed the question first
def pa.end_first_up_is(+o: Am.Out, -e: Am.End, h: {Am.Out.end(o) == e : Am.End}) -> {Am.Out.end(Am.Out.first(Am.Out.up(o))) == Am.End.up(e) : Am.End}:
  Equal.trans(Am.End, Am.Out.end(Am.Out.first(Am.Out.up(o))), Am.Out.end(Am.Out.up(o)), Am.End.up(e), pa.end_first(Am.Out.up(o)), pa.end_up_is(o, e, h))

# The laws
# --------

def pa.nearest(+below: List<&2, Am.Desk>, quiet: {Am.quiet(below) == True{} : Bool}, +yes: Bool, +above: List<&2, Am.Desk>) -> {Am.Out.end(Am.route(List.append(&2, Am.Desk, below, Am.Says{yes} <> above))) == Am.Answered{List.length(&2, Am.Desk, below), yes} : Am.End}:
  match below:
    case Nil{}:
      {==}
    case d <> rest:
      match d:
        case Am.Away{}:
          pa.end_up_is(Am.route(List.append(&2, Am.Desk, rest, Am.Says{yes} <> above)), Am.Answered{List.length(&2, Am.Desk, rest), yes}, pa.nearest(rest, quiet, yes, above))
        case Am.Left{}:
          pa.end_first_up_is(Am.route(List.append(&2, Am.Desk, rest, Am.Says{yes} <> above)), Am.Answered{List.length(&2, Am.Desk, rest), yes}, pa.nearest(rest, quiet, yes, above))
        case Am.Says{z}:
          L.approvals.pa.absurdF({Am.Out.end(Am.route(List.append(&2, Am.Desk, Am.Says{z} <> rest, Am.Says{yes} <> above))) == Am.Answered{List.length(&2, Am.Desk, Am.Says{z} <> rest), yes} : Am.End}, quiet)
        case Am.Phone{}:
          L.approvals.pa.absurdF({Am.Out.end(Am.route(List.append(&2, Am.Desk, Am.Phone{} <> rest, Am.Says{yes} <> above))) == Am.Answered{List.length(&2, Am.Desk, Am.Phone{} <> rest), yes} : Am.End}, quiet)
        case Am.PhoneLeft{}:
          L.approvals.pa.absurdF({Am.Out.end(Am.route(List.append(&2, Am.Desk, Am.PhoneLeft{} <> rest, Am.Says{yes} <> above))) == Am.Answered{List.length(&2, Am.Desk, Am.PhoneLeft{} <> rest), yes} : Am.End}, quiet)
