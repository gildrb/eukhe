# eukhe: the proof of LAW child_answered_by_root

import Base
import ../../bend/approvals.bend as Am
import ../../laws/approvals.bend as Approvals
import ./base.bend as LA

def pa.root(+below: List<&2, Am.Desk>, quiet: {Am.quiet(below) == True{} : Bool}, +yes: Bool) -> {Am.Out.end(Am.route(List.append(&2, Am.Desk, below, [Am.Says{yes}]))) == Am.Answered{List.length(&2, Am.Desk, below), yes} : Am.End}:
  LA.pa.nearest(below, quiet, yes, Nil{})

# (G5) A child's question reaches its root's user

def Approvals.child_answered_by_root(below, quiet, yes):
  pa.root(below, quiet, yes)
