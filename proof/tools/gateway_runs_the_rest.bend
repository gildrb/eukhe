# eukhe: the proof of LAW gateway_runs_the_rest

import Base
import ../../bend/approvals.bend as Am
import ../../bend/tools.bend as Tl
import ../../laws/tools.bend as Tools
import ./base.bend as LA

def pa.runs_the_rest(+es: List<&2, Nat>, not_protected: {Tl.elem(es, 5n) == False{} : Bool}, not_secret: {Tl.elem(es, 6n) == False{} : Bool}, +above: List<&2, Am.Desk>) -> {Am.fate(es, Am.Out.end(Am.route(Am.Phone{} <> above))) == Am.Runs{} : Am.Fate}:
  LA.pa.guard_neither(Tl.elem(es, 5n), Tl.elem(es, 6n), not_protected, not_secret)

def Tools.gateway_runs_the_rest(es, not_protected, not_secret, above):
  pa.runs_the_rest(es, not_protected, not_secret, above)
