# eukhe: the proof of LAW dash_closed_runs_nothing

import Base
import ../../bend/dash.bend as Da
import ../../LAWS.bend as Laws
import ./base.bend as LA

def pa.closed_runs_nothing(+s: Da.St, +c: Nat, +evs: List<&2, Da.Ev>, +closed: {Da.held(c, Da.St.conns(s)) == None{} : Maybe<&2, Nat>}, +again: {Da.any_opens(c, evs) == False{} : Bool}) -> {Da.any_ran(c, Da.run(evs, s)) == False{} : Bool}:
  LA.pa.quiet(evs, s, c, LA.pa.stale_eq(Da.St.cur(s), Da.held(c, Da.St.conns(s)), None{}, closed, {==}), again)

def Laws.dash_closed_runs_nothing(s, c, evs, closed, again):
  pa.closed_runs_nothing(s, c, evs, closed, again)
