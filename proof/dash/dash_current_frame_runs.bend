# eukhe: the proof of LAW dash_current_frame_runs

import Base
import ../../bend/dash.bend as Da
import ../../laws/dash.bend as Dash
import ./base.bend as LA

def pa.current_frame_runs(+s: Da.St, +c: Nat, +cur: {Da.held(c, Da.St.conns(s)) == Some{Da.St.cur(s)} : Maybe<&2, Nat>}) -> {Da.out(s, Da.Frame{c}) == Da.Ran{c} : Da.Out}:
  %Equal.sym(Maybe<&2, Nat>, Da.held(c, Da.St.conns(s)), Some{Da.St.cur(s)}, cur) : {Da.frame.out(c, _, Da.St.cur(s)) == Da.Ran{c} : Da.Out}
  %LA.pa.eq_refl(Da.St.cur(s)) : {Da.frame.ran(c, _) == Da.Ran{c} : Da.Out}
  {==}

def Dash.dash_current_frame_runs(s, c, cur):
  pa.current_frame_runs(s, c, cur)
