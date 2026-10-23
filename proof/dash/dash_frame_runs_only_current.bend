# eukhe: the proof of LAW dash_frame_runs_only_current

import Base
import ../../bend/dash.bend as Da
import ../../LAWS.bend as Laws
import ./base.bend as LA

# The gate
# --------

def pa.ran_ok(+c: Nat, b: Bool, +h: {Da.ran(c, Da.frame.ran(c, b)) == True{} : Bool}) -> {b == True{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      LA.dashboard_auth.pa.absurdF({False{} == True{} : Bool}, h)

# a frame that runs has the current token
def pa.frame_ran_cur(+c: Nat, m: Maybe<&2, Nat>, +cur: Nat, +h: {Da.ran(c, Da.frame.out(c, m, cur)) == True{} : Bool}) -> {m == Some{cur} : Maybe<&2, Nat>}:
  match m:
    case None{}:
      LA.dashboard_auth.pa.absurdF({None{} == Some{cur} : Maybe<&2, Nat>}, h)
    case Some{+t}:
      Equal.cong(Nat, Maybe<&2, Nat>, x => Some{x}, t, cur, LA.pa.eq_true(t, cur, pa.ran_ok(c, Nat.is_eq(t, cur), h)))

# The laws
# --------

def pa.frame_runs_only_current(+s: Da.St, +c: Nat, +ran: {Da.ran(c, Da.out(s, Da.Frame{c})) == True{} : Bool}) -> {Da.held(c, Da.St.conns(s)) == Some{Da.St.cur(s)} : Maybe<&2, Nat>}:
  pa.frame_ran_cur(c, Da.held(c, Da.St.conns(s)), Da.St.cur(s), ran)

# (D1) The dashboard's pairing gate

def Laws.dash_frame_runs_only_current(s, c, ran):
  pa.frame_runs_only_current(s, c, ran)
