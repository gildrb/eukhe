# eukhe: the proof of LAW dash_open_pairs_only_current

import Base
import ../../bend/dash.bend as Da
import ../../laws/dash.bend as Dash
import ./base.bend as LA

def pa.paired_ok(c: Nat, b: Bool, +h: {Da.is_paired(Da.open.out(c, b)) == True{} : Bool}) -> {b == True{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      LA.dashboard_auth.pa.absurdF({False{} == True{} : Bool}, h)

# an admitted token is the current one
def pa.admit_cur(+cur: Nat, shown: Maybe<&2, Nat>, +h: {Da.admit(cur, shown) == True{} : Bool}) -> {shown == Some{cur} : Maybe<&2, Nat>}:
  match shown:
    case None{}:
      LA.dashboard_auth.pa.absurdF({None{} == Some{cur} : Maybe<&2, Nat>}, h)
    case Some{+t}:
      Equal.cong(Nat, Maybe<&2, Nat>, x => Some{x}, t, cur, LA.pa.eq_true(t, cur, h))

def pa.open_pairs_only_current(+s: Da.St, +c: Nat, +shown: Maybe<&2, Nat>, +paired: {Da.is_paired(Da.out(s, Da.Open{c, shown})) == True{} : Bool}) -> {shown == Some{Da.St.cur(s)} : Maybe<&2, Nat>}:
  pa.admit_cur(Da.St.cur(s), shown, pa.paired_ok(c, Da.admit(Da.St.cur(s), shown), paired))

def Dash.dash_open_pairs_only_current(s, c, shown, paired):
  pa.open_pairs_only_current(s, c, shown, paired)
