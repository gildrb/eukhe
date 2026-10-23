# eukhe: the proof of LAW dash_paired_holds_token

import Base
import ../../bend/dash.bend as Da
import ../../LAWS.bend as Laws
import ./base.bend as LA

def pa.paired_holds_token(+s: Da.St, +c: Nat) -> {Da.held(c, Da.St.conns(Da.next(s, Da.Open{c, Some{Da.St.cur(s)}}))) == Some{Da.St.cur(s)} : Maybe<&2, Nat>}:
  match s:
    case Da.St{+cur, +cs}:
      %LA.pa.eq_refl(cur) : {Da.held(c, Da.open.keep(c, cur, _, Da.drop(c, cs))) == Some{cur} : Maybe<&2, Nat>}
      %LA.pa.eq_refl(c) : {Da.held.put(cur, Da.held(c, Da.drop(c, cs)), _) == Some{cur} : Maybe<&2, Nat>}
      {==}

def Laws.dash_paired_holds_token(s, c):
  pa.paired_holds_token(s, c)
