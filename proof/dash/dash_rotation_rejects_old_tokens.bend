# eukhe: the proof of LAW dash_rotation_rejects_old_tokens

import Base
import ../../bend/dash.bend as Da
import ../../laws/dash.bend as Dash
import ./base.bend as LA

# The current token only grows
# ----------------------------

def pa.lt_next(+s: Da.St, +e: Da.Ev, +t: Nat, +h: {Nat.is_lt(t, Da.St.cur(s)) == True{} : Bool}) -> {Nat.is_lt(t, Da.St.cur(Da.next(s, e))) == True{} : Bool}:
  match s:
    case Da.St{+cur, +cs}:
      match e:
        case Da.Rotate{}:
          LA.pa.lt_succ(t, cur, h)
        case Da.Open{x, shown}:
          h
        case Da.Frame{x}:
          h

def pa.lt_state(evs: List<&2, Da.Ev>, +s: Da.St, +t: Nat, +h: {Nat.is_lt(t, Da.St.cur(s)) == True{} : Bool}) -> {Nat.is_lt(t, Da.St.cur(Da.state(evs, s))) == True{} : Bool}:
  match evs:
    case Nil{}:
      h
    case +e <> +rest:
      pa.lt_state(rest, Da.next(s, e), t, pa.lt_next(s, e, t, h))

def pa.lt_rotate(+s: Da.St, +t: Nat, +h: {Nat.is_le(t, Da.St.cur(s)) == True{} : Bool}) -> {Nat.is_lt(t, Da.St.cur(Da.next(s, Da.Rotate{}))) == True{} : Bool}:
  match s:
    case Da.St{+cur, +cs}:
      LA.pa.le_lt_succ(t, cur, h)

def pa.rotation_rejects_old_tokens(+hist: List<&2, Da.Ev>, +more: List<&2, Da.Ev>, +c: Nat, +t: Nat, +old: {Nat.is_le(t, Da.St.cur(Da.state(hist, Da.init()))) == True{} : Bool}) -> {Da.out(Da.state(Da.Rotate{} <> more, Da.state(hist, Da.init())), Da.Open{c, Some{t}}) == Da.Rejected{c} : Da.Out}:
  %Equal.sym(Bool, Nat.is_eq(t, Da.St.cur(Da.state(more, Da.next(Da.state(hist, Da.init()), Da.Rotate{})))), False{}, LA.pa.lt_ne(t, Da.St.cur(Da.state(more, Da.next(Da.state(hist, Da.init()), Da.Rotate{}))), pa.lt_state(more, Da.next(Da.state(hist, Da.init()), Da.Rotate{}), t, pa.lt_rotate(Da.state(hist, Da.init()), t, old)))) : {Da.open.out(c, _) == Da.Rejected{c} : Da.Out}
  {==}

def Dash.dash_rotation_rejects_old_tokens(hist, more, c, t, old):
  pa.rotation_rejects_old_tokens(hist, more, c, t, old)
