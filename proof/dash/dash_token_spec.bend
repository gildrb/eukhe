# eukhe: the proof of LAW dash_token_spec
#
# PROOF: the code's token is the spec's (hx.token: digit by digit, then
# the count); the rest of the choice has the same form on both sides.

import Base
import ../../bend/dash.bend as Da
import ../../laws/dash.bend as Dash
import ./dash_token_spec/hex.bend as LHex

def tk.of(m: Maybe<&2, List<&2, Nat>>, e: Bool) -> {Da.shown.of(m, e) == Dash.sp_shown.of(m, e) : Da.Shown}:
  match m:
    case Some{bs}:
      {==}
    case None{}:
      match e:
        case True{}:
          {==}
        case False{}:
          {==}

def tk.shown(x: Da.Said) -> {Da.shown(x) == Dash.sp_shown(x) : Da.Shown}:
  match x:
    case Da.Spoken{+s}:
      %Equal.sym(Maybe<&2, List<&2, Nat>>, Da.parse(s), Dash.sp_token(s), LHex.hx.token(s)) : {Da.shown.of(_, String.is_empty(s)) == Dash.sp_shown.of(Dash.sp_token(s), String.is_empty(s)) : Da.Shown}
      tk.of(Dash.sp_token(s), String.is_empty(s))
    case Da.Overlong{}:
      {==}

def Dash.dash_token_spec(x):
  tk.shown(x)
