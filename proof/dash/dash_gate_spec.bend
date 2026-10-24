# eukhe: the proof of LAW dash_gate_spec
#
# PROOF: what a pairing presents is the spec's (dash_token_spec); a token
# is then checked as a later frame is (dash_frame_spec); the refusals
# have the same texts on both sides.

import Base
import ../../bend/dash.bend as Da
import ../../laws/dash.bend as Dash
import ./dash_token_spec.bend as PDashTokenSpec
import ./dash_frame_spec.bend as PDashFrameSpec

def gt.shown(x: Da.Shown, +f: Da.Disk, +b: Bool) -> {Da.gate.shown(x, f, b) == Dash.sp_gate.shown(x, f, b) : Da.Pass}:
  match x:
    case Da.Hex{bs}:
      Dash.dash_frame_spec(f, b)
    case Da.Blank{}:
      {==}
    case Da.Junk{}:
      {==}

def gt.gate(x: Da.First, +f: Da.Disk, +b: Bool) -> {Da.gate(x, f, b) == Dash.sp_gate(x, f, b) : Da.Pass}:
  match x:
    case Da.NoText{}:
      {==}
    case Da.NotPairing{}:
      {==}
    case Da.Pair{+t}:
      %Equal.sym(Da.Shown, Da.shown(t), Dash.sp_shown(t), Dash.dash_token_spec(t)) : {Da.gate.shown(_, f, b) == Dash.sp_gate.shown(Dash.sp_shown(t), f, b) : Da.Pass}
      gt.shown(Dash.sp_shown(t), f, b)

def Dash.dash_gate_spec(x, f, b):
  gt.gate(x, f, b)
