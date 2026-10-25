# eukhe: the proof of LAW dash_conn_step_spec
#
# PROOF: by cases on the socket and the event. A first frame's pass is the
# spec's gate (dash_gate_spec), a later frame's the spec's frame
# (dash_frame_spec); each pass moves the socket and answers alike on both
# sides (dcs.first, dcs.later); the other cases compute.

import Base
import ../../bend/dash.bend as Da
import ../../laws/dash.bend as Dash
import ../../laws/dash_conn.bend as DashConn
import ../dash/dash_gate_spec.bend as PDashGateSpec
import ../dash/dash_frame_spec.bend as PDashFrameSpec

def dcs.first(p: Da.Pass) -> {Da.first.pass(p) == DashConn.sp_pass.first(p) : Da.Conn & Da.Verdict}:
  match p:
    case Da.Admit{}:
      {==}
    case Da.Refuse{t}:
      {==}

def dcs.later(p: Da.Pass) -> {Da.frame.pass(p) == DashConn.sp_pass.later(p) : Da.Conn & Da.Verdict}:
  match p:
    case Da.Admit{}:
      {==}
    case Da.Refuse{t}:
      {==}

def dcs.step(c: Da.Conn, e: Da.CEv) -> {Da.cstep(c, e) == DashConn.sp_cstep(c, e) : Da.Conn & Da.Verdict}:
  match c:
    case Da.Waiting{}:
      match e:
        case Da.CFirst{+x, +f, +m}:
          %Equal.sym(Da.Pass, Da.gate(x, f, m), Dash.sp_gate(x, f, m), Dash.dash_gate_spec(x, f, m)) : {Da.first.pass(_) == DashConn.sp_pass.first(Dash.sp_gate(x, f, m)) : Da.Conn & Da.Verdict}
          dcs.first(Dash.sp_gate(x, f, m))
        case Da.CFrame{f, m}:
          {==}
    case Da.Paired{}:
      match e:
        case Da.CFirst{x, f, m}:
          {==}
        case Da.CFrame{+f, +m}:
          %Equal.sym(Da.Pass, Da.frame(f, m), Dash.sp_frame(f, m), Dash.dash_frame_spec(f, m)) : {Da.frame.pass(_) == DashConn.sp_pass.later(Dash.sp_frame(f, m)) : Da.Conn & Da.Verdict}
          dcs.later(Dash.sp_frame(f, m))
    case Da.Closed{}:
      {==}

def DashConn.dash_conn_step_spec(c, e):
  dcs.step(c, e)
