# eukhe: the proof of LAW dash_rotation_ends_connections
#
# PROOF: the shipped stepper answers the spelled frames as the model does
# (dceh.go, from dash_conn_entry_history); Rust's comparison of the
# socket's token with the rotated file fails (LA.drt.unmatched), so the
# frame check refuses with "not valid any more" (dash_frame_stored) and
# the socket closes (LA.drt.frame_refuse); a closed socket answers
# `closed` to every later frame (LA.drt.closed).

import Base
import ../../bend/dash.bend as Da
import ../../bend/ffi_dash.bend as FDa
import ../../laws/dash.bend as Dash
import ../../laws/dash_conn.bend as DashConn
import ../dash/dash_frame_stored.bend as PDashFrameStored
import ./dash_conn_entry_history.bend as PDashConnEntryHistory
import ./base.bend as LA

# the frame after the rotation is refused with "not valid any more"
def drte.frame(+a: List<&2, Nat>, +g: Da.Disk, +b: List<&2, Nat>, +rotated: {Dash.sp_stored(g) == Some{b} : Maybe<&2, List<&2, Nat>>}, other: {DashConn.cv_bytes_same(a, b) == False{} : Bool}) -> {Da.frame(g, DashConn.cv_rust_match(Some{a}, g)) == Da.Refuse{Dash.sp_wrong()} : Da.Pass}:
  %Equal.sym(Bool, DashConn.cv_rust_match(Some{a}, g), False{}, LA.drt.unmatched(a, g, b, rotated, other)) : {Da.frame(g, _) == Da.Refuse{Dash.sp_wrong()} : Da.Pass}
  LA.drt.snd({Da.frame(g, True{}) == Da.Admit{} : Da.Pass}, {Da.frame(g, False{}) == Da.Refuse{Dash.sp_wrong()} : Da.Pass}, Dash.dash_frame_stored(g, LA.drt.holds(Dash.sp_stored(g), b, rotated)))

def drte.fits(+a: List<&2, Nat>, +g: Da.Disk, +fs: List<&2, Da.Disk>, fits: {DashConn.cv_fit_disks(g <> fs) == True{} : Bool}) -> {DashConn.sp_fit_evs(DashConn.cv_frames(Some{a}, g <> fs)) == True{} : Bool}:
  Equal.trans(Bool, DashConn.sp_fit_evs(DashConn.cv_frames(Some{a}, g <> fs)), DashConn.cv_fit_disks(g <> fs), True{}, LA.drt.fit_frames(Some{a}, g <> fs), fits)

def DashConn.dash_rotation_ends_connections(a, g, b, fs, rotated, other, fits):
  %Equal.sym(List<&2, String>, DashConn.cs_feed(DashConn.cv_frames(Some{a}, g <> fs), (FDa.Live{Da.Paired{}}, "")), "" <> DashConn.cs_replies(DashConn.cv_frames(Some{a}, g <> fs), Da.Paired{}), PDashConnEntryHistory.dceh.go(DashConn.cv_frames(Some{a}, g <> fs), Da.Paired{}, "", drte.fits(a, g, fs, fits))) : {_ == "" <> DashConn.sp_w_verdict(Da.VRefuse{Dash.sp_wrong()}) <> DashConn.cw_closed(fs) : List<&2, String>}
  %Equal.sym(List<&2, String>, DashConn.sp_w_verdict(DashConn.cv_verdict(Da.cstep(Da.Paired{}, Da.CFrame{g, DashConn.cv_rust_match(Some{a}, g)}))) <> DashConn.cs_replies(DashConn.cv_frames(Some{a}, fs), DashConn.cv_conn(Da.cstep(Da.Paired{}, Da.CFrame{g, DashConn.cv_rust_match(Some{a}, g)}))), DashConn.sp_w_verdict(Da.VRefuse{Dash.sp_wrong()}) <> DashConn.cs_replies(DashConn.cv_frames(Some{a}, fs), Da.Closed{}), LA.drt.replies(Da.cstep(Da.Paired{}, Da.CFrame{g, DashConn.cv_rust_match(Some{a}, g)}), Dash.sp_wrong(), DashConn.cv_frames(Some{a}, fs), LA.drt.frame_refuse(Da.frame(g, DashConn.cv_rust_match(Some{a}, g)), Dash.sp_wrong(), drte.frame(a, g, b, rotated, other)))) : {"" <> _ == "" <> DashConn.sp_w_verdict(Da.VRefuse{Dash.sp_wrong()}) <> DashConn.cw_closed(fs) : List<&2, String>}
  %Equal.sym(List<&2, String>, DashConn.cs_replies(DashConn.cv_frames(Some{a}, fs), Da.Closed{}), DashConn.cw_closed(fs), LA.drt.closed(Some{a}, fs)) : {"" <> (DashConn.sp_w_verdict(Da.VRefuse{Dash.sp_wrong()}) <> _) == "" <> DashConn.sp_w_verdict(Da.VRefuse{Dash.sp_wrong()}) <> DashConn.cw_closed(fs) : List<&2, String>}
  {==}
