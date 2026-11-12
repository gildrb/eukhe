# eukhe: the proof of LAW dash_rotation_rejects_old_tokens
#
# PROOF: the shipped stepper, opened as Rust opens it, answers the spelled
# events as the model does (dceh.go, from dash_conn_entry_history); Rust's
# comparison of the old token with the rotated file fails
# (LA.drt.unmatched), so the gate refuses the pairing with "not valid any
# more" (dash_gate_token_stored) and the socket closes
# (LA.drt.first_refuse); a closed socket answers `closed` to every later
# frame (LA.drt.closed).

import Base
import ../../bend/dash.bend as Da
import ../../bend/ffi_dash.bend as FDa
import ../../laws/base.bend as LawsBase
import ../../laws/dash.bend as Dash
import ../../laws/dash_conn.bend as DashConn
import ../dash/dash_gate_token_stored.bend as PDashGateTokenStored
import ./dash_conn_entry_history.bend as PDashConnEntryHistory
import ./base.bend as LA

# Rust's comparison of the old token with the rotated file fails
def drro.unmatched(+t: String, +a: List<&2, Nat>, +g: Da.Disk, +b: List<&2, Nat>, old: {Dash.sp_token(t) == Some{a} : Maybe<&2, List<&2, Nat>>}, rotated: {Dash.sp_stored(g) == Some{b} : Maybe<&2, List<&2, Nat>>}, other: {DashConn.cv_bytes_same(a, b) == False{} : Bool}) -> {DashConn.cv_rust_match(Dash.sp_token(t), g) == False{} : Bool}:
  %Equal.sym(Maybe<&2, List<&2, Nat>>, Dash.sp_token(t), Some{a}, old) : {DashConn.cv_rust_match(_, g) == False{} : Bool}
  LA.drt.unmatched(a, g, b, rotated, other)

# the pairing is refused with "not valid any more"
def drro.gate(+t: String, +a: List<&2, Nat>, +g: Da.Disk, +b: List<&2, Nat>, +old: {Dash.sp_token(t) == Some{a} : Maybe<&2, List<&2, Nat>>}, +rotated: {Dash.sp_stored(g) == Some{b} : Maybe<&2, List<&2, Nat>>}, other: {DashConn.cv_bytes_same(a, b) == False{} : Bool}) -> {Da.gate(Da.Pair{Da.Spoken{t}}, g, DashConn.cv_rust_match(Dash.sp_token(t), g)) == Da.Refuse{Dash.sp_wrong()} : Da.Pass}:
  %Equal.sym(Bool, DashConn.cv_rust_match(Dash.sp_token(t), g), False{}, drro.unmatched(t, a, g, b, old, rotated, other)) : {Da.gate(Da.Pair{Da.Spoken{t}}, g, _) == Da.Refuse{Dash.sp_wrong()} : Da.Pass}
  LA.drt.snd({Da.gate(Da.Pair{Da.Spoken{t}}, g, True{}) == Da.Admit{} : Da.Pass}, {Da.gate(Da.Pair{Da.Spoken{t}}, g, False{}) == Da.Refuse{Dash.sp_wrong()} : Da.Pass}, Dash.dash_gate_token_stored(t, g, LA.drt.holds(Dash.sp_token(t), a, old), LA.drt.holds(Dash.sp_stored(g), b, rotated)))

# every event of the socket's life fits the wire
def drro.fits(+t: String, +g: Da.Disk, +fs: List<&2, Da.Disk>, fit: {LawsBase.wire_fits(String.length(t)) == True{} : Bool}, fits: {DashConn.cv_fit_disks(g <> fs) == True{} : Bool}) -> {DashConn.sp_fit_evs(DashConn.cv_life(t, g, fs)) == True{} : Bool}:
  %Equal.sym(Bool, DashConn.sp_fit_evs(DashConn.cv_frames(Dash.sp_token(t), fs)), DashConn.cv_fit_disks(fs), LA.drt.fit_frames(Dash.sp_token(t), fs)) : {Bool.and(Bool.and(LawsBase.wire_fits(String.length(t)), Dash.sp_fit_disk(g)), _) == True{} : Bool}
  LA.drt.and3(LawsBase.wire_fits(String.length(t)), Dash.sp_fit_disk(g), DashConn.cv_fit_disks(fs), fit, fits)

def DashConn.dash_rotation_rejects_old_tokens(t, a, g, b, fs, old, rotated, other, fit, fits):
  %Equal.sym(List<&2, String>, DashConn.cs_feed(DashConn.cv_life(t, g, fs), (FDa.Live{Da.Waiting{}}, "")), "" <> DashConn.cs_replies(DashConn.cv_life(t, g, fs), Da.Waiting{}), PDashConnEntryHistory.dceh.go(DashConn.cv_life(t, g, fs), Da.Waiting{}, "", drro.fits(t, g, fs, fit, fits))) : {_ == "" <> DashConn.sp_w_verdict(Da.VRefuse{Dash.sp_wrong()}) <> DashConn.cw_closed(fs) : List<&2, String>}
  %Equal.sym(List<&2, String>, DashConn.sp_w_verdict(DashConn.cv_verdict(Da.cstep(Da.Waiting{}, Da.CFirst{Da.Pair{Da.Spoken{t}}, g, DashConn.cv_rust_match(Dash.sp_token(t), g)}))) <> DashConn.cs_replies(DashConn.cv_frames(Dash.sp_token(t), fs), DashConn.cv_conn(Da.cstep(Da.Waiting{}, Da.CFirst{Da.Pair{Da.Spoken{t}}, g, DashConn.cv_rust_match(Dash.sp_token(t), g)}))), DashConn.sp_w_verdict(Da.VRefuse{Dash.sp_wrong()}) <> DashConn.cs_replies(DashConn.cv_frames(Dash.sp_token(t), fs), Da.Closed{}), LA.drt.replies(Da.cstep(Da.Waiting{}, Da.CFirst{Da.Pair{Da.Spoken{t}}, g, DashConn.cv_rust_match(Dash.sp_token(t), g)}), Dash.sp_wrong(), DashConn.cv_frames(Dash.sp_token(t), fs), LA.drt.first_refuse(Da.gate(Da.Pair{Da.Spoken{t}}, g, DashConn.cv_rust_match(Dash.sp_token(t), g)), Dash.sp_wrong(), drro.gate(t, a, g, b, old, rotated, other)))) : {"" <> _ == "" <> DashConn.sp_w_verdict(Da.VRefuse{Dash.sp_wrong()}) <> DashConn.cw_closed(fs) : List<&2, String>}
  %Equal.sym(List<&2, String>, DashConn.cs_replies(DashConn.cv_frames(Dash.sp_token(t), fs), Da.Closed{}), DashConn.cw_closed(fs), LA.drt.closed(Dash.sp_token(t), fs)) : {"" <> (DashConn.sp_w_verdict(Da.VRefuse{Dash.sp_wrong()}) <> _) == "" <> DashConn.sp_w_verdict(Da.VRefuse{Dash.sp_wrong()}) <> DashConn.cw_closed(fs) : List<&2, String>}
  {==}
