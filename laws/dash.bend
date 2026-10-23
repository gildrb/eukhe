# eukhe: the laws of area dash

import Base
import ../bend/dash.bend as Da

# ---- dashboard_auth ----

# LAWS (D1): the dashboard's pairing gate. Each law is an open claim about
# the model in bend/dash.bend; PROOF.bend proves them (as Dash.<law>)
# with the lemmas of proof/dash/.

# (D1) Pairing
# ------------
# docs/dashboard.md "Pairing", the model in bend/dash.bend; the Rust gate
# (crates/eukhe-dashboard/src/pairing.rs, http.rs, bridge.rs) and the
# model run the same events in the bridge test
# pairing::tests::the_gate_pairs_as_its_model. Every input is free: any
# state, any connection, any token, any events before and after.

# LAW: a frame runs (a daemon command) only when its connection holds the
# current token
law dash_frame_runs_only_current:
  for +s: Da.St
  for +c: Nat
  for ran: {Da.ran(c, Da.out(s, Da.Frame{c})) == True{} : Bool}
  {Da.held(c, Da.St.conns(s)) == Some{Da.St.cur(s)} : Maybe<&2, Nat>}

# LAW: a frame of a connection that holds the current token runs
law dash_current_frame_runs:
  for +s: Da.St
  for +c: Nat
  for cur: {Da.held(c, Da.St.conns(s)) == Some{Da.St.cur(s)} : Maybe<&2, Nat>}
  {Da.out(s, Da.Frame{c}) == Da.Ran{c} : Da.Out}

# LAW: a connection pairs only when it presents the current token
law dash_open_pairs_only_current:
  for +s: Da.St
  for +c: Nat
  for +shown: Maybe<&2, Nat>
  for paired: {Da.is_paired(Da.out(s, Da.Open{c, shown})) == True{} : Bool}
  {shown == Some{Da.St.cur(s)} : Maybe<&2, Nat>}

# LAW: a connection that presents the current token pairs
law dash_current_open_pairs:
  for +s: Da.St
  for +c: Nat
  {Da.out(s, Da.Open{c, Some{Da.St.cur(s)}}) == Da.Paired{c} : Da.Out}

# LAW: a paired connection holds the token it presented
law dash_paired_holds_token:
  for +s: Da.St
  for +c: Nat
  {Da.held(c, Da.St.conns(Da.next(s, Da.Open{c, Some{Da.St.cur(s)}}))) == Some{Da.St.cur(s)} : Maybe<&2, Nat>}

# LAW: a connection that is not open runs no frame, whatever comes, until
# it opens again
law dash_closed_runs_nothing:
  for +s: Da.St
  for +c: Nat
  for +evs: List<&2, Da.Ev>
  for closed: {Da.held(c, Da.St.conns(s)) == None{} : Maybe<&2, Nat>}
  for again: {Da.any_opens(c, evs) == False{} : Bool}
  {Da.any_ran(c, Da.run(evs, s)) == False{} : Bool}

# LAW: a rejected connection runs no frame, whatever comes, until it
# opens again
law dash_rejected_runs_nothing:
  for +s: Da.St
  for +c: Nat
  for +shown: Maybe<&2, Nat>
  for +evs: List<&2, Da.Ev>
  for rejected: {Da.is_paired(Da.out(s, Da.Open{c, shown})) == False{} : Bool}
  for again: {Da.any_opens(c, evs) == False{} : Bool}
  {Da.any_ran(c, Da.run(Da.Open{c, shown} <> evs, s)) == False{} : Bool}

# LAW: after any history, a rotation ends every connection: none runs a
# frame, whatever comes, until it opens again
law dash_rotation_ends_connections:
  for +hist: List<&2, Da.Ev>
  for +c: Nat
  for +evs: List<&2, Da.Ev>
  for again: {Da.any_opens(c, evs) == False{} : Bool}
  {Da.any_ran(c, Da.run(Da.Rotate{} <> evs, Da.state(hist, Da.init()))) == False{} : Bool}

# LAW: after any history, a rotation invalidates every token made before
# it: an open that presents one is rejected, whatever comes after
law dash_rotation_rejects_old_tokens:
  for +hist: List<&2, Da.Ev>
  for +more: List<&2, Da.Ev>
  for +c: Nat
  for +t: Nat
  for old: {Nat.is_le(t, Da.St.cur(Da.state(hist, Da.init()))) == True{} : Bool}
  {Da.out(Da.state(Da.Rotate{} <> more, Da.state(hist, Da.init())), Da.Open{c, Some{t}}) == Da.Rejected{c} : Da.Out}
