# eukhe: the laws of area dash, section socket: the stepper each dashboard
# socket runs (bend/dash.bend section 2), as the compiled core runs it
# (bend/ffi_dash.bend open, step)

import Base
import ../bend/dash.bend as Da
import ../bend/ffi_dash.bend as FDa
import ../bend/wire.bend as Wr
import ./dash.bend as Dash
import ./base.bend as LawsBase

# LAWS (D1): crates/eukhe-dashboard (http.rs, bridge.rs, pairing.rs) opens
# one stepper per socket and is an event loop with no policy: it sends each
# frame as it arrives, with the token file read at that moment and whether
# its constant-time comparison found the socket's token (the one the frame
# presents, or the one the socket paired with) equal to the file's
# (`matches`), and does what the stepper answers. The stepper decides.
# Every input is free: any socket state, any first frame, any token file,
# any comparison result, any order of events.
#
# C1: a socket waits for its pairing. Its first frame opens it exactly
#     when the frame is a pairing whose text is a token, the file holds a
#     token, and Rust reported a match (laws/dash.bend R3); else it is
#     refused with the text of R3 and closes. A later frame before any
#     pairing is refused (pairing needed) and closes.
# C2: a frame of a paired socket runs exactly when the file, read at that
#     frame, holds a token and Rust reported a match against it; else it is
#     refused with the text of R4 and the socket closes (a rotation by any
#     process ends every socket at its next frame). A second pairing frame
#     is refused (pairing needed) and closes.
# C3: a closed socket runs nothing, whatever comes.
# C4: the entry: an open with no input is a waiting socket; an open with
#     input is refused, and so is every step after it; a live socket
#     answers every input that is exactly one event as Rust writes it
#     (`sp_w_ev`: the tag, then the fields in Rust's order) with the
#     step's verdict, spelled; any other input answers exactly
#     `E dash: malformed event` and keeps the socket.
# C5: a token rotation (the file now holds another token than the one a
#     socket paired with) ends every socket at its next frame, and every
#     frame after it runs nothing, whatever the file holds later; a new
#     socket whose pairing presents an old token (any token but the one the
#     file holds) is refused and runs nothing. Rust's comparison is
#     pairing.rs `equal`: both tokens exist and are the same bytes.

# Spec helpers
# ------------

def cv_conn(r: Da.Conn & Da.Verdict) -> Da.Conn:
  (c, v) = r
  c

def cv_verdict(r: Da.Conn & Da.Verdict) -> Da.Verdict:
  (c, v) = r
  v

def cv_is_run(v: Da.Verdict) -> Bool:
  match v:
    case Da.VPaired{}:
      False{}
    case Da.VRun{}:
      True{}
    case Da.VRefuse{t}:
      False{}
    case Da.VClosed{}:
      False{}

def cv_is_paired(v: Da.Verdict) -> Bool:
  match v:
    case Da.VPaired{}:
      True{}
    case Da.VRun{}:
      False{}
    case Da.VRefuse{t}:
      False{}
    case Da.VClosed{}:
      False{}

def cv_is_refuse(v: Da.Verdict) -> Bool:
  match v:
    case Da.VPaired{}:
      False{}
    case Da.VRun{}:
      False{}
    case Da.VRefuse{t}:
      True{}
    case Da.VClosed{}:
      False{}

def cv_is_closed(c: Da.Conn) -> Bool:
  match c:
    case Da.Waiting{}:
      False{}
    case Da.Paired{}:
      False{}
    case Da.Closed{}:
      True{}

# whether Rust reported a match with the event
def cv_matches(e: Da.CEv) -> Bool:
  match e:
    case Da.CFirst{x, f, m}:
      m
    case Da.CFrame{f, m}:
      m

# the file holds a token
def cv_holds(f: Da.Disk) -> Bool:
  Maybe.is_some(&2, List<&2, Nat>, Dash.sp_stored(f))

# C2: a frame of a paired socket, with Rust's match against a file that
# holds a token
def cv_frame_ok(c: Da.Conn, e: Da.CEv) -> Bool:
  match c:
    case Da.Waiting{}:
      False{}
    case Da.Paired{}:
      match e:
        case Da.CFirst{x, f, m}:
          False{}
        case Da.CFrame{f, m}:
          Bool.and(m, cv_holds(f))
    case Da.Closed{}:
      False{}

def cv_presents.shown(s: Da.Shown) -> Bool:
  match s:
    case Da.Hex{bs}:
      True{}
    case Da.Blank{}:
      False{}
    case Da.Junk{}:
      False{}

# a first frame that is a pairing whose text is a token
def cv_presents(x: Da.First) -> Bool:
  match x:
    case Da.NoText{}:
      False{}
    case Da.NotPairing{}:
      False{}
    case Da.Pair{t}:
      cv_presents.shown(Dash.sp_shown(t))

# C1: the first frame of a waiting socket presents a token, the file holds
# one, and Rust reported a match
def cv_pair_ok(c: Da.Conn, e: Da.CEv) -> Bool:
  match c:
    case Da.Waiting{}:
      match e:
        case Da.CFirst{x, f, m}:
          Bool.and(m, Bool.and(cv_presents(x), cv_holds(f)))
        case Da.CFrame{f, m}:
          False{}
    case Da.Paired{}:
      False{}
    case Da.Closed{}:
      False{}

# Runs of events
# --------------

# the verdicts of a socket fed the events es from c, in order
def cv_run(es: List<&2, Da.CEv>, +c: Da.Conn) -> List<&2, Da.Verdict>:
  match es:
    case Nil{}:
      Nil{}
    case +e <> t:
      cv_verdict(Da.cstep(c, e)) <> cv_run(t, cv_conn(Da.cstep(c, e)))

# where the verdicts of a socket stand
type Ph is Data:
  PhWait{}
  PhPaired{}
  PhClosed{}

# whether a verdict may come where the verdicts stand: from waiting,
# only `paired` or a refusal; from paired, only `run` or a refusal; once
# closed, only `closed`
def cv_good(ph: Ph, +v: Da.Verdict) -> Bool:
  match ph:
    case PhWait{}:
      Bool.or(cv_is_paired(v), cv_is_refuse(v))
    case PhPaired{}:
      Bool.or(cv_is_run(v), cv_is_refuse(v))
    case PhClosed{}:
      match v:
        case Da.VPaired{}:
          False{}
        case Da.VRun{}:
          False{}
        case Da.VRefuse{x}:
          False{}
        case Da.VClosed{}:
          True{}

# where the verdicts stand after v
def cv_next(ph: Ph, v: Da.Verdict) -> Ph:
  match v:
    case Da.VPaired{}:
      PhPaired{}
    case Da.VRun{}:
      ph
    case Da.VRefuse{x}:
      PhClosed{}
    case Da.VClosed{}:
      PhClosed{}

# C1-C3 over a run: nothing runs before a pairing, nothing pairs twice,
# and after a refusal nothing but `closed` comes
def cv_ok(vs: List<&2, Da.Verdict>, +ph: Ph) -> Bool:
  match vs:
    case Nil{}:
      True{}
    case +v <> t:
      Bool.and(cv_good(ph, v), cv_ok(t, cv_next(ph, v)))

# whether any verdict runs a frame or opens the socket
def cv_any_live(vs: List<&2, Da.Verdict>) -> Bool:
  match vs:
    case Nil{}:
      False{}
    case +v <> t:
      Bool.or(Bool.or(cv_is_run(v), cv_is_paired(v)), cv_any_live(t))

# C5: two tokens are the same bytes, in order
def cv_bytes_same(a: List<&2, Nat>, b: List<&2, Nat>) -> Bool:
  match a:
    case Nil{}:
      match b:
        case Nil{}:
          True{}
        case y <> ys:
          False{}
    case x <> xs:
      match b:
        case Nil{}:
          False{}
        case y <> ys:
          Bool.and(Nat.is_eq(x, y), cv_bytes_same(xs, ys))

def cv_rust_match.held(a: List<&2, Nat>, m: Maybe<&2, List<&2, Nat>>) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{b}:
      cv_bytes_same(a, b)

# C5: what Rust's comparison (pairing.rs `equal`) reports for the socket's
# token p (None: its pairing presented none) against the file f: both
# tokens exist (the file's by R2) and are the same bytes
def cv_rust_match(p: Maybe<&2, List<&2, Nat>>, f: Da.Disk) -> Bool:
  match p:
    case None{}:
      False{}
    case Some{a}:
      cv_rust_match.held(a, Dash.sp_stored(f))

# C5: the later frames of a socket whose token is p, one per file read, as
# Rust sends them
def cv_frames(+p: Maybe<&2, List<&2, Nat>>, fs: List<&2, Da.Disk>) -> List<&2, Da.CEv>:
  match fs:
    case Nil{}:
      Nil{}
    case +f <> t:
      Da.CFrame{f, cv_rust_match(p, f)} <> cv_frames(p, t)

# C5: a socket as Rust drives it: its pairing presents the text t, with
# the file g, then later frames with the files fs; its token is the one t
# spells (R1), if any
def cv_life(+t: String, +g: Da.Disk, fs: List<&2, Da.Disk>) -> List<&2, Da.CEv>:
  Da.CFirst{Da.Pair{Da.Spoken{t}}, g, cv_rust_match(Dash.sp_token(t), g)} <> cv_frames(Dash.sp_token(t), fs)

# every file text fits the wire
def cv_fit_disks(fs: List<&2, Da.Disk>) -> Bool:
  match fs:
    case Nil{}:
      True{}
    case f <> t:
      Bool.and(Dash.sp_fit_disk(f), cv_fit_disks(t))

# The entry: spellers and the reader
# ----------------------------------

def sp_malformed() -> String:
  SCon{'E', SCon{' ', "dash: malformed event"}}

# an event as Rust writes it, then rest
def sp_w_ev(e: Da.CEv, rest: String) -> String:
  match e:
    case Da.CFirst{x, f, m}:
      Wr.put_nat(0n, Dash.sp_w_first(x, Dash.sp_w_disk(f, Wr.put_bool(m, rest))))
    case Da.CFrame{f, m}:
      Wr.put_nat(1n, Dash.sp_w_disk(f, Wr.put_bool(m, rest)))

# every length of the event fits the wire
def sp_fit_ev(e: Da.CEv) -> Bool:
  match e:
    case Da.CFirst{x, f, m}:
      Bool.and(Dash.sp_fit_first(x), Dash.sp_fit_disk(f))
    case Da.CFrame{f, m}:
      Dash.sp_fit_disk(f)

def sp_fit_evs(es: List<&2, Da.CEv>) -> Bool:
  match es:
    case Nil{}:
      True{}
    case e <> t:
      Bool.and(sp_fit_ev(e), sp_fit_evs(t))

# the verdict as Rust reads it
def sp_w_verdict(v: Da.Verdict) -> String:
  match v:
    case Da.VPaired{}:
      Wr.put_nat(0n, "")
    case Da.VRun{}:
      Wr.put_nat(1n, "")
    case Da.VRefuse{t}:
      Wr.put_nat(2n, Wr.put_str(t, ""))
    case Da.VClosed{}:
      Wr.put_nat(3n, "")

def cs_reply(r: Da.Conn & Da.Verdict) -> FDa.St & String:
  (c, v) = r
  (FDa.Live{c}, sp_w_verdict(v))

# the reply of a step
def cs_out(r: FDa.St & String) -> String:
  (st, out) = r
  out

# the reply of a refused open
def sp_open_refused() -> String:
  SCon{'E', SCon{' ', "dash: the open takes no input"}}

# one reply of a refused socket per input
def sp_shut(ins: List<&2, String>) -> List<&2, String>:
  match ins:
    case Nil{}:
      Nil{}
    case i <> t:
      SCon{'E', SCon{' ', "dash: the open was refused"}} <> sp_shut(t)

# the replies of the shipped stepper to the spelled events es, from r
def cs_feed(es: List<&2, Da.CEv>, r: FDa.St & String) -> List<&2, String>:
  match es:
    case Nil{}:
      (st, out) = r
      [out]
    case e <> t:
      (st, out) = r
      out <> cs_feed(t, FDa.step(st, sp_w_ev(e, "")))

# the replies of the shipped stepper to raw inputs, from r
def cs_raw(ins: List<&2, String>, r: FDa.St & String) -> List<&2, String>:
  match ins:
    case Nil{}:
      (st, out) = r
      [out]
    case i <> t:
      (st, out) = r
      out <> cs_raw(t, FDa.step(st, i))

# the model's replies to es from c, spelled
def cs_replies(es: List<&2, Da.CEv>, +c: Da.Conn) -> List<&2, String>:
  match es:
    case Nil{}:
      Nil{}
    case +e <> t:
      sp_w_verdict(cv_verdict(Da.cstep(c, e))) <> cs_replies(t, cv_conn(Da.cstep(c, e)))

# the socket after a step
def cs_st(r: FDa.St & String) -> FDa.St:
  (st, out) = r
  st

# the replies of the shipped stepper to the raw inputs ins, from st
def cs_outs(ins: List<&2, String>, +st: FDa.St) -> List<&2, String>:
  match ins:
    case Nil{}:
      Nil{}
    case +i <> t:
      cs_out(FDa.step(st, i)) <> cs_outs(t, cs_st(FDa.step(st, i)))

# C3: a reply that neither opens a socket nor runs a frame: `closed` as
# Rust reads it (tag 3), or the malformed error (an input that is no event)
def cw_quiet1(+o: String) -> Bool:
  Bool.or(LawsBase.text_same(o, sp_w_verdict(Da.VClosed{})), LawsBase.text_same(o, sp_malformed()))

def cw_quiet(os: List<&2, String>) -> Bool:
  match os:
    case Nil{}:
      True{}
    case o <> t:
      Bool.and(cw_quiet1(o), cw_quiet(t))

# C5: `closed` as Rust reads it, once per file read
def cw_closed(fs: List<&2, Da.Disk>) -> List<&2, String>:
  match fs:
    case Nil{}:
      Nil{}
    case f <> t:
      sp_w_verdict(Da.VClosed{}) <> cw_closed(t)

# Laws: the socket
# ----------------

# LAW dash_conn_first_refused (C1): a waiting socket whose first frame the
# gate refuses (laws/dash.bend R3: dash_gate_*) closes and tells the tab
# the gate's text
# EXCLUDES: a refused pairing that leaves the socket waiting or open; a
#   refusal told with another text than R3's
law dash_conn_first_refused:
  for +x: Da.First
  for +f: Da.Disk
  for +m: Bool
  for +t: String
  for refused: {Da.gate(x, f, m) == Da.Refuse{t} : Da.Pass}
  {Da.cstep(Da.Waiting{}, Da.CFirst{x, f, m}) == (Da.Closed{}, Da.VRefuse{t}) : Da.Conn & Da.Verdict}

# LAW dash_conn_later_refused (C2): a frame of a paired socket that the
# frame check refuses (laws/dash.bend R4: dash_frame_*) closes the socket
# and tells the tab that text
# EXCLUDES: a refused frame that leaves the socket paired (and runs the
#   next one); a refusal told with another text than R4's
law dash_conn_later_refused:
  for +f: Da.Disk
  for +m: Bool
  for +t: String
  for refused: {Da.frame(f, m) == Da.Refuse{t} : Da.Pass}
  {Da.cstep(Da.Paired{}, Da.CFrame{f, m}) == (Da.Closed{}, Da.VRefuse{t}) : Da.Conn & Da.Verdict}

# LAW dash_conn_out_of_order (C1, C2): a later frame before any pairing,
# and a second pairing frame of a paired socket, close the socket with
# "pairing needed", whatever the file holds and Rust reported
# EXCLUDES: a command frame taken as a pairing; a second pairing that
#   re-pairs or is ignored; another refusal text
law dash_conn_out_of_order:
  for +x: Da.First
  for +f: Da.Disk
  for +m: Bool
  {Da.cstep(Da.Waiting{}, Da.CFrame{f, m}) == (Da.Closed{}, Da.VRefuse{Dash.sp_missing()}) : Da.Conn & Da.Verdict} & {Da.cstep(Da.Paired{}, Da.CFirst{x, f, m}) == (Da.Closed{}, Da.VRefuse{Dash.sp_missing()}) : Da.Conn & Da.Verdict}

# LAW dash_conn_runs_only_matched (C2): from every socket state, a frame
# runs only when Rust reported a match against the file read at that
# moment, the file holds a token, and the socket is paired
# EXCLUDES: a frame run before pairing, after a rotation, with the file
#   gone, or without Rust's match
law dash_conn_runs_only_matched:
  for +c: Da.Conn
  for +e: Da.CEv
  for ran: {cv_is_run(cv_verdict(Da.cstep(c, e))) == True{} : Bool}
  {cv_frame_ok(c, e) == True{} : Bool}

# LAW dash_conn_matched_frame_runs (C2): a frame of a paired socket that
# Rust matched against a file holding a token runs, and the socket stays
# paired
# EXCLUDES: a valid tab locked out (a frame refused while its token is
#   current), a socket that unpairs after a frame
law dash_conn_matched_frame_runs:
  for +f: Da.Disk
  for holds: {cv_holds(f) == True{} : Bool}
  {Da.cstep(Da.Paired{}, Da.CFrame{f, True{}}) == (Da.Paired{}, Da.VRun{}) : Da.Conn & Da.Verdict}

# LAW dash_conn_pairs_only_matched (C1): from every socket state, a socket
# opens only on its first frame, when that frame presents a token, the
# file holds one, and Rust reported a match
# EXCLUDES: a socket opened twice, on an old token after a rotation, on a
#   blank or junk text, on a file with no token, without Rust's match
law dash_conn_pairs_only_matched:
  for +c: Da.Conn
  for +e: Da.CEv
  for paired: {cv_is_paired(cv_verdict(Da.cstep(c, e))) == True{} : Bool}
  {cv_pair_ok(c, e) == True{} : Bool}

# LAW dash_conn_matched_first_pairs (C1): a waiting socket whose first
# frame presents a token that Rust matched against a file holding a token
# pairs
# EXCLUDES: a valid tab refused its pairing
law dash_conn_matched_first_pairs:
  for +x: Da.First
  for +f: Da.Disk
  for shown: {cv_presents(x) == True{} : Bool}
  for holds: {cv_holds(f) == True{} : Bool}
  {Da.cstep(Da.Waiting{}, Da.CFirst{x, f, True{}}) == (Da.Paired{}, Da.VPaired{}) : Da.Conn & Da.Verdict}

# LAW dash_conn_nothing_before_pairing (C1): a waiting socket runs no
# frame, whatever comes
# EXCLUDES: a daemon command run for a tab that never paired
law dash_conn_nothing_before_pairing:
  for +e: Da.CEv
  {cv_is_run(cv_verdict(Da.cstep(Da.Waiting{}, e))) == False{} : Bool}

# LAW dash_conn_refusal_closes (C1, C2): from every socket state, a
# refusal closes the socket
# EXCLUDES: a refused socket that stays open (and runs later frames)
law dash_conn_refusal_closes:
  for +c: Da.Conn
  for +e: Da.CEv
  for refused: {cv_is_refuse(cv_verdict(Da.cstep(c, e))) == True{} : Bool}
  {cv_is_closed(cv_conn(Da.cstep(c, e))) == True{} : Bool}

# LAW dash_conn_refused_runs_nothing (C1-C3): after a refusal, from every
# socket state, nothing runs or opens, whatever comes
# EXCLUDES: a refused socket that runs a later frame or pairs again
law dash_conn_refused_runs_nothing:
  for +c: Da.Conn
  for +e: Da.CEv
  for +es: List<&2, Da.CEv>
  for refused: {cv_is_refuse(cv_verdict(Da.cstep(c, e))) == True{} : Bool}
  {cv_any_live(cv_run(es, cv_conn(Da.cstep(c, e)))) == False{} : Bool}

# LAW dash_conn_history (C1-C3): over every sequence of events from a
# socket that waits for its pairing, nothing runs before it pairs, it
# pairs at most once, and after a refusal nothing but `closed` comes
# EXCLUDES: any order of frames, rotations and pairings that runs a frame
#   for an unpaired socket or after a refusal
law dash_conn_history:
  for +es: List<&2, Da.CEv>
  {cv_ok(cv_run(es, Da.Waiting{}), PhWait{}) == True{} : Bool}

# LAW dash_conn_unmatched_ends (C1-C3): from every socket state, an event
# Rust did not match (a rotation, by any process, since the socket's token
# was made; another token; no token) ends the socket: it and every event
# after it run and open nothing, whatever comes, even if the file holds
# the token again. This is the core's half of a token rotation: once the
# file holds a new token, Rust's comparison reports no match for an old
# one (crates/eukhe-dashboard pairing.rs), and its socket ends here (with
# Rust's comparison spelled out, at the entry: dash_rotation_ends_connections,
# dash_rotation_rejects_old_tokens)
# EXCLUDES: a frame run after a rotation; a socket reopened when a
#   rotation is undone; an old token paired after a rotation
law dash_conn_unmatched_ends:
  for +c: Da.Conn
  for +e: Da.CEv
  for +es: List<&2, Da.CEv>
  for unmatched: {cv_matches(e) == False{} : Bool}
  {cv_any_live(cv_run(e <> es, c)) == False{} : Bool}

# LAW dash_conn_example (C1-C3): anchor: a token presented and matched
# pairs; frames run while the file holds a token and Rust matched; a frame
# after a rotation is refused and nothing runs after; a blank pairing, an
# unmatched token, a file with no token and a frame before pairing are
# refused with their texts
# EXCLUDES: a spec that takes any of the near misses
law dash_conn_example:
  {cv_run([Da.CFirst{Da.Pair{Da.Spoken{"00112233445566778899aabbccddeeff00112233445566778899aabbccddeeff"}}, Da.Holds{"00112233445566778899AABBCCDDEEFF00112233445566778899aabbccddeeff\n"}, True{}}, Da.CFrame{Da.Holds{"00112233445566778899aabbccddeeff00112233445566778899aabbccddeeff"}, True{}}, Da.CFrame{Da.Holds{"ff112233445566778899aabbccddeeff00112233445566778899aabbccddeeff"}, False{}}, Da.CFrame{Da.Holds{"00112233445566778899aabbccddeeff00112233445566778899aabbccddeeff"}, True{}}], Da.Waiting{}) == [Da.VPaired{}, Da.VRun{}, Da.VRefuse{Dash.sp_wrong()}, Da.VClosed{}] : List<&2, Da.Verdict>} & {[cv_verdict(Da.cstep(Da.Waiting{}, Da.CFirst{Da.Pair{Da.Spoken{""}}, Da.NoFile{}, False{}})), cv_verdict(Da.cstep(Da.Waiting{}, Da.CFirst{Da.Pair{Da.Spoken{"00112233445566778899aabbccddeeff00112233445566778899aabbccddeefe"}}, Da.Holds{"00112233445566778899aabbccddeeff00112233445566778899aabbccddeeff"}, False{}})), cv_verdict(Da.cstep(Da.Waiting{}, Da.CFirst{Da.Pair{Da.Spoken{"00112233445566778899aabbccddeeff00112233445566778899aabbccddeeff"}}, Da.Unread{}, False{}})), cv_verdict(Da.cstep(Da.Waiting{}, Da.CFrame{Da.NoFile{}, True{}})), cv_verdict(Da.cstep(Da.Paired{}, Da.CFrame{Da.NoFile{}, True{}}))] == [Da.VRefuse{Dash.sp_missing()}, Da.VRefuse{Dash.sp_wrong()}, Da.VRefuse{Dash.sp_unset()}, Da.VRefuse{Dash.sp_missing()}, Da.VRefuse{Dash.sp_unset()}] : List<&2, Da.Verdict>}

# LAW dash_conn_terms_witness: anchor: each laws-side term of the socket
# laws takes both values on some point (it is no constant answer); this
# says nothing about the code
# EXCLUDES: a vacuous term (one constant answer) that would make a safety
#   law say nothing
law dash_conn_terms_witness:
  {[cv_is_run(Da.VRun{}), cv_is_run(Da.VPaired{}), cv_is_paired(Da.VPaired{}), cv_is_paired(Da.VClosed{}), cv_is_refuse(Da.VRefuse{"x"}), cv_is_refuse(Da.VRun{}), cv_is_closed(Da.Closed{}), cv_is_closed(Da.Waiting{}), cv_any_live([Da.VClosed{}, Da.VRun{}]), cv_any_live([Da.VRefuse{"x"}, Da.VClosed{}]), cv_ok([Da.VRun{}], PhWait{}), cv_ok([Da.VRefuse{"x"}, Da.VRun{}], PhWait{}), cv_ok([Da.VPaired{}, Da.VRun{}, Da.VRefuse{"x"}, Da.VClosed{}], PhWait{}), cv_matches(Da.CFrame{Da.NoFile{}, True{}}), cv_matches(Da.CFirst{Da.NoText{}, Da.NoFile{}, False{}}), cv_frame_ok(Da.Paired{}, Da.CFrame{Da.Holds{"00112233445566778899aabbccddeeff00112233445566778899aabbccddeeff"}, True{}}), cv_frame_ok(Da.Paired{}, Da.CFrame{Da.Unread{}, True{}}), cv_pair_ok(Da.Waiting{}, Da.CFirst{Da.Pair{Da.Spoken{"00112233445566778899aabbccddeeff00112233445566778899aabbccddeeff"}}, Da.Holds{"00112233445566778899aabbccddeeff00112233445566778899aabbccddeeff"}, True{}}), cv_pair_ok(Da.Waiting{}, Da.CFirst{Da.Pair{Da.Spoken{"0g112233445566778899aabbccddeeff00112233445566778899aabbccddeeff"}}, Da.Holds{"00112233445566778899aabbccddeeff00112233445566778899aabbccddeeff"}, True{}})] == [True{}, False{}, True{}, False{}, True{}, False{}, True{}, False{}, True{}, False{}, False{}, False{}, True{}, True{}, False{}, True{}, False{}, True{}, False{}] : List<&2, Bool>}

# Laws: the entry
# ---------------

# LAW dash_conn_entry_open (C4): the open with no input is a socket
# waiting for its pairing, and replies nothing
# EXCLUDES: a socket that starts paired
law dash_conn_entry_open:
  {FDa.open("") == (FDa.Live{Da.Waiting{}}, "") : FDa.St & String}

# LAW dash_conn_entry_open_refused (C4): an open with input is refused
# with its error form
# EXCLUDES: a default socket for an open Rust never sends
law dash_conn_entry_open_refused:
  for +s: String
  for h: {String.is_empty(s) == False{} : Bool}
  {FDa.open(s) == (FDa.Refused{}, SCon{'E', SCon{' ', "dash: the open takes no input"}}) : FDa.St & String}

# LAW dash_conn_entry_refused_stays (C4): after an open with input, every
# step, of every input, answers the refused error form: the open's error
# first, then one refusal per input
# EXCLUDES: a refused socket that opens, pairs or runs later; a refused
#   open that forgets it was refused
law dash_conn_entry_refused_stays:
  for +s: String
  for +ins: List<&2, String>
  for h: {String.is_empty(s) == False{} : Bool}
  {cs_raw(ins, FDa.open(s)) == sp_open_refused() <> sp_shut(ins) : List<&2, String>}

# LAW dash_conn_entry_reads (C4): the shipped decoder reads back every
# event Rust spells (every length within the wire), leaving the rest
# untouched
# EXCLUDES: a decoder that refuses or misreads an event Rust sends (a
#   field read in another order, a tag misnumbered)
law dash_conn_entry_reads:
  for +e: Da.CEv
  for +rest: String
  for h: {sp_fit_ev(e) == True{} : Bool}
  {FDa.get_ev(sp_w_ev(e, rest)) == Wr.Got{e, rest} : Wr.Dec<Da.CEv>}

# LAW dash_conn_entry_exact (C4): from every socket, every input the step
# does not answer with the error form is exactly one event Rust spells,
# every length within the wire
# EXCLUDES: a verdict made on input that is no event (an unknown tag, a
#   malformed field, input left over)
law dash_conn_entry_exact:
  for +c: Da.Conn
  for +s: String
  for ok: {LawsBase.wire_opens_err(cs_out(FDa.step(FDa.Live{c}, s))) == False{} : Bool}
  exs e: Da.CEv
  {s == sp_w_ev(e, "") : String} & {sp_fit_ev(e) == True{} : Bool}

# LAW dash_conn_entry_refuses (C4): from every socket, every error the step
# answers is exactly `E dash: malformed event`, and the socket is kept
# EXCLUDES: a malformed input that moves or closes the socket; an error
#   text that varies with the input
law dash_conn_entry_refuses:
  for +c: Da.Conn
  for +s: String
  for bad: {LawsBase.wire_opens_err(cs_out(FDa.step(FDa.Live{c}, s))) == True{} : Bool}
  {FDa.step(FDa.Live{c}, s) == (FDa.Live{c}, sp_malformed()) : FDa.St & String}

# LAW dash_conn_entry_answers (C4): from every socket, every event Rust
# spells moves the socket as the model's step does (Da.cstep, whose laws
# are the socket laws above) and answers its verdict, spelled
# EXCLUDES: an event Rust sends refused or answered otherwise
law dash_conn_entry_answers:
  for +c: Da.Conn
  for +e: Da.CEv
  for h: {sp_fit_ev(e) == True{} : Bool}
  {FDa.step(FDa.Live{c}, sp_w_ev(e, "")) == cs_reply(Da.cstep(c, e)) : FDa.St & String}

# LAW dash_conn_entry_history (C4): the shipped stepper, opened as Rust
# opens it and fed any events Rust spells, replies to each what the model
# decides after the events before it, so every socket law holds for the
# socket Rust drives
# EXCLUDES: a stepper that forgets, reorders or replays an event
law dash_conn_entry_history:
  for +es: List<&2, Da.CEv>
  for fits: {sp_fit_evs(es) == True{} : Bool}
  {cs_feed(es, FDa.open("")) == "" <> cs_replies(es, Da.Waiting{}) : List<&2, String>}

# Laws: what an ended socket runs (C3, C5)
# ----------------------------------------

# LAW dash_closed_runs_nothing (C3): the shipped stepper of a closed
# socket answers every raw input of every run with `closed` (or, for an
# input that is no event, the malformed error): it never opens the socket
# again and never runs a frame, whatever comes (a pairing, a matched
# frame, a file that holds the token again, junk)
# EXCLUDES: a closed socket reopened by a pairing or a frame; a command run
#   for a closed socket; a closed socket that answers a refusal again
law dash_closed_runs_nothing:
  for +ins: List<&2, String>
  {cw_quiet(cs_outs(ins, FDa.Live{Da.Closed{}})) == True{} : Bool}

# LAW dash_rejected_runs_nothing (C1-C3): from every socket, once the
# shipped stepper answers an input with a refusal (tag 2 and its text, as
# Rust reads `Refuse`), the socket is closed: every later raw input of
# every run answers `closed` (or the malformed error), so nothing opens or
# runs for a rejected socket
# EXCLUDES: a rejected pairing or frame that leaves the socket waiting or
#   paired; a later frame of a rejected socket run; a rejected socket that
#   pairs again
law dash_rejected_runs_nothing:
  for +c: Da.Conn
  for +s: String
  for +t: String
  for +ins: List<&2, String>
  for refused: {cs_out(FDa.step(FDa.Live{c}, s)) == Wr.put_nat(2n, Wr.put_str(t, "")) : String}
  {cw_quiet(cs_outs(ins, cs_st(FDa.step(FDa.Live{c}, s)))) == True{} : Bool}

# LAW dash_rotation_ends_connections (C2, C5): a paired socket whose token
# is the bytes a, fed by the shipped stepper the later frames Rust sends
# (each with the file read at that frame and Rust's comparison of a with
# the file's token, pairing.rs `equal`), where the file at the first of
# them holds another token b (a rotation replaced it): that frame is
# refused with "not valid any more" and every frame after it answers
# `closed`, whatever the file holds later (the old token again included);
# every file text fits the wire
# EXCLUDES: a frame run after a rotation; a rotation that leaves sockets
#   open until they reconnect; a socket reopened when the old token comes
#   back; a rotation told with another text
law dash_rotation_ends_connections:
  for +a: List<&2, Nat>
  for +g: Da.Disk
  for +b: List<&2, Nat>
  for +fs: List<&2, Da.Disk>
  for rotated: {Dash.sp_stored(g) == Some{b} : Maybe<&2, List<&2, Nat>>}
  for other: {cv_bytes_same(a, b) == False{} : Bool}
  for fits: {cv_fit_disks(g <> fs) == True{} : Bool}
  {cs_feed(cv_frames(Some{a}, g <> fs), (FDa.Live{Da.Paired{}}, "")) == "" <> sp_w_verdict(Da.VRefuse{Dash.sp_wrong()}) <> cw_closed(fs) : List<&2, String>}

# LAW dash_rotation_rejects_old_tokens (C1, C5): after a rotation (the
# file g holds the token b), a new socket, opened as Rust opens it, whose
# pairing presents a text t that spells another token a (R1: an old token,
# or any other), with Rust's comparison of a with the file's token, is
# refused with "not valid any more", and every later frame it sends
# answers `closed`, whatever the file holds then (the old token again
# included); every text fits the wire
# EXCLUDES: a socket paired on an old token after a rotation; a refused
#   old-token socket that runs a later frame or pairs later; the refusal
#   told as "pairing needed" or "no pairing token"
law dash_rotation_rejects_old_tokens:
  for +t: String
  for +a: List<&2, Nat>
  for +g: Da.Disk
  for +b: List<&2, Nat>
  for +fs: List<&2, Da.Disk>
  for old: {Dash.sp_token(t) == Some{a} : Maybe<&2, List<&2, Nat>>}
  for rotated: {Dash.sp_stored(g) == Some{b} : Maybe<&2, List<&2, Nat>>}
  for other: {cv_bytes_same(a, b) == False{} : Bool}
  for fit: {LawsBase.wire_fits(String.length(t)) == True{} : Bool}
  for fits: {cv_fit_disks(g <> fs) == True{} : Bool}
  {cs_feed(cv_life(t, g, fs), FDa.open("")) == "" <> sp_w_verdict(Da.VRefuse{Dash.sp_wrong()}) <> cw_closed(fs) : List<&2, String>}

# LAW dash_rotation_example (C3, C5): anchor and premise witness: the
# current token pairs and runs; after a rotation an old token's socket is
# refused, and a paired socket's next frame is refused, then `closed` even
# when the old token comes back; a frame matched against the token runs;
# the laws-side terms take both values
# EXCLUDES: vacuous rotation premises; a spec that takes the old token
law dash_rotation_example:
  {[cs_feed(cv_life("00112233445566778899aabbccddeeff00112233445566778899aabbccddeeff", Da.Holds{"00112233445566778899aabbccddeeff00112233445566778899aabbccddeeff\n"}, [Da.Holds{"00112233445566778899aabbccddeeff00112233445566778899aabbccddeeff"}]), FDa.open("")), cs_feed(cv_life("00112233445566778899aabbccddeeff00112233445566778899aabbccddeeff", Da.Holds{"ff112233445566778899aabbccddeeff00112233445566778899aabbccddeeff\n"}, [Da.Holds{"00112233445566778899aabbccddeeff00112233445566778899aabbccddeeff"}]), FDa.open("")), cs_feed(cv_frames(Dash.sp_token("00112233445566778899aabbccddeeff00112233445566778899aabbccddeeff"), [Da.Holds{"ff112233445566778899aabbccddeeff00112233445566778899aabbccddeeff"}, Da.Holds{"00112233445566778899aabbccddeeff00112233445566778899aabbccddeeff"}]), (FDa.Live{Da.Paired{}}, ""))] == [["", "0,", "1,"], ["", Wr.put_nat(2n, Wr.put_str(Dash.sp_wrong(), "")), "3,"], ["", Wr.put_nat(2n, Wr.put_str(Dash.sp_wrong(), "")), "3,"]] : List<&2, List<&2, String>>} & {[cw_quiet1("3,"), cw_quiet1("1,"), cw_quiet1(sp_malformed()), cv_bytes_same([1n, 2n], [1n, 2n]), cv_bytes_same([1n, 2n], [1n, 3n]), cv_bytes_same([1n], [1n, 2n])] == [True{}, False{}, True{}, True{}, False{}, False{}] : List<&2, Bool>}

# LAW dash_conn_entry_example (C4): anchor: the bytes Rust sends and the
# replies: a matched pairing (paired), a matched frame (runs), an unmatched
# frame on a file with no token (refused with its text), one more
# (closed), an unknown tag and input left over
# EXCLUDES: another spelling of an event or a verdict
law dash_conn_entry_example:
  {cs_raw(["0,2,0,64,00112233445566778899aabbccddeeff00112233445566778899aabbccddeeff2,65,00112233445566778899aabbccddeeff00112233445566778899aabbccddeeff\nT", "1,2,64,00112233445566778899aabbccddeeff00112233445566778899aabbccddeeffT", "1,0,F", "1,0,T", "2,", "1,0,Tx"], FDa.open("")) == ["", "0,", "1,", Wr.put_nat(2n, Wr.put_str(Dash.sp_unset(), "")), "3,", sp_malformed(), sp_malformed()] : List<&2, String>}

# LAW dash_conn_fits_example (C4): witness: events of each kind Rust sends
# fit the wire (the entry laws are not vacuous)
law dash_conn_fits_example:
  {sp_fit_evs([Da.CFirst{Da.Pair{Da.Spoken{"ab"}}, Da.Holds{"cd"}, True{}}, Da.CFirst{Da.NoText{}, Da.NoFile{}, False{}}, Da.CFrame{Da.Unread{}, True{}}, Da.CFrame{Da.Huge{}, False{}}]) == True{} : Bool}
