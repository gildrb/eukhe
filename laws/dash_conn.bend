# eukhe: the laws of area dash, section socket: the stepper each dashboard
# socket runs (bend/dash.bend section 2), as the compiled core runs it
# (bend/ffi_dash.bend open, step)

import Base
import ../bend/dash.bend as Da
import ../bend/ffi_dash.bend as FDa
import ../bend/wire.bend as Wr
import ./dash.bend as Dash

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
#     answers every input that is exactly one event (the grammar of
#     bend/ffi_dash.bend, restated by `read_ev`) with the step's verdict,
#     spelled; any other input answers exactly `E dash: malformed event`
#     and keeps the socket.

# Spec helpers
# ------------

def sp_pass.first(p: Da.Pass) -> Da.Conn & Da.Verdict:
  match p:
    case Da.Admit{}:
      (Da.Paired{}, Da.VPaired{})
    case Da.Refuse{t}:
      (Da.Closed{}, Da.VRefuse{t})

def sp_pass.later(p: Da.Pass) -> Da.Conn & Da.Verdict:
  match p:
    case Da.Admit{}:
      (Da.Paired{}, Da.VRun{})
    case Da.Refuse{t}:
      (Da.Closed{}, Da.VRefuse{t})

# C1-C3: one event of a socket
def sp_cstep(c: Da.Conn, e: Da.CEv) -> Da.Conn & Da.Verdict:
  match c:
    case Da.Waiting{}:
      match e:
        case Da.CFirst{x, f, m}:
          sp_pass.first(Dash.sp_gate(x, f, m))
        case Da.CFrame{f, m}:
          (Da.Closed{}, Da.VRefuse{Dash.sp_missing()})
    case Da.Paired{}:
      match e:
        case Da.CFirst{x, f, m}:
          (Da.Closed{}, Da.VRefuse{Dash.sp_missing()})
        case Da.CFrame{f, m}:
          sp_pass.later(Dash.sp_frame(f, m))
    case Da.Closed{}:
      (Da.Closed{}, Da.VClosed{})

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

def rd_disk.text(r: Wr.Dec<String>) -> Wr.Dec<Da.Disk>:
  match r:
    case Wr.Got{t, s}:
      Wr.Got{Da.Holds{t}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def rd_disk(r: Wr.Dec<Nat>) -> Wr.Dec<Da.Disk>:
  match r:
    case Wr.Got{t, s}:
      match t:
        case 0n:
          Wr.Got{Da.NoFile{}, s}
        case 1n:
          Wr.Got{Da.Unread{}, s}
        case 2n:
          rd_disk.text(Wr.get_str(s))
        case 3n:
          Wr.Got{Da.Huge{}, s}
        case 4n+u:
          Wr.Bad{}
    case Wr.Bad{}:
      Wr.Bad{}

def rd_said.spoken(r: Wr.Dec<String>) -> Wr.Dec<Da.Said>:
  match r:
    case Wr.Got{t, s}:
      Wr.Got{Da.Spoken{t}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def rd_said(r: Wr.Dec<Nat>) -> Wr.Dec<Da.Said>:
  match r:
    case Wr.Got{t, s}:
      match t:
        case 0n:
          rd_said.spoken(Wr.get_str(s))
        case 1n:
          Wr.Got{Da.Overlong{}, s}
        case 2n+u:
          Wr.Bad{}
    case Wr.Bad{}:
      Wr.Bad{}

def rd_first.pair(r: Wr.Dec<Da.Said>) -> Wr.Dec<Da.First>:
  match r:
    case Wr.Got{t, s}:
      Wr.Got{Da.Pair{t}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def rd_first(r: Wr.Dec<Nat>) -> Wr.Dec<Da.First>:
  match r:
    case Wr.Got{t, s}:
      match t:
        case 0n:
          Wr.Got{Da.NoText{}, s}
        case 1n:
          Wr.Got{Da.NotPairing{}, s}
        case 2n:
          rd_first.pair(rd_said(Wr.get_nat(s)))
        case 3n+u:
          Wr.Bad{}
    case Wr.Bad{}:
      Wr.Bad{}

def rd_ev.matches(x: Da.First, f: Da.Disk, r: Wr.Dec<Bool>) -> Wr.Dec<Da.CEv>:
  match r:
    case Wr.Got{m, s}:
      Wr.Got{Da.CFirst{x, f, m}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def rd_ev.first(x: Da.First, r: Wr.Dec<Da.Disk>) -> Wr.Dec<Da.CEv>:
  match r:
    case Wr.Got{f, s}:
      rd_ev.matches(x, f, Wr.get_bool(s))
    case Wr.Bad{}:
      Wr.Bad{}

def rd_ev.pair(r: Wr.Dec<Da.First>) -> Wr.Dec<Da.CEv>:
  match r:
    case Wr.Got{x, s}:
      rd_ev.first(x, rd_disk(Wr.get_nat(s)))
    case Wr.Bad{}:
      Wr.Bad{}

def rd_ev.later(f: Da.Disk, r: Wr.Dec<Bool>) -> Wr.Dec<Da.CEv>:
  match r:
    case Wr.Got{m, s}:
      Wr.Got{Da.CFrame{f, m}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def rd_ev.frame(r: Wr.Dec<Da.Disk>) -> Wr.Dec<Da.CEv>:
  match r:
    case Wr.Got{f, s}:
      rd_ev.later(f, Wr.get_bool(s))
    case Wr.Bad{}:
      Wr.Bad{}

def rd_ev.go(r: Wr.Dec<Nat>) -> Wr.Dec<Da.CEv>:
  match r:
    case Wr.Got{t, s}:
      match t:
        case 0n:
          rd_ev.pair(rd_first(Wr.get_nat(s)))
        case 1n:
          rd_ev.frame(rd_disk(Wr.get_nat(s)))
        case 2n+u:
          Wr.Bad{}
    case Wr.Bad{}:
      Wr.Bad{}

# the event s starts with, and what follows it
def read_ev(s: String) -> Wr.Dec<Da.CEv>:
  rd_ev.go(Wr.get_nat(s))

def cs_reply(r: Da.Conn & Da.Verdict) -> FDa.St & String:
  (c, v) = r
  (FDa.Live{c}, sp_w_verdict(v))

def cs.end(whole: Bool, +c: Da.Conn, e: Da.CEv) -> FDa.St & String:
  match whole:
    case True{}:
      cs_reply(sp_cstep(c, e))
    case False{}:
      (FDa.Live{c}, sp_malformed())

def cs.run(+c: Da.Conn, r: Wr.Dec<Da.CEv>) -> FDa.St & String:
  match r:
    case Wr.Got{e, s}:
      cs.end(Wr.end(s), c, e)
    case Wr.Bad{}:
      (FDa.Live{c}, sp_malformed())

# the step of a live socket c on s: the spec's step on the event s is
# exactly, spelled; else the error form, the socket kept
def cspec(+c: Da.Conn, s: String) -> FDa.St & String:
  cs.run(c, read_ev(s))

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

# the spec's replies to es from c, spelled
def cs_replies(es: List<&2, Da.CEv>, +c: Da.Conn) -> List<&2, String>:
  match es:
    case Nil{}:
      Nil{}
    case +e <> t:
      sp_w_verdict(cv_verdict(sp_cstep(c, e))) <> cs_replies(t, cv_conn(sp_cstep(c, e)))

# Laws: the socket
# ----------------

# LAW dash_conn_step_spec (C1-C3): every event, from every socket state,
# moves the socket and answers the verdict exactly as the spec's table
# (restates dash_gate_is_model and dash_frame_is_model over the stepper)
# EXCLUDES: a socket opened on a text that is no token, on a file with no
#   token, or without Rust's match; a frame that runs on a rotated,
#   missing or damaged file; a closed socket that runs or opens; a second
#   pairing taken; a refusal with another text
law dash_conn_step_spec:
  for +c: Da.Conn
  for +e: Da.CEv
  {Da.cstep(c, e) == sp_cstep(c, e) : Da.Conn & Da.Verdict}

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

# LAW dash_conn_closed_stays (C3): a closed socket stays closed and runs
# nothing, whatever comes (restates dash_closed_runs_nothing)
# EXCLUDES: a closed socket reopened by a pairing or a frame
law dash_conn_closed_stays:
  for +e: Da.CEv
  {Da.cstep(Da.Closed{}, e) == (Da.Closed{}, Da.VClosed{}) : Da.Conn & Da.Verdict}

# LAW dash_conn_refused_runs_nothing (C1-C3): after a refusal, from every
# socket state, nothing runs or opens, whatever comes (restates
# dash_rejected_runs_nothing)
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
# the token again (restates dash_rotation_ends_connections and
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

# LAW dash_conn_terms_exact: the terms of the socket laws mean what they
# say
# EXCLUDES: a vacuous term (one constant answer) that would make a safety
#   law say nothing
law dash_conn_terms_exact:
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

# LAW dash_conn_entry_shut (C4): a refused open answers every step with its
# error form
# EXCLUDES: a refused socket that opens or runs
law dash_conn_entry_shut:
  for +s: String
  {FDa.step(FDa.Refused{}, s) == (FDa.Refused{}, SCon{'E', SCon{' ', "dash: the open was refused"}}) : FDa.St & String}

# LAW dash_conn_entry_exact (C4): on every input, from every socket, the
# entry answers the spec's step on the event the input is exactly (as the
# wire's reader reads it), spelled; on any other input exactly the error
# form, the socket kept
# EXCLUDES: a field misread or swapped, a malformed event answered or
#   moving the socket, input left over ignored, another error text
law dash_conn_entry_exact:
  for +c: Da.Conn
  for +s: String
  {FDa.step(FDa.Live{c}, s) == cspec(c, s) : FDa.St & String}

# LAW dash_conn_entry_reads (C4): the reader reads back every event Rust
# spells (every length within the wire), leaving the rest untouched
# EXCLUDES: a reader that refuses or misreads an event Rust sends
law dash_conn_entry_reads:
  for +e: Da.CEv
  for +rest: String
  for h: {sp_fit_ev(e) == True{} : Bool}
  {read_ev(sp_w_ev(e, rest)) == Wr.Got{e, rest} : Wr.Dec<Da.CEv>}

# LAW dash_conn_entry_answers (C4): from every socket, every event Rust
# spells moves the socket as the spec's step does and answers its verdict
# EXCLUDES: an event Rust sends refused or answered otherwise
law dash_conn_entry_answers:
  for +c: Da.Conn
  for +e: Da.CEv
  for h: {sp_fit_ev(e) == True{} : Bool}
  {FDa.step(FDa.Live{c}, sp_w_ev(e, "")) == cs_reply(sp_cstep(c, e)) : FDa.St & String}

# LAW dash_conn_entry_history (C4): the shipped stepper, opened as Rust
# opens it and fed any events Rust spells, replies to each what the spec
# decides after the events before it: every socket law holds for the
# socket Rust drives
# EXCLUDES: a stepper that forgets, reorders or replays an event
law dash_conn_entry_history:
  for +es: List<&2, Da.CEv>
  for fits: {sp_fit_evs(es) == True{} : Bool}
  {cs_feed(es, FDa.open("")) == "" <> cs_replies(es, Da.Waiting{}) : List<&2, String>}

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
