# ffi_notice: the stepper of the compiled Bend core for the kernel restore
# notices a TUI view shows (crates/eukhe-tui/src/restore_notices.rs): its
# state is the view's record of bend/notice.bend (the restore notices it
# showed), kept in the Bend heap. Each step is one ask to `M.answer`; the
# reply is its answer. The codec is the wire format of bend/wire.bend
# (crates/eukhe-bend/WIRE.md):
#
#   open   nothing                                        reply: empty
#   step   Ask                                            reply: Ans
#   Ask    0, sid: String, Msg (shows) | 1, sid: String, List<Msg> (notes)
#   Msg    0 (another role) | 1, kind: String, stamp: String (custom)
#   Ans    Bool (shown) | empty (noted)
#
# A malformed ask, or one with input left over, answers the wire's error
# form and keeps the record; an open with input opens the refused state,
# which answers every step with the error form. laws/notice.bend
# (notice_ffi_*) pins the entry. Pure: no IO, no @unsafe.

import Base
import ./wire.bend as W
import ./notice.bend as M

# Decoders
# --------

def get_msg.custom(k: String, r: W.Dec<String>) -> W.Dec<M.Msg>:
  match r:
    case W.Got{s, rest}:
      W.Got{M.Custom{k, s}, rest}
    case W.Bad{}:
      W.Bad{}

def get_msg.kind(r: W.Dec<String>) -> W.Dec<M.Msg>:
  match r:
    case W.Got{k, s}:
      get_msg.custom(k, W.get_str(s))
    case W.Bad{}:
      W.Bad{}

def get_msg.tag(n: Nat, s: String) -> W.Dec<M.Msg>:
  match n:
    case 0n:
      W.Got{M.Other{}, s}
    case 1n+a:
      match a:
        case 0n:
          get_msg.kind(W.get_str(s))
        case 1n+b:
          W.Bad{}

def get_msg.go(r: W.Dec<Nat>) -> W.Dec<M.Msg>:
  match r:
    case W.Got{n, s}:
      get_msg.tag(n, s)
    case W.Bad{}:
      W.Bad{}

# a message
def get_msg(s: String) -> W.Dec<M.Msg>:
  get_msg.go(W.get_nat(s))

def get_ask.shows(sid: String, r: W.Dec<M.Msg>) -> W.Dec<M.Ask>:
  match r:
    case W.Got{m, s}:
      W.Got{M.Shows{sid, m}, s}
    case W.Bad{}:
      W.Bad{}

def get_ask.notes(sid: String, r: W.Dec<List<&2, M.Msg>>) -> W.Dec<M.Ask>:
  match r:
    case W.Got{ms, s}:
      W.Got{M.Notes{sid, ms}, s}
    case W.Bad{}:
      W.Bad{}

def get_ask.shows.sid(r: W.Dec<String>) -> W.Dec<M.Ask>:
  match r:
    case W.Got{sid, s}:
      get_ask.shows(sid, get_msg(s))
    case W.Bad{}:
      W.Bad{}

def get_ask.notes.sid(r: W.Dec<String>) -> W.Dec<M.Ask>:
  match r:
    case W.Got{sid, s}:
      get_ask.notes(sid, W.get_list(~M.Msg, ~get_msg, s))
    case W.Bad{}:
      W.Bad{}

def get_ask.tag(n: Nat, s: String) -> W.Dec<M.Ask>:
  match n:
    case 0n:
      get_ask.shows.sid(W.get_str(s))
    case 1n+a:
      match a:
        case 0n:
          get_ask.notes.sid(W.get_str(s))
        case 1n+b:
          W.Bad{}

def get_ask.go(r: W.Dec<Nat>) -> W.Dec<M.Ask>:
  match r:
    case W.Got{n, s}:
      get_ask.tag(n, s)
    case W.Bad{}:
      W.Bad{}

# the ask of a step
def get_ask(s: String) -> W.Dec<M.Ask>:
  get_ask.go(W.get_nat(s))

# Encoders
# --------

# the reply of a step
def put_ans(a: M.Ans) -> String:
  match a:
    case M.Shown{b}:
      W.put_bool(b, "")
    case M.Noted{}:
      ""

# The stepper
# -----------

# the view's record, or a refused open
type St is Data:
  Live{rs: List<&2, M.Seen>}
  Shut{}

def open.go(done: Bool) -> St & String:
  match done:
    case True{}:
      (Live{Nil{}}, "")
    case False{}:
      (Shut{}, W.err("notice: the open takes no input"))

# open: an empty record (the view showed nothing yet)
def open(input: String) -> St & String:
  open.go(W.end(input))

def step.ans(r: List<&2, M.Seen> & M.Ans) -> St & String:
  (rs, a) = r
  (Live{rs}, put_ans(a))

def step.end(done: Bool, +rs: List<&2, M.Seen>, q: M.Ask) -> St & String:
  match done:
    case True{}:
      step.ans(M.answer(rs, q))
    case False{}:
      (Live{rs}, W.err("notice: malformed ask"))

def step.ask(rs: List<&2, M.Seen>, r: W.Dec<M.Ask>) -> St & String:
  match r:
    case W.Got{q, rest}:
      step.end(W.end(rest), rs, q)
    case W.Bad{}:
      (Live{rs}, W.err("notice: malformed ask"))

# step: one ask of the view; the reply is its answer
def step(st: St, input: String) -> St & String:
  match st:
    case Live{rs}:
      step.ask(rs, get_ask(input))
    case Shut{}:
      (Shut{}, W.err("notice: the open was refused"))
