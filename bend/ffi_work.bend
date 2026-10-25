# ffi_work: the session's work as the stall checks measure it, as an
# entry of the compiled Bend core (bend/progress.bend). Two parts:
#
# - the stepper: the work ledger of one conversation
#   (crates/eukhe-core/src/durable/children/work.rs `WorkLedger`), kept in
#   the Bend heap. Each step is one event to `M.next`; the reply is its
#   answer.
# - the call: which last check the goal's progress check compares with
#   (`M.compared`, crates/eukhe-core/src/durable/goals/state.rs); Rust then
#   asks bend/ffi_progress.bend for the check.
#
# The codec is the wire format of bend/wire.bend (crates/eukhe-bend/WIRE.md):
#
#   open    nothing                                   reply: empty
#   step    Ev                                        reply: Out
#   Ev      0, at: Maybe<Nat>, List<Ent> (the view) | 1, List<Ent> (a page)
#           | 2, fp: Nat (a progress note)
#   Ent     id: Nat, List<Blk>
#   Blk     0, key: Nat, fp: Nat (a call) | 1, key: Nat, fp: Nat (a result)
#           | 2, (text) | 3, (thinking) | 4, (user) | 5, (system)
#   Out     0, work: Nat, read: Nat, last: Maybe<Nat> | 1, (again)
#   ffi     Maybe<Last>, Last = run: Bool, goal: Bool, stalls: Nat,
#           work: Nat                                 reply: Maybe<Prior>,
#           Prior = stalls: Nat, work: Nat
#
# A malformed event, or one with input left over, answers the wire's error
# form and keeps the ledger; an open with input opens the refused state,
# which answers every step with the error form; a malformed call answers
# the error form. laws/progress.bend (work_entry_*, prior_entry_*) pins
# the entry. Pure: no IO, no @unsafe.

import Base
import ./wire.bend as W
import ./progress.bend as M

# Decoders
# --------

def get_blk.res.fp(+k: Nat, r: W.Dec<Nat>) -> W.Dec<M.Blk>:
  match r:
    case W.Got{f, s}:
      W.Got{M.Res{k, f}, s}
    case W.Bad{}:
      W.Bad{}

def get_blk.res(r: W.Dec<Nat>) -> W.Dec<M.Blk>:
  match r:
    case W.Got{+k, s}:
      get_blk.res.fp(k, W.get_nat(s))
    case W.Bad{}:
      W.Bad{}

def get_blk.call.fp(+k: Nat, r: W.Dec<Nat>) -> W.Dec<M.Blk>:
  match r:
    case W.Got{f, s}:
      W.Got{M.Call{k, f}, s}
    case W.Bad{}:
      W.Bad{}

def get_blk.call(r: W.Dec<Nat>) -> W.Dec<M.Blk>:
  match r:
    case W.Got{+k, s}:
      get_blk.call.fp(k, W.get_nat(s))
    case W.Bad{}:
      W.Bad{}

def get_blk.tag(n: Nat, s: String) -> W.Dec<M.Blk>:
  match n:
    case 0n:
      get_blk.call(W.get_nat(s))
    case 1n:
      get_blk.res(W.get_nat(s))
    case 2n:
      W.Got{M.Txt{}, s}
    case 3n:
      W.Got{M.Think{}, s}
    case 4n:
      W.Got{M.User{}, s}
    case 5n:
      W.Got{M.Sys{}, s}
    case 6n+p:
      W.Bad{}

def get_blk.go(r: W.Dec<Nat>) -> W.Dec<M.Blk>:
  match r:
    case W.Got{n, s}:
      get_blk.tag(n, s)
    case W.Bad{}:
      W.Bad{}

# a block
def get_blk(s: String) -> W.Dec<M.Blk>:
  get_blk.go(W.get_nat(s))

def get_ent.bs(+i: Nat, r: W.Dec<List<&2, M.Blk>>) -> W.Dec<M.Ent>:
  match r:
    case W.Got{bs, s}:
      W.Got{M.Ent{i, bs}, s}
    case W.Bad{}:
      W.Bad{}

def get_ent.go(r: W.Dec<Nat>) -> W.Dec<M.Ent>:
  match r:
    case W.Got{+i, s}:
      get_ent.bs(i, W.get_list(~M.Blk, ~get_blk, s))
    case W.Bad{}:
      W.Bad{}

# an entry
def get_ent(s: String) -> W.Dec<M.Ent>:
  get_ent.go(W.get_nat(s))

def get_at.some(r: W.Dec<Nat>) -> W.Dec<Maybe<&2, Nat>>:
  match r:
    case W.Got{x, s}:
      W.Got{Some{x}, s}
    case W.Bad{}:
      W.Bad{}

def get_at.tag(n: Nat, s: String) -> W.Dec<Maybe<&2, Nat>>:
  match n:
    case 0n:
      W.Got{None{}, s}
    case 1n:
      get_at.some(W.get_nat(s))
    case 2n+p:
      W.Bad{}

def get_at.go(r: W.Dec<Nat>) -> W.Dec<Maybe<&2, Nat>>:
  match r:
    case W.Got{n, s}:
      get_at.tag(n, s)
    case W.Bad{}:
      W.Bad{}

# a Maybe<Nat>
def get_at(s: String) -> W.Dec<Maybe<&2, Nat>>:
  get_at.go(W.get_nat(s))

def get_ev.view(at: Maybe<&2, Nat>, r: W.Dec<List<&2, M.Ent>>) -> W.Dec<M.Ev>:
  match r:
    case W.Got{es, s}:
      W.Got{M.View{at, es}, s}
    case W.Bad{}:
      W.Bad{}

def get_ev.at(r: W.Dec<Maybe<&2, Nat>>) -> W.Dec<M.Ev>:
  match r:
    case W.Got{at, s}:
      get_ev.view(at, W.get_list(~M.Ent, ~get_ent, s))
    case W.Bad{}:
      W.Bad{}

def get_ev.page(r: W.Dec<List<&2, M.Ent>>) -> W.Dec<M.Ev>:
  match r:
    case W.Got{es, s}:
      W.Got{M.Page{es}, s}
    case W.Bad{}:
      W.Bad{}

def get_ev.note(r: W.Dec<Nat>) -> W.Dec<M.Ev>:
  match r:
    case W.Got{x, s}:
      W.Got{M.Note{x}, s}
    case W.Bad{}:
      W.Bad{}

def get_ev.tag(n: Nat, s: String) -> W.Dec<M.Ev>:
  match n:
    case 0n:
      get_ev.at(get_at(s))
    case 1n:
      get_ev.page(W.get_list(~M.Ent, ~get_ent, s))
    case 2n:
      get_ev.note(W.get_nat(s))
    case 3n+p:
      W.Bad{}

def get_ev.go(r: W.Dec<Nat>) -> W.Dec<M.Ev>:
  match r:
    case W.Got{n, s}:
      get_ev.tag(n, s)
    case W.Bad{}:
      W.Bad{}

# the event of a step
def get_ev(s: String) -> W.Dec<M.Ev>:
  get_ev.go(W.get_nat(s))

def get_last.work(r: Bool, g: Bool, +n: Nat, d: W.Dec<Nat>) -> W.Dec<Maybe<&2, M.Last>>:
  match d:
    case W.Got{w, s}:
      W.Got{Some{M.Last{r, g, n, w}}, s}
    case W.Bad{}:
      W.Bad{}

def get_last.stalls(r: Bool, g: Bool, d: W.Dec<Nat>) -> W.Dec<Maybe<&2, M.Last>>:
  match d:
    case W.Got{+n, s}:
      get_last.work(r, g, n, W.get_nat(s))
    case W.Bad{}:
      W.Bad{}

def get_last.goal(r: Bool, d: W.Dec<Bool>) -> W.Dec<Maybe<&2, M.Last>>:
  match d:
    case W.Got{g, s}:
      get_last.stalls(r, g, W.get_nat(s))
    case W.Bad{}:
      W.Bad{}

def get_last.run(d: W.Dec<Bool>) -> W.Dec<Maybe<&2, M.Last>>:
  match d:
    case W.Got{r, s}:
      get_last.goal(r, W.get_bool(s))
    case W.Bad{}:
      W.Bad{}

def get_last.tag(n: Nat, s: String) -> W.Dec<Maybe<&2, M.Last>>:
  match n:
    case 0n:
      W.Got{None{}, s}
    case 1n:
      get_last.run(W.get_bool(s))
    case 2n+p:
      W.Bad{}

def get_last.go(r: W.Dec<Nat>) -> W.Dec<Maybe<&2, M.Last>>:
  match r:
    case W.Got{n, s}:
      get_last.tag(n, s)
    case W.Bad{}:
      W.Bad{}

# the request of the call: the last check, if any
def get_last(s: String) -> W.Dec<Maybe<&2, M.Last>>:
  get_last.go(W.get_nat(s))

# Encoders
# --------

def put_at(m: Maybe<&2, Nat>, rest: String) -> String:
  match m:
    case None{}:
      W.put_nat(0n, rest)
    case Some{x}:
      W.put_nat(1n, W.put_nat(x, rest))

# the reply of a step
def put_out(o: M.Out) -> String:
  match o:
    case M.Read{w, r, z}:
      W.put_nat(0n, W.put_nat(w, W.put_nat(r, put_at(z, ""))))
    case M.Again{}:
      W.put_nat(1n, "")

# the reply of the call
def put_prior(m: Maybe<&2, M.Prior>) -> String:
  match m:
    case None{}:
      W.put_nat(0n, "")
    case Some{p}:
      match p:
        case M.Prior{s, w}:
          W.put_nat(1n, W.put_nat(s, W.put_nat(w, "")))

# The call
# --------

def run.end(whole: Bool, m: Maybe<&2, M.Last>) -> String:
  match whole:
    case True{}:
      put_prior(M.compared(m))
    case False{}:
      W.err("work: malformed request")

def run(r: W.Dec<Maybe<&2, M.Last>>) -> String:
  match r:
    case W.Got{m, s}:
      run.end(W.end(s), m)
    case W.Bad{}:
      W.err("work: malformed request")

# the entry's call: the prior check the goal's check compares with
def ffi(input: String) -> String:
  run(get_last(input))

# The stepper
# -----------

# the ledger, or a refused open
type St is Data:
  Live{l: M.Led}
  Shut{}

def open.go(done: Bool) -> St & String:
  match done:
    case True{}:
      (Live{M.Led.empty()}, "")
    case False{}:
      (Shut{}, W.err("work: the open takes no input"))

# open: a ledger that read nothing
def open(input: String) -> St & String:
  open.go(W.end(input))

def step.out(r: M.Led & M.Out) -> St & String:
  (l, o) = r
  (Live{l}, put_out(o))

def step.end(done: Bool, l: M.Led, e: M.Ev) -> St & String:
  match done:
    case True{}:
      step.out(M.next(l, e))
    case False{}:
      (Live{l}, W.err("work: malformed event"))

def step.ev(l: M.Led, r: W.Dec<M.Ev>) -> St & String:
  match r:
    case W.Got{e, rest}:
      step.end(W.end(rest), l, e)
    case W.Bad{}:
      (Live{l}, W.err("work: malformed event"))

# step: one event of the ledger; the reply is its answer
def step(st: St, input: String) -> St & String:
  match st:
    case Live{l}:
      step.ev(l, get_ev(input))
    case Shut{}:
      (Shut{}, W.err("work: the open was refused"))
