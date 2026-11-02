# ffi_worker: the entry of the compiled Bend core for the "main + worker"
# session shape (bend/worker.bend): the pause of the worker tree and the
# forward pick. A plain call: Rust (crates/eukhe-bend/src/rules/worker.rs)
# keeps the pause state in a durable doc and sends it with each event.
#
# Wire (crates/eukhe-bend/WIRE.md):
#   Mode     = tag 0 Run | 1 Paused
#   St       = a record (mode: Mode, parked: Maybe<Nat>, kept: List<Nat>,
#              inflight: Nat)
#   Ev       = tag 0 Pause | 1 Resume | 2 Gate (kind: Nat, id: Nat)
#              | 3 Done | 4 Msg (id: Nat, wakes: Bool) | 5 End
#   Msg      = a record (seq: Nat, text: String)
#   request  = tag 0 Step (st: St, ev: Ev)
#              | 1 Forward (cursor: Nat, msgs: List<Msg>, note: Maybe<String>)
#   reply    Step: the new St, then Verdict = tag 0 Go | 1 Hold
#              | 2 Release (List<Nat>) | 3 Kept | 4 Pass | 5 Ack
#            Forward: a record (cursor: Nat, picked: List<Nat>, body: String)
# A malformed request, or one with input left over, answers the error
# form.

import Base
import ./wire.bend as W
import ./worker.bend as M

type Req is Data:
  Step{st: M.St, ev: M.Ev}
  Forward{cursor: Nat, msgs: List<&2, M.UMsg>, note: Maybe<&2, String>}

# Lists of Nats
# -------------

def put_nats(xs: List<&2, Nat>, rest: String) -> String:
  W.put_list(~Nat, ~W.put_nat, xs, rest)

def get_nats(s: String) -> W.Dec<List<&2, Nat>>:
  W.get_list(~Nat, ~W.get_nat, s)

# The pause state
# ---------------

def put_mode(m: M.Mode, rest: String) -> String:
  match m:
    case M.Run{}:
      W.put_nat(0n, rest)
    case M.Paused{}:
      W.put_nat(1n, rest)

def get_mode.tag(t: Nat, s: String) -> W.Dec<M.Mode>:
  match t:
    case 0n:
      W.Got{M.Run{}, s}
    case 1n:
      W.Got{M.Paused{}, s}
    case 2n+x:
      W.Bad{}

def get_mode.go(d: W.Dec<Nat>) -> W.Dec<M.Mode>:
  match d:
    case W.Got{t, s}:
      get_mode.tag(t, s)
    case W.Bad{}:
      W.Bad{}

def get_mode(s: String) -> W.Dec<M.Mode>:
  get_mode.go(W.get_nat(s))

def put_parked(p: Maybe<&2, Nat>, rest: String) -> String:
  match p:
    case None{}:
      W.put_nat(0n, rest)
    case Some{x}:
      W.put_nat(1n, W.put_nat(x, rest))

def get_parked.some(d: W.Dec<Nat>) -> W.Dec<Maybe<&2, Nat>>:
  match d:
    case W.Got{x, s}:
      W.Got{Some{x}, s}
    case W.Bad{}:
      W.Bad{}

def get_parked.tag(t: Nat, s: String) -> W.Dec<Maybe<&2, Nat>>:
  match t:
    case 0n:
      W.Got{None{}, s}
    case 1n:
      get_parked.some(W.get_nat(s))
    case 2n+x:
      W.Bad{}

def get_parked.go(d: W.Dec<Nat>) -> W.Dec<Maybe<&2, Nat>>:
  match d:
    case W.Got{t, s}:
      get_parked.tag(t, s)
    case W.Bad{}:
      W.Bad{}

def get_parked(s: String) -> W.Dec<Maybe<&2, Nat>>:
  get_parked.go(W.get_nat(s))

def put_st(x: M.St, rest: String) -> String:
  match x:
    case M.St{m, p, k, n}:
      put_mode(m, put_parked(p, put_nats(k, W.put_nat(n, rest))))

def get_st.n(m: M.Mode, p: Maybe<&2, Nat>, k: List<&2, Nat>, d: W.Dec<Nat>) -> W.Dec<M.St>:
  match d:
    case W.Got{n, s}:
      W.Got{M.St{m, p, k, n}, s}
    case W.Bad{}:
      W.Bad{}

def get_st.kept(m: M.Mode, p: Maybe<&2, Nat>, d: W.Dec<List<&2, Nat>>) -> W.Dec<M.St>:
  match d:
    case W.Got{k, s}:
      get_st.n(m, p, k, W.get_nat(s))
    case W.Bad{}:
      W.Bad{}

def get_st.parked(m: M.Mode, d: W.Dec<Maybe<&2, Nat>>) -> W.Dec<M.St>:
  match d:
    case W.Got{p, s}:
      get_st.kept(m, p, get_nats(s))
    case W.Bad{}:
      W.Bad{}

def get_st.mode(d: W.Dec<M.Mode>) -> W.Dec<M.St>:
  match d:
    case W.Got{m, s}:
      get_st.parked(m, get_parked(s))
    case W.Bad{}:
      W.Bad{}

def get_st(s: String) -> W.Dec<M.St>:
  get_st.mode(get_mode(s))

# Events
# ------

def get_ev.gate.id(g: Nat, d: W.Dec<Nat>) -> W.Dec<M.Ev>:
  match d:
    case W.Got{i, s}:
      W.Got{M.Gate{g, i}, s}
    case W.Bad{}:
      W.Bad{}

def get_ev.gate(d: W.Dec<Nat>) -> W.Dec<M.Ev>:
  match d:
    case W.Got{g, s}:
      get_ev.gate.id(g, W.get_nat(s))
    case W.Bad{}:
      W.Bad{}

def get_ev.msg.wakes(i: Nat, d: W.Dec<Bool>) -> W.Dec<M.Ev>:
  match d:
    case W.Got{w, s}:
      W.Got{M.Msg{i, w}, s}
    case W.Bad{}:
      W.Bad{}

def get_ev.msg(d: W.Dec<Nat>) -> W.Dec<M.Ev>:
  match d:
    case W.Got{i, s}:
      get_ev.msg.wakes(i, W.get_bool(s))
    case W.Bad{}:
      W.Bad{}

def get_ev.tag(t: Nat, s: String) -> W.Dec<M.Ev>:
  match t:
    case 0n:
      W.Got{M.Pause{}, s}
    case 1n:
      W.Got{M.Resume{}, s}
    case 2n:
      get_ev.gate(W.get_nat(s))
    case 3n:
      W.Got{M.ToolDone{}, s}
    case 4n:
      get_ev.msg(W.get_nat(s))
    case 5n:
      W.Got{M.End{}, s}
    case 6n+x:
      W.Bad{}

def get_ev.go(d: W.Dec<Nat>) -> W.Dec<M.Ev>:
  match d:
    case W.Got{t, s}:
      get_ev.tag(t, s)
    case W.Bad{}:
      W.Bad{}

def get_ev(s: String) -> W.Dec<M.Ev>:
  get_ev.go(W.get_nat(s))

# Messages and the note
# ---------------------

def get_umsg.text(q: Nat, d: W.Dec<String>) -> W.Dec<M.UMsg>:
  match d:
    case W.Got{t, s}:
      W.Got{M.UMsg{q, t}, s}
    case W.Bad{}:
      W.Bad{}

def get_umsg.seq(d: W.Dec<Nat>) -> W.Dec<M.UMsg>:
  match d:
    case W.Got{q, s}:
      get_umsg.text(q, W.get_str(s))
    case W.Bad{}:
      W.Bad{}

def get_umsg(s: String) -> W.Dec<M.UMsg>:
  get_umsg.seq(W.get_nat(s))

def get_umsgs(s: String) -> W.Dec<List<&2, M.UMsg>>:
  W.get_list(~M.UMsg, ~get_umsg, s)

def get_note.some(d: W.Dec<String>) -> W.Dec<Maybe<&2, String>>:
  match d:
    case W.Got{n, s}:
      W.Got{Some{n}, s}
    case W.Bad{}:
      W.Bad{}

def get_note.tag(t: Nat, s: String) -> W.Dec<Maybe<&2, String>>:
  match t:
    case 0n:
      W.Got{None{}, s}
    case 1n:
      get_note.some(W.get_str(s))
    case 2n+x:
      W.Bad{}

def get_note.go(d: W.Dec<Nat>) -> W.Dec<Maybe<&2, String>>:
  match d:
    case W.Got{t, s}:
      get_note.tag(t, s)
    case W.Bad{}:
      W.Bad{}

def get_note(s: String) -> W.Dec<Maybe<&2, String>>:
  get_note.go(W.get_nat(s))

# The request
# -----------

def get_req.ev(x: M.St, d: W.Dec<M.Ev>) -> W.Dec<Req>:
  match d:
    case W.Got{e, s}:
      W.Got{Step{x, e}, s}
    case W.Bad{}:
      W.Bad{}

def get_req.st(d: W.Dec<M.St>) -> W.Dec<Req>:
  match d:
    case W.Got{x, s}:
      get_req.ev(x, get_ev(s))
    case W.Bad{}:
      W.Bad{}

def get_req.note(c: Nat, ms: List<&2, M.UMsg>, d: W.Dec<Maybe<&2, String>>) -> W.Dec<Req>:
  match d:
    case W.Got{n, s}:
      W.Got{Forward{c, ms, n}, s}
    case W.Bad{}:
      W.Bad{}

def get_req.msgs(c: Nat, d: W.Dec<List<&2, M.UMsg>>) -> W.Dec<Req>:
  match d:
    case W.Got{ms, s}:
      get_req.note(c, ms, get_note(s))
    case W.Bad{}:
      W.Bad{}

def get_req.cursor(d: W.Dec<Nat>) -> W.Dec<Req>:
  match d:
    case W.Got{c, s}:
      get_req.msgs(c, get_umsgs(s))
    case W.Bad{}:
      W.Bad{}

def get_req.tag(t: Nat, s: String) -> W.Dec<Req>:
  match t:
    case 0n:
      get_req.st(get_st(s))
    case 1n:
      get_req.cursor(W.get_nat(s))
    case 2n+x:
      W.Bad{}

def get_req.go(d: W.Dec<Nat>) -> W.Dec<Req>:
  match d:
    case W.Got{t, s}:
      get_req.tag(t, s)
    case W.Bad{}:
      W.Bad{}

def get_req(s: String) -> W.Dec<Req>:
  get_req.go(W.get_nat(s))

# Replies
# -------

def put_verdict(v: M.Verdict, rest: String) -> String:
  match v:
    case M.Go{}:
      W.put_nat(0n, rest)
    case M.Hold{}:
      W.put_nat(1n, rest)
    case M.Release{xs}:
      W.put_nat(2n, put_nats(xs, rest))
    case M.Kept{}:
      W.put_nat(3n, rest)
    case M.Pass{}:
      W.put_nat(4n, rest)
    case M.Ack{}:
      W.put_nat(5n, rest)

def get_verdict.release(d: W.Dec<List<&2, Nat>>) -> W.Dec<M.Verdict>:
  match d:
    case W.Got{xs, s}:
      W.Got{M.Release{xs}, s}
    case W.Bad{}:
      W.Bad{}

def get_verdict.tag(t: Nat, s: String) -> W.Dec<M.Verdict>:
  match t:
    case 0n:
      W.Got{M.Go{}, s}
    case 1n:
      W.Got{M.Hold{}, s}
    case 2n:
      get_verdict.release(get_nats(s))
    case 3n:
      W.Got{M.Kept{}, s}
    case 4n:
      W.Got{M.Pass{}, s}
    case 5n:
      W.Got{M.Ack{}, s}
    case 6n+x:
      W.Bad{}

def get_verdict.go(d: W.Dec<Nat>) -> W.Dec<M.Verdict>:
  match d:
    case W.Got{t, s}:
      get_verdict.tag(t, s)
    case W.Bad{}:
      W.Bad{}

def get_verdict(s: String) -> W.Dec<M.Verdict>:
  get_verdict.go(W.get_nat(s))

def put_pick(x: M.Pick, rest: String) -> String:
  match x:
    case M.Pick{c, ps, b}:
      W.put_nat(c, put_nats(ps, W.put_str(b, rest)))

def get_pick.body(c: Nat, ps: List<&2, Nat>, d: W.Dec<String>) -> W.Dec<M.Pick>:
  match d:
    case W.Got{b, s}:
      W.Got{M.Pick{c, ps, b}, s}
    case W.Bad{}:
      W.Bad{}

def get_pick.picked(c: Nat, d: W.Dec<List<&2, Nat>>) -> W.Dec<M.Pick>:
  match d:
    case W.Got{ps, s}:
      get_pick.body(c, ps, W.get_str(s))
    case W.Bad{}:
      W.Bad{}

def get_pick.cursor(d: W.Dec<Nat>) -> W.Dec<M.Pick>:
  match d:
    case W.Got{c, s}:
      get_pick.picked(c, get_nats(s))
    case W.Bad{}:
      W.Bad{}

def get_pick(s: String) -> W.Dec<M.Pick>:
  get_pick.cursor(W.get_nat(s))

# The entry
# ---------

def ffi.stepped(r: M.St & M.Verdict) -> String:
  (x, v) = r
  put_st(x, put_verdict(v, ""))

def ffi.run(r: Req) -> String:
  match r:
    case Step{x, e}:
      ffi.stepped(M.step(x, e))
    case Forward{c, ms, n}:
      put_pick(M.pick(c, ms, n), "")

def ffi.whole(r: Req, done: Bool) -> String:
  match done:
    case True{}:
      ffi.run(r)
    case False{}:
      W.err("worker: input left over")

def ffi.go(d: W.Dec<Req>) -> String:
  match d:
    case W.Got{r, s}:
      ffi.whole(r, W.end(s))
    case W.Bad{}:
      W.err("worker: malformed request")

# a pause step or a forward pick in, the model's answer out
def ffi(input: String) -> String:
  ffi.go(get_req(input))
