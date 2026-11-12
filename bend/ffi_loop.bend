# ffi_loop: the entry of the compiled Bend core for `/loop`
# (bend/loop.bend): every decision of a loop (start, stop, abort, a new
# prompt, a settled turn, the evidence of the condition command, a worker
# restart) and the verdict of one piece of evidence. A plain call: Rust
# (crates/eukhe-bend/src/rules/loop_mode.rs) keeps the state in the
# session's durable storage, as the text this entry wrote, and sends it
# back with each event.
#
# Wire (crates/eukhe-bend/WIRE.md):
#   Cond    = tag 0 NoCond | 1 Until (cmd: String) | 2 While (cmd: String)
#   Evid    = tag 0 Exited (code: Nat) | 1 NoStatus | 2 TimedOut
#             | 3 SpawnFailed | 4 Cancelled
#   End     = tag 0 Satisfied | 1 CheckBroke | 2 OutOfTurns | 3 OutOfTime
#             | 4 TurnsFailed | 5 OutOfBudget | 6 Stopped
#   Phase   = tag 0 Off | 1 Armed | 2 Turn | 3 Judging | 4 Paused
#             | 5 Ended (why: End)
#   Limit   = tag 0 NoLimit | 1 Count (n: Nat) | 2 Span (ms: Nat)
#   Out     = tag 0 Ran | 1 Errored | 2 Halted
#   Last    = tag 0 NoCheck | 1 Check (at: Nat, ev: Evid)
#   St      = a record (phase: Phase, iter: Nat, left: Maybe<Nat>,
#             deadline: Maybe<Nat>, cond: Cond, body: String, fails: Nat,
#             last: Last)
#   Ev      = tag 0 Enter (limit: Limit, cond: Cond,
#             prompt: Maybe<String>, now: Nat) | 1 Stop | 2 Abort
#             | 3 Prompt (text: String)
#             | 4 Settled (iter: Nat, out: Out, blocked: Bool, now: Nat,
#               funded: Bool)
#             | 5 Judged (iter: Nat, ev: Evid, blocked: Bool, now: Nat,
#               funded: Bool)
#             | 6 Restart
#   request = tag 0 Step (st: St, ev: Ev) | 1 Verdict (until: Bool, ev: Evid)
#   reply   Step: the new St, then Act = tag 0 Rest
#             | 1 Submit (iter: Nat, text: String) | 2 Adopt (iter: Nat)
#             | 3 Judge (iter: Nat) | 4 Resume (iter: Nat, text: String)
#             | 5 Report (why: End) | 6 Defer
#           Verdict: tag 0 Confirmed | 1 Refuted | 2 Broken | 3 Unjudged
# A malformed request, or one with input left over, answers the error
# form. Pure: no IO, no @unsafe.

import Base
import ./wire.bend as W
import ./loop.bend as M

type Req is Data:
  Step{st: M.St, ev: M.Ev}
  Verdict{until: Bool, ev: M.Evid}

# Maybe<Nat>, Maybe<String>
# -------------------------

def put_mnat(m: Maybe<&2, Nat>, rest: String) -> String:
  match m:
    case None{}:
      W.put_nat(0n, rest)
    case Some{x}:
      W.put_nat(1n, W.put_nat(x, rest))

def get_mnat.some(d: W.Dec<Nat>) -> W.Dec<Maybe<&2, Nat>>:
  match d:
    case W.Got{x, s}:
      W.Got{Some{x}, s}
    case W.Bad{}:
      W.Bad{}

def get_mnat.tag(t: Nat, s: String) -> W.Dec<Maybe<&2, Nat>>:
  match t:
    case 0n:
      W.Got{None{}, s}
    case 1n:
      get_mnat.some(W.get_nat(s))
    case 2n+x:
      W.Bad{}

def get_mnat.go(d: W.Dec<Nat>) -> W.Dec<Maybe<&2, Nat>>:
  match d:
    case W.Got{t, s}:
      get_mnat.tag(t, s)
    case W.Bad{}:
      W.Bad{}

def get_mnat(s: String) -> W.Dec<Maybe<&2, Nat>>:
  get_mnat.go(W.get_nat(s))

def get_mstr.some(d: W.Dec<String>) -> W.Dec<Maybe<&2, String>>:
  match d:
    case W.Got{x, s}:
      W.Got{Some{x}, s}
    case W.Bad{}:
      W.Bad{}

def get_mstr.tag(t: Nat, s: String) -> W.Dec<Maybe<&2, String>>:
  match t:
    case 0n:
      W.Got{None{}, s}
    case 1n:
      get_mstr.some(W.get_str(s))
    case 2n+x:
      W.Bad{}

def get_mstr.go(d: W.Dec<Nat>) -> W.Dec<Maybe<&2, String>>:
  match d:
    case W.Got{t, s}:
      get_mstr.tag(t, s)
    case W.Bad{}:
      W.Bad{}

def get_mstr(s: String) -> W.Dec<Maybe<&2, String>>:
  get_mstr.go(W.get_nat(s))

# The condition
# -------------

def put_cond(c: M.Cond, rest: String) -> String:
  match c:
    case M.NoCond{}:
      W.put_nat(0n, rest)
    case M.Until{cmd}:
      W.put_nat(1n, W.put_str(cmd, rest))
    case M.While{cmd}:
      W.put_nat(2n, W.put_str(cmd, rest))

def get_cond.until(d: W.Dec<String>) -> W.Dec<M.Cond>:
  match d:
    case W.Got{cmd, s}:
      W.Got{M.Until{cmd}, s}
    case W.Bad{}:
      W.Bad{}

def get_cond.while(d: W.Dec<String>) -> W.Dec<M.Cond>:
  match d:
    case W.Got{cmd, s}:
      W.Got{M.While{cmd}, s}
    case W.Bad{}:
      W.Bad{}

def get_cond.tag(t: Nat, s: String) -> W.Dec<M.Cond>:
  match t:
    case 0n:
      W.Got{M.NoCond{}, s}
    case 1n:
      get_cond.until(W.get_str(s))
    case 2n:
      get_cond.while(W.get_str(s))
    case 3n+x:
      W.Bad{}

def get_cond.go(d: W.Dec<Nat>) -> W.Dec<M.Cond>:
  match d:
    case W.Got{t, s}:
      get_cond.tag(t, s)
    case W.Bad{}:
      W.Bad{}

def get_cond(s: String) -> W.Dec<M.Cond>:
  get_cond.go(W.get_nat(s))

# The evidence
# ------------

def put_evid(e: M.Evid, rest: String) -> String:
  match e:
    case M.Exited{code}:
      W.put_nat(0n, W.put_nat(code, rest))
    case M.NoStatus{}:
      W.put_nat(1n, rest)
    case M.TimedOut{}:
      W.put_nat(2n, rest)
    case M.SpawnFailed{}:
      W.put_nat(3n, rest)
    case M.Cancelled{}:
      W.put_nat(4n, rest)

def get_evid.code(d: W.Dec<Nat>) -> W.Dec<M.Evid>:
  match d:
    case W.Got{code, s}:
      W.Got{M.Exited{code}, s}
    case W.Bad{}:
      W.Bad{}

def get_evid.tag(t: Nat, s: String) -> W.Dec<M.Evid>:
  match t:
    case 0n:
      get_evid.code(W.get_nat(s))
    case 1n:
      W.Got{M.NoStatus{}, s}
    case 2n:
      W.Got{M.TimedOut{}, s}
    case 3n:
      W.Got{M.SpawnFailed{}, s}
    case 4n:
      W.Got{M.Cancelled{}, s}
    case 5n+x:
      W.Bad{}

def get_evid.go(d: W.Dec<Nat>) -> W.Dec<M.Evid>:
  match d:
    case W.Got{t, s}:
      get_evid.tag(t, s)
    case W.Bad{}:
      W.Bad{}

def get_evid(s: String) -> W.Dec<M.Evid>:
  get_evid.go(W.get_nat(s))

# The end and the phase
# ---------------------

def put_end(w: M.End, rest: String) -> String:
  match w:
    case M.Satisfied{}:
      W.put_nat(0n, rest)
    case M.CheckBroke{}:
      W.put_nat(1n, rest)
    case M.OutOfTurns{}:
      W.put_nat(2n, rest)
    case M.OutOfTime{}:
      W.put_nat(3n, rest)
    case M.TurnsFailed{}:
      W.put_nat(4n, rest)
    case M.OutOfBudget{}:
      W.put_nat(5n, rest)
    case M.Stopped{}:
      W.put_nat(6n, rest)

def get_end.tag(t: Nat, s: String) -> W.Dec<M.End>:
  match t:
    case 0n:
      W.Got{M.Satisfied{}, s}
    case 1n:
      W.Got{M.CheckBroke{}, s}
    case 2n:
      W.Got{M.OutOfTurns{}, s}
    case 3n:
      W.Got{M.OutOfTime{}, s}
    case 4n:
      W.Got{M.TurnsFailed{}, s}
    case 5n:
      W.Got{M.OutOfBudget{}, s}
    case 6n:
      W.Got{M.Stopped{}, s}
    case 7n+x:
      W.Bad{}

def get_end.go(d: W.Dec<Nat>) -> W.Dec<M.End>:
  match d:
    case W.Got{t, s}:
      get_end.tag(t, s)
    case W.Bad{}:
      W.Bad{}

def get_end(s: String) -> W.Dec<M.End>:
  get_end.go(W.get_nat(s))

def put_phase(p: M.Phase, rest: String) -> String:
  match p:
    case M.Off{}:
      W.put_nat(0n, rest)
    case M.Armed{}:
      W.put_nat(1n, rest)
    case M.Turn{}:
      W.put_nat(2n, rest)
    case M.Judging{}:
      W.put_nat(3n, rest)
    case M.Paused{}:
      W.put_nat(4n, rest)
    case M.Ended{w}:
      W.put_nat(5n, put_end(w, rest))

def get_phase.ended(d: W.Dec<M.End>) -> W.Dec<M.Phase>:
  match d:
    case W.Got{w, s}:
      W.Got{M.Ended{w}, s}
    case W.Bad{}:
      W.Bad{}

def get_phase.tag(t: Nat, s: String) -> W.Dec<M.Phase>:
  match t:
    case 0n:
      W.Got{M.Off{}, s}
    case 1n:
      W.Got{M.Armed{}, s}
    case 2n:
      W.Got{M.Turn{}, s}
    case 3n:
      W.Got{M.Judging{}, s}
    case 4n:
      W.Got{M.Paused{}, s}
    case 5n:
      get_phase.ended(get_end(s))
    case 6n+x:
      W.Bad{}

def get_phase.go(d: W.Dec<Nat>) -> W.Dec<M.Phase>:
  match d:
    case W.Got{t, s}:
      get_phase.tag(t, s)
    case W.Bad{}:
      W.Bad{}

def get_phase(s: String) -> W.Dec<M.Phase>:
  get_phase.go(W.get_nat(s))

# The last evidence
# -----------------

def put_last(x: M.Last, rest: String) -> String:
  match x:
    case M.NoCheck{}:
      W.put_nat(0n, rest)
    case M.Check{at, ev}:
      W.put_nat(1n, W.put_nat(at, put_evid(ev, rest)))

def get_last.ev(at: Nat, d: W.Dec<M.Evid>) -> W.Dec<M.Last>:
  match d:
    case W.Got{ev, s}:
      W.Got{M.Check{at, ev}, s}
    case W.Bad{}:
      W.Bad{}

def get_last.at(d: W.Dec<Nat>) -> W.Dec<M.Last>:
  match d:
    case W.Got{at, s}:
      get_last.ev(at, get_evid(s))
    case W.Bad{}:
      W.Bad{}

def get_last.tag(t: Nat, s: String) -> W.Dec<M.Last>:
  match t:
    case 0n:
      W.Got{M.NoCheck{}, s}
    case 1n:
      get_last.at(W.get_nat(s))
    case 2n+x:
      W.Bad{}

def get_last.go(d: W.Dec<Nat>) -> W.Dec<M.Last>:
  match d:
    case W.Got{t, s}:
      get_last.tag(t, s)
    case W.Bad{}:
      W.Bad{}

def get_last(s: String) -> W.Dec<M.Last>:
  get_last.go(W.get_nat(s))

# The state
# ---------

def put_st(x: M.St, rest: String) -> String:
  match x:
    case M.St{p, i, l, d, c, b, f, z}:
      put_phase(p, W.put_nat(i, put_mnat(l, put_mnat(d, put_cond(c, W.put_str(b, W.put_nat(f, put_last(z, rest))))))))

def get_st.last(p: M.Phase, i: Nat, l: Maybe<&2, Nat>, d: Maybe<&2, Nat>, c: M.Cond, b: String, f: Nat, r: W.Dec<M.Last>) -> W.Dec<M.St>:
  match r:
    case W.Got{z, s}:
      W.Got{M.St{p, i, l, d, c, b, f, z}, s}
    case W.Bad{}:
      W.Bad{}

def get_st.fails(p: M.Phase, i: Nat, l: Maybe<&2, Nat>, d: Maybe<&2, Nat>, c: M.Cond, b: String, r: W.Dec<Nat>) -> W.Dec<M.St>:
  match r:
    case W.Got{f, s}:
      get_st.last(p, i, l, d, c, b, f, get_last(s))
    case W.Bad{}:
      W.Bad{}

def get_st.body(p: M.Phase, i: Nat, l: Maybe<&2, Nat>, d: Maybe<&2, Nat>, c: M.Cond, r: W.Dec<String>) -> W.Dec<M.St>:
  match r:
    case W.Got{b, s}:
      get_st.fails(p, i, l, d, c, b, W.get_nat(s))
    case W.Bad{}:
      W.Bad{}

def get_st.cond(p: M.Phase, i: Nat, l: Maybe<&2, Nat>, d: Maybe<&2, Nat>, r: W.Dec<M.Cond>) -> W.Dec<M.St>:
  match r:
    case W.Got{c, s}:
      get_st.body(p, i, l, d, c, W.get_str(s))
    case W.Bad{}:
      W.Bad{}

def get_st.deadline(p: M.Phase, i: Nat, l: Maybe<&2, Nat>, r: W.Dec<Maybe<&2, Nat>>) -> W.Dec<M.St>:
  match r:
    case W.Got{d, s}:
      get_st.cond(p, i, l, d, get_cond(s))
    case W.Bad{}:
      W.Bad{}

def get_st.left(p: M.Phase, i: Nat, r: W.Dec<Maybe<&2, Nat>>) -> W.Dec<M.St>:
  match r:
    case W.Got{l, s}:
      get_st.deadline(p, i, l, get_mnat(s))
    case W.Bad{}:
      W.Bad{}

def get_st.iter(p: M.Phase, r: W.Dec<Nat>) -> W.Dec<M.St>:
  match r:
    case W.Got{i, s}:
      get_st.left(p, i, get_mnat(s))
    case W.Bad{}:
      W.Bad{}

def get_st.phase(r: W.Dec<M.Phase>) -> W.Dec<M.St>:
  match r:
    case W.Got{p, s}:
      get_st.iter(p, W.get_nat(s))
    case W.Bad{}:
      W.Bad{}

def get_st(s: String) -> W.Dec<M.St>:
  get_st.phase(get_phase(s))

# Limits and outcomes
# -------------------

def get_limit.count(d: W.Dec<Nat>) -> W.Dec<M.Limit>:
  match d:
    case W.Got{n, s}:
      W.Got{M.Count{n}, s}
    case W.Bad{}:
      W.Bad{}

def get_limit.span(d: W.Dec<Nat>) -> W.Dec<M.Limit>:
  match d:
    case W.Got{ms, s}:
      W.Got{M.Span{ms}, s}
    case W.Bad{}:
      W.Bad{}

def get_limit.tag(t: Nat, s: String) -> W.Dec<M.Limit>:
  match t:
    case 0n:
      W.Got{M.NoLimit{}, s}
    case 1n:
      get_limit.count(W.get_nat(s))
    case 2n:
      get_limit.span(W.get_nat(s))
    case 3n+x:
      W.Bad{}

def get_limit.go(d: W.Dec<Nat>) -> W.Dec<M.Limit>:
  match d:
    case W.Got{t, s}:
      get_limit.tag(t, s)
    case W.Bad{}:
      W.Bad{}

def get_limit(s: String) -> W.Dec<M.Limit>:
  get_limit.go(W.get_nat(s))

def get_out.tag(t: Nat, s: String) -> W.Dec<M.Out>:
  match t:
    case 0n:
      W.Got{M.Ran{}, s}
    case 1n:
      W.Got{M.Errored{}, s}
    case 2n:
      W.Got{M.Halted{}, s}
    case 3n+x:
      W.Bad{}

def get_out.go(d: W.Dec<Nat>) -> W.Dec<M.Out>:
  match d:
    case W.Got{t, s}:
      get_out.tag(t, s)
    case W.Bad{}:
      W.Bad{}

def get_out(s: String) -> W.Dec<M.Out>:
  get_out.go(W.get_nat(s))

# Events
# ------

def get_ev.enter.now(lim: M.Limit, c: M.Cond, pr: Maybe<&2, String>, d: W.Dec<Nat>) -> W.Dec<M.Ev>:
  match d:
    case W.Got{now, s}:
      W.Got{M.Enter{lim, c, pr, now}, s}
    case W.Bad{}:
      W.Bad{}

def get_ev.enter.prompt(lim: M.Limit, c: M.Cond, d: W.Dec<Maybe<&2, String>>) -> W.Dec<M.Ev>:
  match d:
    case W.Got{pr, s}:
      get_ev.enter.now(lim, c, pr, W.get_nat(s))
    case W.Bad{}:
      W.Bad{}

def get_ev.enter.cond(lim: M.Limit, d: W.Dec<M.Cond>) -> W.Dec<M.Ev>:
  match d:
    case W.Got{c, s}:
      get_ev.enter.prompt(lim, c, get_mstr(s))
    case W.Bad{}:
      W.Bad{}

def get_ev.enter(d: W.Dec<M.Limit>) -> W.Dec<M.Ev>:
  match d:
    case W.Got{lim, s}:
      get_ev.enter.cond(lim, get_cond(s))
    case W.Bad{}:
      W.Bad{}

def get_ev.prompt(d: W.Dec<String>) -> W.Dec<M.Ev>:
  match d:
    case W.Got{t, s}:
      W.Got{M.Prompt{t}, s}
    case W.Bad{}:
      W.Bad{}

def get_ev.settled.funded(k: Nat, o: M.Out, b: Bool, now: Nat, d: W.Dec<Bool>) -> W.Dec<M.Ev>:
  match d:
    case W.Got{fu, s}:
      W.Got{M.Settled{k, o, b, now, fu}, s}
    case W.Bad{}:
      W.Bad{}

def get_ev.settled.now(k: Nat, o: M.Out, b: Bool, d: W.Dec<Nat>) -> W.Dec<M.Ev>:
  match d:
    case W.Got{now, s}:
      get_ev.settled.funded(k, o, b, now, W.get_bool(s))
    case W.Bad{}:
      W.Bad{}

def get_ev.settled.blocked(k: Nat, o: M.Out, d: W.Dec<Bool>) -> W.Dec<M.Ev>:
  match d:
    case W.Got{b, s}:
      get_ev.settled.now(k, o, b, W.get_nat(s))
    case W.Bad{}:
      W.Bad{}

def get_ev.settled.out(k: Nat, d: W.Dec<M.Out>) -> W.Dec<M.Ev>:
  match d:
    case W.Got{o, s}:
      get_ev.settled.blocked(k, o, W.get_bool(s))
    case W.Bad{}:
      W.Bad{}

def get_ev.settled(d: W.Dec<Nat>) -> W.Dec<M.Ev>:
  match d:
    case W.Got{k, s}:
      get_ev.settled.out(k, get_out(s))
    case W.Bad{}:
      W.Bad{}

def get_ev.judged.funded(k: Nat, ev: M.Evid, b: Bool, now: Nat, d: W.Dec<Bool>) -> W.Dec<M.Ev>:
  match d:
    case W.Got{fu, s}:
      W.Got{M.Judged{k, ev, b, now, fu}, s}
    case W.Bad{}:
      W.Bad{}

def get_ev.judged.now(k: Nat, ev: M.Evid, b: Bool, d: W.Dec<Nat>) -> W.Dec<M.Ev>:
  match d:
    case W.Got{now, s}:
      get_ev.judged.funded(k, ev, b, now, W.get_bool(s))
    case W.Bad{}:
      W.Bad{}

def get_ev.judged.blocked(k: Nat, ev: M.Evid, d: W.Dec<Bool>) -> W.Dec<M.Ev>:
  match d:
    case W.Got{b, s}:
      get_ev.judged.now(k, ev, b, W.get_nat(s))
    case W.Bad{}:
      W.Bad{}

def get_ev.judged.ev(k: Nat, d: W.Dec<M.Evid>) -> W.Dec<M.Ev>:
  match d:
    case W.Got{ev, s}:
      get_ev.judged.blocked(k, ev, W.get_bool(s))
    case W.Bad{}:
      W.Bad{}

def get_ev.judged(d: W.Dec<Nat>) -> W.Dec<M.Ev>:
  match d:
    case W.Got{k, s}:
      get_ev.judged.ev(k, get_evid(s))
    case W.Bad{}:
      W.Bad{}

def get_ev.tag(t: Nat, s: String) -> W.Dec<M.Ev>:
  match t:
    case 0n:
      get_ev.enter(get_limit(s))
    case 1n:
      W.Got{M.Stop{}, s}
    case 2n:
      W.Got{M.Abort{}, s}
    case 3n:
      get_ev.prompt(W.get_str(s))
    case 4n:
      get_ev.settled(W.get_nat(s))
    case 5n:
      get_ev.judged(W.get_nat(s))
    case 6n:
      W.Got{M.Restart{}, s}
    case 7n+x:
      W.Bad{}

def get_ev.go(d: W.Dec<Nat>) -> W.Dec<M.Ev>:
  match d:
    case W.Got{t, s}:
      get_ev.tag(t, s)
    case W.Bad{}:
      W.Bad{}

def get_ev(s: String) -> W.Dec<M.Ev>:
  get_ev.go(W.get_nat(s))

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

def get_req.evid(u: Bool, d: W.Dec<M.Evid>) -> W.Dec<Req>:
  match d:
    case W.Got{ev, s}:
      W.Got{Verdict{u, ev}, s}
    case W.Bad{}:
      W.Bad{}

def get_req.until(d: W.Dec<Bool>) -> W.Dec<Req>:
  match d:
    case W.Got{u, s}:
      get_req.evid(u, get_evid(s))
    case W.Bad{}:
      W.Bad{}

def get_req.tag(t: Nat, s: String) -> W.Dec<Req>:
  match t:
    case 0n:
      get_req.st(get_st(s))
    case 1n:
      get_req.until(W.get_bool(s))
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

def put_act(a: M.Act, rest: String) -> String:
  match a:
    case M.Rest{}:
      W.put_nat(0n, rest)
    case M.Submit{i, t}:
      W.put_nat(1n, W.put_nat(i, W.put_str(t, rest)))
    case M.Adopt{i}:
      W.put_nat(2n, W.put_nat(i, rest))
    case M.Judge{i}:
      W.put_nat(3n, W.put_nat(i, rest))
    case M.Resume{i, t}:
      W.put_nat(4n, W.put_nat(i, W.put_str(t, rest)))
    case M.Report{w}:
      W.put_nat(5n, put_end(w, rest))
    case M.Defer{}:
      W.put_nat(6n, rest)

def put_verdict(v: M.Verdict, rest: String) -> String:
  match v:
    case M.Confirmed{}:
      W.put_nat(0n, rest)
    case M.Refuted{}:
      W.put_nat(1n, rest)
    case M.Broken{}:
      W.put_nat(2n, rest)
    case M.Unjudged{}:
      W.put_nat(3n, rest)

# The entry
# ---------

def ffi.stepped(r: M.St & M.Act) -> String:
  (x, a) = r
  put_st(x, put_act(a, ""))

def ffi.run(r: Req) -> String:
  match r:
    case Step{x, e}:
      ffi.stepped(M.step(x, e))
    case Verdict{u, ev}:
      put_verdict(M.judge(u, ev), "")

def ffi.whole(r: Req, done: Bool) -> String:
  match done:
    case True{}:
      ffi.run(r)
    case False{}:
      W.err("loop: input left over")

def ffi.go(d: W.Dec<Req>) -> String:
  match d:
    case W.Got{r, s}:
      ffi.whole(r, W.end(s))
    case W.Bad{}:
      W.err("loop: malformed request")

# a loop step or a verdict in, the model's answer out
def ffi(input: String) -> String:
  ffi.go(get_req(input))
