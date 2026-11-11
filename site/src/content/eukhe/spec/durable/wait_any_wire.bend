# durable (spec): the wire of the wait_any entry
# (bend/ffi_wait_any.bend, crates/eukhe-bend/WIRE.md) restated without the
# entry's code: how Rust spells a request, which requests fit the wire,
# the reply the decisions of spec/durable/wait_any.bend spell, and the
# reader of a request. The laws of area wait_any state that the entry
# answers it. A spec: the shipped code never calls it.
#
# W1: a request is its tag, then its fields: 0 a poll: named, the cancel
#     fired, the cap passed (a Bool each), the targets (a list of Nats:
#     0 running, 1 ready, 2 gone); 1 a step: the session has a wake path
#     (Bool), the job's watchers (Nat), its phase (0 live, 1 kept, 2 sent)
#     and the event (0 watch, 1 unwatch, 2 settles, 3 taken); 2 a timeout:
#     the asked seconds (0 none | 1, the seconds). It fits when each Nat it
#     carries (the target count, the watchers, the seconds) fits the wire.
# W2: a reply is, for a poll, 0 wait | 1, the index taken | 2 nothing to
#     wait for | 3 capped | 4 cancelled; for a step, the watchers, the
#     phase and the deliveries made (a Nat each); for a timeout, the
#     seconds.
# W3: anything else is no request.

import Base
import ../../bend/wait_any.bend as Wa
import ../../bend/ffi_wait_any.bend as FWa
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ./wait_any.bend as WaSpec

# Codes (W1)
# ----------

def c_tgt(t: Wa.Tgt) -> Nat:
  match t:
    case Wa.Runs{}:
      0n
    case Wa.Unread{}:
      1n
    case Wa.Read{}:
      2n

def c_tgts(ts: List<&2, Wa.Tgt>) -> List<&2, Nat>:
  match ts:
    case Nil{}:
      Nil{}
    case Con{t, rest}:
      c_tgt(t) <> c_tgts(rest)

def c_phase(p: Wa.Phase) -> Nat:
  match p:
    case Wa.Live{}:
      0n
    case Wa.Kept{}:
      1n
    case Wa.Sent{}:
      2n

def c_ev(e: Wa.Ev) -> Nat:
  match e:
    case Wa.Watch{}:
      0n
    case Wa.Unwatch{}:
      1n
    case Wa.Settles{}:
      2n
    case Wa.Taken{}:
      3n

# Requests (W1)
# -------------

def w_asked(a: Maybe<&2, Nat>, rest: String) -> String:
  match a:
    case None{}:
      Wr.put_nat(0n, rest)
    case Some{t}:
      Wr.put_nat(1n, Wr.put_nat(t, rest))

# a request, then rest
def w_req(q: FWa.Req, rest: String) -> String:
  match q:
    case FWa.QPoll{n, c, l, ts}:
      Wr.put_nat(0n, Wr.put_bool(n, Wr.put_bool(c, Wr.put_bool(l, Wr.put_list(~Nat, ~Wr.put_nat, c_tgts(ts), rest)))))
    case FWa.QStep{k, d, e}:
      match d:
        case Wa.D{w, p}:
          Wr.put_nat(1n, Wr.put_bool(k, Wr.put_nat(w, Wr.put_nat(c_phase(p), Wr.put_nat(c_ev(e), rest)))))
    case FWa.QTimeout{a}:
      Wr.put_nat(2n, w_asked(a, rest))

def fit_asked(a: Maybe<&2, Nat>) -> Bool:
  match a:
    case None{}:
      True{}
    case Some{t}:
      LawsBase.wire_fits(t)

# every Nat the request carries fits the wire
def fit(q: FWa.Req) -> Bool:
  match q:
    case FWa.QPoll{n, c, l, +ts}:
      LawsBase.wire_fits(List.length(&2, Wa.Tgt, ts))
    case FWa.QStep{k, d, e}:
      match d:
        case Wa.D{w, p}:
          LawsBase.wire_fits(w)
    case FWa.QTimeout{a}:
      fit_asked(a)

# Replies (W2): the spec's decisions
# ----------------------------------

def w_pick(p: Wa.Pick) -> String:
  match p:
    case Wa.Waits{}:
      Wr.put_nat(0n, "")
    case Wa.Takes{i}:
      Wr.put_nat(1n, Wr.put_nat(i, ""))
    case Wa.NoWork{}:
      Wr.put_nat(2n, "")
    case Wa.Capped{}:
      Wr.put_nat(3n, "")
    case Wa.Stopped{}:
      Wr.put_nat(4n, "")

def w_out(o: Wa.Out) -> String:
  match o:
    case Wa.Out{d, k}:
      match d:
        case Wa.D{w, p}:
          Wr.put_nat(w, Wr.put_nat(c_phase(p), Wr.put_nat(k, "")))

# the reply to a request: the spec's decision, spelled
def w_reply(q: FWa.Req) -> String:
  match q:
    case FWa.QPoll{n, c, l, ts}:
      w_pick(WaSpec.poll(n, c, l, ts))
    case FWa.QStep{k, d, e}:
      w_out(WaSpec.step(k, d, e))
    case FWa.QTimeout{a}:
      Wr.put_nat(WaSpec.timeout(a), "")

# The reader (W3)
# ---------------

def r_tgt(n: Nat) -> Maybe<&2, Wa.Tgt>:
  match n:
    case 0n:
      Some{Wa.Runs{}}
    case 1n:
      Some{Wa.Unread{}}
    case 2n:
      Some{Wa.Read{}}
    case 3n+u:
      None{}

def r_tgts.cons(t: Maybe<&2, Wa.Tgt>, r: Maybe<&2, List<&2, Wa.Tgt>>) -> Maybe<&2, List<&2, Wa.Tgt>>:
  match t:
    case None{}:
      None{}
    case Some{x}:
      match r:
        case None{}:
          None{}
        case Some{xs}:
          Some{x <> xs}

def r_tgts(ns: List<&2, Nat>) -> Maybe<&2, List<&2, Wa.Tgt>>:
  match ns:
    case Nil{}:
      Some{Nil{}}
    case Con{n, rest}:
      r_tgts.cons(r_tgt(n), r_tgts(rest))

def r_phase(n: Nat) -> Maybe<&2, Wa.Phase>:
  match n:
    case 0n:
      Some{Wa.Live{}}
    case 1n:
      Some{Wa.Kept{}}
    case 2n:
      Some{Wa.Sent{}}
    case 3n+u:
      None{}

def r_ev(n: Nat) -> Maybe<&2, Wa.Ev>:
  match n:
    case 0n:
      Some{Wa.Watch{}}
    case 1n:
      Some{Wa.Unwatch{}}
    case 2n:
      Some{Wa.Settles{}}
    case 3n:
      Some{Wa.Taken{}}
    case 4n+u:
      None{}

def r_poll.ok(n: Bool, c: Bool, l: Bool, ts: Maybe<&2, List<&2, Wa.Tgt>>, s: String) -> Wr.Dec<FWa.Req>:
  match ts:
    case Some{xs}:
      Wr.Got{FWa.QPoll{n, c, l, xs}, s}
    case None{}:
      Wr.Bad{}

def r_poll.ts(n: Bool, c: Bool, l: Bool, x: Wr.Dec<List<&2, Nat>>) -> Wr.Dec<FWa.Req>:
  match x:
    case Wr.Got{ns, s}:
      r_poll.ok(n, c, l, r_tgts(ns), s)
    case Wr.Bad{}:
      Wr.Bad{}

def r_poll.late(n: Bool, c: Bool, x: Wr.Dec<Bool>) -> Wr.Dec<FWa.Req>:
  match x:
    case Wr.Got{l, s}:
      r_poll.ts(n, c, l, Wr.get_list(~Nat, ~Wr.get_nat, s))
    case Wr.Bad{}:
      Wr.Bad{}

def r_poll.cancel(n: Bool, x: Wr.Dec<Bool>) -> Wr.Dec<FWa.Req>:
  match x:
    case Wr.Got{c, s}:
      r_poll.late(n, c, Wr.get_bool(s))
    case Wr.Bad{}:
      Wr.Bad{}

def r_poll(x: Wr.Dec<Bool>) -> Wr.Dec<FWa.Req>:
  match x:
    case Wr.Got{n, s}:
      r_poll.cancel(n, Wr.get_bool(s))
    case Wr.Bad{}:
      Wr.Bad{}

def r_step.ok(k: Bool, w: Nat, p: Maybe<&2, Wa.Phase>, e: Maybe<&2, Wa.Ev>, s: String) -> Wr.Dec<FWa.Req>:
  match p:
    case None{}:
      Wr.Bad{}
    case Some{ph}:
      match e:
        case None{}:
          Wr.Bad{}
        case Some{ev}:
          Wr.Got{FWa.QStep{k, Wa.D{w, ph}, ev}, s}

def r_step.ev(k: Bool, w: Nat, p: Nat, x: Wr.Dec<Nat>) -> Wr.Dec<FWa.Req>:
  match x:
    case Wr.Got{e, s}:
      r_step.ok(k, w, r_phase(p), r_ev(e), s)
    case Wr.Bad{}:
      Wr.Bad{}

def r_step.phase(k: Bool, w: Nat, x: Wr.Dec<Nat>) -> Wr.Dec<FWa.Req>:
  match x:
    case Wr.Got{p, s}:
      r_step.ev(k, w, p, Wr.get_nat(s))
    case Wr.Bad{}:
      Wr.Bad{}

def r_step.watchers(k: Bool, x: Wr.Dec<Nat>) -> Wr.Dec<FWa.Req>:
  match x:
    case Wr.Got{w, s}:
      r_step.phase(k, w, Wr.get_nat(s))
    case Wr.Bad{}:
      Wr.Bad{}

def r_step(x: Wr.Dec<Bool>) -> Wr.Dec<FWa.Req>:
  match x:
    case Wr.Got{k, s}:
      r_step.watchers(k, Wr.get_nat(s))
    case Wr.Bad{}:
      Wr.Bad{}

def r_timeout.secs(x: Wr.Dec<Nat>) -> Wr.Dec<FWa.Req>:
  match x:
    case Wr.Got{t, s}:
      Wr.Got{FWa.QTimeout{Some{t}}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def r_timeout(x: Wr.Dec<Nat>) -> Wr.Dec<FWa.Req>:
  match x:
    case Wr.Got{t, s}:
      match t:
        case 0n:
          Wr.Got{FWa.QTimeout{None{}}, s}
        case 1n:
          r_timeout.secs(Wr.get_nat(s))
        case 2n+u:
          Wr.Bad{}
    case Wr.Bad{}:
      Wr.Bad{}

def r_req.tag(x: Wr.Dec<Nat>) -> Wr.Dec<FWa.Req>:
  match x:
    case Wr.Got{t, s}:
      match t:
        case 0n:
          r_poll(Wr.get_bool(s))
        case 1n:
          r_step(Wr.get_bool(s))
        case 2n:
          r_timeout(Wr.get_nat(s))
        case 3n+u:
          Wr.Bad{}
    case Wr.Bad{}:
      Wr.Bad{}

# a request at the start of s, read with the wire's decoders
def r_req(s: String) -> Wr.Dec<FWa.Req>:
  r_req.tag(Wr.get_nat(s))

def r_whole.end(e: Bool, q: FWa.Req) -> Maybe<&2, FWa.Req>:
  match e:
    case True{}:
      Some{q}
    case False{}:
      None{}

def r_whole(d: Wr.Dec<FWa.Req>) -> Maybe<&2, FWa.Req>:
  match d:
    case Wr.Got{q, +s}:
      r_whole.end(Wr.end(s), q)
    case Wr.Bad{}:
      None{}

# the request s spells whole, with nothing after it
def read_req(s: String) -> Maybe<&2, FWa.Req>:
  r_whole(r_req(s))
