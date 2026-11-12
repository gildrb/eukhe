# durable (spec): the wire of the wait_any entry
# (bend/ffi_wait_any.bend, crates/eukhe-bend/WIRE.md) restated without the
# entry's code: how Rust spells a request, which requests fit the wire,
# and how a reply spells the model's decision (bend/wait_any.bend, whose
# answers the laws of area wait_any pin as properties). The laws state
# that the entry answers every spelled request with its spelled reply,
# and that any input it answers without the error form is a spelled
# request. A spec: the shipped code never calls it.
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
# W3: anything else is no request: the entry answers it with the error
#     form `E wait_any: malformed request`.

import Base
import ../../bend/wait_any.bend as Wa
import ../../bend/ffi_wait_any.bend as FWa
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase

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

# Replies (W2): a decision, spelled
# ---------------------------------

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

# the reply to a request: the model's decision, spelled
def w_reply(q: FWa.Req) -> String:
  match q:
    case FWa.QPoll{n, c, l, ts}:
      w_pick(Wa.poll(n, c, l, ts))
    case FWa.QStep{k, d, e}:
      w_out(Wa.step(k, d, e))
    case FWa.QTimeout{a}:
      Wr.put_nat(Wa.timeout(a), "")
