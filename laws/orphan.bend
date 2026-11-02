# eukhe: the laws of area orphan

import Base
import ../bend/ffi_orphan.bend as FO
import ../bend/orphan.bend as Or
import ../bend/wire.bend as Wr
import ./base.bend as LawsBase

# The restart-budget entry of the compiled core (bend/ffi_supervise.bend)

# LAW orphan_never_aborts_resumable: a lost supervisor's worker never aborts work a later supervisor can
# resume: its exit aborts nothing and records the session busy exactly
# when it held work
law orphan_never_aborts_resumable:
  for +window: Nat
  for +evs: List<&2, Or.Ev>
  Or.Sound(Or.run(window, evs))

# LAW orphan_idle_exit_due: an orphaned worker without work exits once the whole window passed
# (any window, any absence)
# EXCLUDES: an exit before the window, a worker kept alive past it
law orphan_idle_exit_due:
  for +window: Nat
  for +absent: Nat
  {Or.exit_due.at(Some{window}, absent, Or.Idle{}) == Nat.is_le(window, absent) : Bool}

# LAW orphan_work_exit_due: an orphaned worker with work exits once two windows passed: the
# work defers the exit by exactly one more window, never forever
# EXCLUDES: work that does not defer the exit, defers it forever, or by
# a wrong amount
law orphan_work_exit_due:
  for +window: Nat
  for +absent: Nat
  {Or.exit_due.at(Some{window}, absent, Or.Ongoing{}) == Nat.is_le(Nat.add(window, window), absent) : Bool}

# LAW orphan_capped_window_never_expires: a window past the runtime's Nat range (Rust saturates a larger env
# window to `None`) never expires, whatever the absence and the work
# EXCLUDES: a saturated huge window that turns into an early exit
law orphan_capped_window_never_expires:
  for +absent: Nat
  for work: Or.Work
  {Or.exit_due.at(None{}, absent, work) == False{} : Bool}

def orphan_exit_spec(work: Or.Work) -> Or.Exit:
  match work:
    case Or.Idle{}:
      Or.Shut{}
    case Or.Ongoing{}:
      Or.Handover{}

# LAW orphan_exit_by_work: without work the orphan exit closes the session; with work it
# hands the work over (both values of Work)
# EXCLUDES: a handover of nothing, a close that drops work
law orphan_exit_by_work:
  for work: Or.Work
  {Or.orphan_exit(work) == orphan_exit_spec(work) : Or.Exit}

# The orphan entry of the compiled core (bend/ffi_orphan.bend)

# LAW orphan_wire_req_window: the entry reads back every request Rust writes: a window that fits
# the wire, an absence that fits, the work; the rest is untouched
# EXCLUDES: a misread window, absence or work, a lost or eaten rest
law orphan_wire_req_window:
  for +w: Nat
  for hw: {LawsBase.wire_fits(w) == True{} : Bool}
  for +a: Nat
  for ha: {LawsBase.wire_fits(a) == True{} : Bool}
  for +k: Or.Work
  for rest: String
  {FO.get_req(FO.put_req(FO.Req{Some{w}, a, k}, rest)) == Wr.Got{FO.Req{Some{w}, a, k}, rest} : Wr.Dec<FO.Req>}

# LAW orphan_wire_req_no_window: and a request with no window (past the wire's range)
# EXCLUDES: a missing window read as some window
law orphan_wire_req_no_window:
  for +a: Nat
  for ha: {LawsBase.wire_fits(a) == True{} : Bool}
  for +k: Or.Work
  for rest: String
  {FO.get_req(FO.put_req(FO.Req{None{}, a, k}, rest)) == Wr.Got{FO.Req{None{}, a, k}, rest} : Wr.Dec<FO.Req>}

# LAW orphan_wire_reply: Rust reads back every reply the entry writes
# EXCLUDES: a swapped due flag or exit
law orphan_wire_reply:
  for +d: Bool
  for +e: Or.Exit
  for rest: String
  {FO.get_reply(FO.put_reply(FO.Reply{d, e}, rest)) == Wr.Got{FO.Reply{d, e}, rest} : Wr.Dec<FO.Reply>}

# LAW orphan_ffi_decides: on a whole request the entry answers the model's decision: whether
# the worker exits now, and how
# EXCLUDES: an entry that answers anything but exit_due.at and orphan_exit
law orphan_ffi_decides:
  for +s: String
  for +m: Maybe<&2, Nat>
  for +a: Nat
  for +k: Or.Work
  for h: {FO.get_req(s) == Wr.Got{FO.Req{m, a, k}, ""} : Wr.Dec<FO.Req>}
  {FO.ffi(s) == FO.put_reply(FO.Reply{Or.exit_due.at(m, a, k), Or.orphan_exit(k)}, "") : String}

# LAW orphan_ffi_malformed: a malformed request answers the error form, never a decision
# EXCLUDES: a default decision on garbage
law orphan_ffi_malformed:
  for +s: String
  for h: {FO.get_req(s) == Wr.Bad{} : Wr.Dec<FO.Req>}
  {FO.ffi(s) == Wr.err("orphan: malformed request") : String}

# LAW orphan_ffi_left_over: a request with input after it answers the error form
# EXCLUDES: a decision on a request with trailing garbage
law orphan_ffi_left_over:
  for +s: String
  for +q: FO.Req
  for +r: String
  for h: {FO.get_req(s) == Wr.Got{q, r} : Wr.Dec<FO.Req>}
  for ne: {String.is_empty(r) == False{} : Bool}
  {FO.ffi(s) == Wr.err("orphan: input left over") : String}

# The whole entry, every input
# ----------------------------
# The request and the reply as the wire grammar of WIRE.md, read and
# spelled with the wire primitives alone (never the entry's own codec),
# and the decision as the requirement states it (never the model's code):
#   request  the window: 0 (none, past the wire's range) | 1 then the
#            window; the absence; the work: 0 idle | 1 ongoing
#   reply    whether the worker exits now, then how: 0 shut | 1 handover
# A request that cannot be read answers "orphan: malformed request"; a
# request with input after it answers "orphan: input left over".

def or_read.work(m: Maybe<&2, Nat>, a: Nat, r: Wr.Dec<Nat>) -> Wr.Dec<FO.Req>:
  match r:
    case Wr.Got{t, s}:
      match t:
        case 0n:
          Wr.Got{FO.Req{m, a, Or.Idle{}}, s}
        case 1n:
          Wr.Got{FO.Req{m, a, Or.Ongoing{}}, s}
        case 2n+p:
          Wr.Bad{}
    case Wr.Bad{}:
      Wr.Bad{}

def or_read.absent(m: Maybe<&2, Nat>, r: Wr.Dec<Nat>) -> Wr.Dec<FO.Req>:
  match r:
    case Wr.Got{a, s}:
      or_read.work(m, a, Wr.get_nat(s))
    case Wr.Bad{}:
      Wr.Bad{}

def or_read.window(r: Wr.Dec<Nat>) -> Wr.Dec<FO.Req>:
  match r:
    case Wr.Got{w, s}:
      or_read.absent(Some{w}, Wr.get_nat(s))
    case Wr.Bad{}:
      Wr.Bad{}

def or_read.tag(r: Wr.Dec<Nat>) -> Wr.Dec<FO.Req>:
  match r:
    case Wr.Got{t, s}:
      match t:
        case 0n:
          or_read.absent(None{}, Wr.get_nat(s))
        case 1n:
          or_read.window(Wr.get_nat(s))
        case 2n+p:
          Wr.Bad{}
    case Wr.Bad{}:
      Wr.Bad{}

# the request at the head of s, and the input after it
def or_read(s: String) -> Wr.Dec<FO.Req>:
  or_read.tag(Wr.get_nat(s))

# the worker exits now: never with no window (past the wire's range);
# without work once the window passed; with work once two windows passed
def or_due(m: Maybe<&2, Nat>, +a: Nat, k: Or.Work) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{+w}:
      match k:
        case Or.Idle{}:
          Nat.is_le(w, a)
        case Or.Ongoing{}:
          Nat.is_le(Nat.add(w, w), a)

# how the worker exits: without work it shuts the session (0), with work
# it hands the work over (1)
def or_exit_tag(k: Or.Work) -> Nat:
  match k:
    case Or.Idle{}:
      0n
    case Or.Ongoing{}:
      1n

def or_reply(q: FO.Req) -> String:
  match q:
    case FO.Req{m, a, +k}:
      Wr.put_bool(or_due(m, a, k), Wr.put_nat(or_exit_tag(k), ""))

def or_entry.of(d: Wr.Dec<FO.Req>) -> String:
  match d:
    case Wr.Got{q, r}:
      match r:
        case SNil{}:
          or_reply(q)
        case SCon{c, t}:
          Wr.err("orphan: input left over")
    case Wr.Bad{}:
      Wr.err("orphan: malformed request")

# the entry's answer to s
def or_entry(s: String) -> String:
  or_entry.of(or_read(s))

# LAW orphan_ffi_exact: for every input, the entry answers exactly: on a request (as the wire
# primitives read it) with nothing after it, whether the worker exits now
# (never with no window; idle once the window passed; with work once two
# windows passed) and how (idle: shut, with work: handover); on a request
# with input after it, the error form "orphan: input left over"; on any
# other input, the error form "orphan: malformed request"
# EXCLUDES: a misread or reordered field, a tag read as another, an exit
#   before or after its window, a swapped exit, a decision on garbage or on
#   a request with input after it, another error text, a codec of the
#   entry wrong both ways (the spec never calls it)
law orphan_ffi_exact:
  for +s: String
  {FO.ffi(s) == or_entry(s) : String}

# LAW orphan_ffi_exact_example: anchor: the strings Rust writes and the replies it reads: an
# idle worker past its window, a working one inside its second window, no
# window; an unknown window tag and input left over are refused
# EXCLUDES: a field order other than Rust's, a vacuous orphan_ffi_exact
law orphan_ffi_exact_example:
  {[or_entry("1,5,5,0,"), or_entry("1,5,9,1,"), or_entry("0,7,1,"), or_entry("2,5,0,"), or_entry("1,5,5,0,x")] == ["T0,", "F1,", "F1,", Wr.err("orphan: malformed request"), Wr.err("orphan: input left over")] : List<&2, String>}
