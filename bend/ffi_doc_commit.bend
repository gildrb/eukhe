# ffi_doc_commit: the entry of the compiled Bend core for the writer's
# choices (bend/doc_commit.bend, section "The writer's choices"; Rust:
# crates/eukhe-docs write.rs, hashline/mod.rs, store.rs). Each request
# names one choice and carries what Rust met (crates/eukhe-bend/WIRE.md is
# the grammar):
#
#   tag 0  check    the files of an edit, List<Met>; Met = changed (Bool),
#                   taken (Bool)
#                   -> 0 go | 1, at (Nat), why (0 changed | 1 taken)
#   tag 1  publish  a Pub   -> Outcome
#   tag 2  answer   the staged files, List<Fate>
#                   -> 0 failure | 1, List<Note>, partial (Bool)
#   tag 3  gate     a Base, a Disk   -> 0 proceed | 1 unseen | 2 stale
#   tag 4  seen     a digest (String), the seen digests (List<String>)
#                   -> the seen digests after
#   tag 5  prefix   the digest of a target's file name (String)
#                   -> the name prefix of its temporary files (String)
#   tag 6  sweep    that digest, the entries List<Ent>; Ent = name
#                   (String), held (Bool)
#                   -> the indices of the entries to remove (List<Nat>)
#
#   Pub      0 Updated{Placed} | 1 Deleted{removed: Bool}
#            | 2 Moved{Placed, removed: Bool}
#   Placed   0 not placed | 1 Placed{synced: Bool}
#   Outcome  0 Lands{warn: 0 none | 1 sync | 2 remove} | 1 fails
#   Fate     0 noop | 1 Wrote{Outcome} | 2 untried
#   Note     0 untouched | 1 written | 2 unwritten | 3 Skipped{at: Nat}
#   Base     0 OnSeen{List<String>} | 1 on bytes
#   Disk     0 absent | 1 Present{digest: String, expected: Bool}
#
# Malformed input, or input left after the request, answers
# `E doc_commit: malformed request`, never a default. Pure: no IO, no
# @unsafe.

import Base
import ./wire.bend as W
import ./doc_commit.bend as Dc

# A request of the entry
type Req is Data:
  QCheck{mets: List<&2, Dc.Met>}
  QPublish{pub: Dc.Pub}
  QAnswer{fates: List<&2, Dc.Fate>}
  QGate{base: Dc.Base, disk: Dc.Disk}
  QSeen{digest: String, seen: List<&2, String>}
  QPrefix{h: String}
  QSweep{h: String, ents: List<&2, Dc.Ent>}

# Requests
# --------

def get_met.taken(c: Bool, r: W.Dec<Bool>) -> W.Dec<Dc.Met>:
  match r:
    case W.Got{t, s}:
      W.Got{Dc.Met{c, t}, s}
    case W.Bad{}:
      W.Bad{}

def get_met.changed(r: W.Dec<Bool>) -> W.Dec<Dc.Met>:
  match r:
    case W.Got{c, s}:
      get_met.taken(c, W.get_bool(s))
    case W.Bad{}:
      W.Bad{}

def get_met(s: String) -> W.Dec<Dc.Met>:
  get_met.changed(W.get_bool(s))

def get_placed.synced(r: W.Dec<Bool>) -> W.Dec<Dc.Placed>:
  match r:
    case W.Got{b, s}:
      W.Got{Dc.Placed{b}, s}
    case W.Bad{}:
      W.Bad{}

def get_placed.tag(t: Nat, s: String) -> W.Dec<Dc.Placed>:
  match t:
    case 0n:
      W.Got{Dc.NotPlaced{}, s}
    case 1n:
      get_placed.synced(W.get_bool(s))
    case 2n+u:
      W.Bad{}

def get_placed(r: W.Dec<Nat>) -> W.Dec<Dc.Placed>:
  match r:
    case W.Got{t, s}:
      get_placed.tag(t, s)
    case W.Bad{}:
      W.Bad{}

def get_pub.updated(r: W.Dec<Dc.Placed>) -> W.Dec<Dc.Pub>:
  match r:
    case W.Got{x, s}:
      W.Got{Dc.Updated{x}, s}
    case W.Bad{}:
      W.Bad{}

def get_pub.deleted(r: W.Dec<Bool>) -> W.Dec<Dc.Pub>:
  match r:
    case W.Got{b, s}:
      W.Got{Dc.Deleted{b}, s}
    case W.Bad{}:
      W.Bad{}

def get_pub.removed(x: Dc.Placed, r: W.Dec<Bool>) -> W.Dec<Dc.Pub>:
  match r:
    case W.Got{b, s}:
      W.Got{Dc.Moved{x, b}, s}
    case W.Bad{}:
      W.Bad{}

def get_pub.moved(r: W.Dec<Dc.Placed>) -> W.Dec<Dc.Pub>:
  match r:
    case W.Got{x, s}:
      get_pub.removed(x, W.get_bool(s))
    case W.Bad{}:
      W.Bad{}

def get_pub.tag(t: Nat, s: String) -> W.Dec<Dc.Pub>:
  match t:
    case 0n:
      get_pub.updated(get_placed(W.get_nat(s)))
    case 1n:
      get_pub.deleted(W.get_bool(s))
    case 2n:
      get_pub.moved(get_placed(W.get_nat(s)))
    case 3n+u:
      W.Bad{}

def get_pub(r: W.Dec<Nat>) -> W.Dec<Dc.Pub>:
  match r:
    case W.Got{t, s}:
      get_pub.tag(t, s)
    case W.Bad{}:
      W.Bad{}

def get_warn.tag(t: Nat, s: String) -> W.Dec<Dc.Warn>:
  match t:
    case 0n:
      W.Got{Dc.NoWarn{}, s}
    case 1n:
      W.Got{Dc.SyncWarn{}, s}
    case 2n:
      W.Got{Dc.RemoveWarn{}, s}
    case 3n+u:
      W.Bad{}

def get_outcome.warn(r: W.Dec<Dc.Warn>) -> W.Dec<Dc.Outcome>:
  match r:
    case W.Got{w, s}:
      W.Got{Dc.Lands{w}, s}
    case W.Bad{}:
      W.Bad{}

def get_outcome.lands(r: W.Dec<Nat>) -> W.Dec<Dc.Outcome>:
  match r:
    case W.Got{t, s}:
      get_outcome.warn(get_warn.tag(t, s))
    case W.Bad{}:
      W.Bad{}

def get_outcome.tag(t: Nat, s: String) -> W.Dec<Dc.Outcome>:
  match t:
    case 0n:
      get_outcome.lands(W.get_nat(s))
    case 1n:
      W.Got{Dc.Fails{}, s}
    case 2n+u:
      W.Bad{}

def get_outcome(r: W.Dec<Nat>) -> W.Dec<Dc.Outcome>:
  match r:
    case W.Got{t, s}:
      get_outcome.tag(t, s)
    case W.Bad{}:
      W.Bad{}

def get_fate.wrote(r: W.Dec<Dc.Outcome>) -> W.Dec<Dc.Fate>:
  match r:
    case W.Got{o, s}:
      W.Got{Dc.Wrote{o}, s}
    case W.Bad{}:
      W.Bad{}

def get_fate.tag(t: Nat, s: String) -> W.Dec<Dc.Fate>:
  match t:
    case 0n:
      W.Got{Dc.Noop{}, s}
    case 1n:
      get_fate.wrote(get_outcome(W.get_nat(s)))
    case 2n:
      W.Got{Dc.Untried{}, s}
    case 3n+u:
      W.Bad{}

def get_fate.start(r: W.Dec<Nat>) -> W.Dec<Dc.Fate>:
  match r:
    case W.Got{t, s}:
      get_fate.tag(t, s)
    case W.Bad{}:
      W.Bad{}

def get_fate(s: String) -> W.Dec<Dc.Fate>:
  get_fate.start(W.get_nat(s))

def get_strs(s: String) -> W.Dec<List<&2, String>>:
  W.get_list(~String, ~W.get_str, s)

def get_base.seen(r: W.Dec<List<&2, String>>) -> W.Dec<Dc.Base>:
  match r:
    case W.Got{xs, s}:
      W.Got{Dc.OnSeen{xs}, s}
    case W.Bad{}:
      W.Bad{}

def get_base.tag(t: Nat, s: String) -> W.Dec<Dc.Base>:
  match t:
    case 0n:
      get_base.seen(get_strs(s))
    case 1n:
      W.Got{Dc.OnBytes{}, s}
    case 2n+u:
      W.Bad{}

def get_base(r: W.Dec<Nat>) -> W.Dec<Dc.Base>:
  match r:
    case W.Got{t, s}:
      get_base.tag(t, s)
    case W.Bad{}:
      W.Bad{}

def get_disk.expected(g: String, r: W.Dec<Bool>) -> W.Dec<Dc.Disk>:
  match r:
    case W.Got{e, s}:
      W.Got{Dc.Present{g, e}, s}
    case W.Bad{}:
      W.Bad{}

def get_disk.digest(r: W.Dec<String>) -> W.Dec<Dc.Disk>:
  match r:
    case W.Got{g, s}:
      get_disk.expected(g, W.get_bool(s))
    case W.Bad{}:
      W.Bad{}

def get_disk.tag(t: Nat, s: String) -> W.Dec<Dc.Disk>:
  match t:
    case 0n:
      W.Got{Dc.Absent{}, s}
    case 1n:
      get_disk.digest(W.get_str(s))
    case 2n+u:
      W.Bad{}

def get_disk(r: W.Dec<Nat>) -> W.Dec<Dc.Disk>:
  match r:
    case W.Got{t, s}:
      get_disk.tag(t, s)
    case W.Bad{}:
      W.Bad{}

def get_ent.held(n: String, r: W.Dec<Bool>) -> W.Dec<Dc.Ent>:
  match r:
    case W.Got{h, s}:
      W.Got{Dc.Ent{n, h}, s}
    case W.Bad{}:
      W.Bad{}

def get_ent.name(r: W.Dec<String>) -> W.Dec<Dc.Ent>:
  match r:
    case W.Got{n, s}:
      get_ent.held(n, W.get_bool(s))
    case W.Bad{}:
      W.Bad{}

def get_ent(s: String) -> W.Dec<Dc.Ent>:
  get_ent.name(W.get_str(s))

def get_check(r: W.Dec<List<&2, Dc.Met>>) -> W.Dec<Req>:
  match r:
    case W.Got{ms, s}:
      W.Got{QCheck{ms}, s}
    case W.Bad{}:
      W.Bad{}

def get_publish(r: W.Dec<Dc.Pub>) -> W.Dec<Req>:
  match r:
    case W.Got{p, s}:
      W.Got{QPublish{p}, s}
    case W.Bad{}:
      W.Bad{}

def get_answer(r: W.Dec<List<&2, Dc.Fate>>) -> W.Dec<Req>:
  match r:
    case W.Got{fs, s}:
      W.Got{QAnswer{fs}, s}
    case W.Bad{}:
      W.Bad{}

def get_gate.disk(b: Dc.Base, r: W.Dec<Dc.Disk>) -> W.Dec<Req>:
  match r:
    case W.Got{d, s}:
      W.Got{QGate{b, d}, s}
    case W.Bad{}:
      W.Bad{}

def get_gate(r: W.Dec<Dc.Base>) -> W.Dec<Req>:
  match r:
    case W.Got{b, s}:
      get_gate.disk(b, get_disk(W.get_nat(s)))
    case W.Bad{}:
      W.Bad{}

def get_seen.list(d: String, r: W.Dec<List<&2, String>>) -> W.Dec<Req>:
  match r:
    case W.Got{xs, s}:
      W.Got{QSeen{d, xs}, s}
    case W.Bad{}:
      W.Bad{}

def get_seen(r: W.Dec<String>) -> W.Dec<Req>:
  match r:
    case W.Got{d, s}:
      get_seen.list(d, get_strs(s))
    case W.Bad{}:
      W.Bad{}

def get_prefix(r: W.Dec<String>) -> W.Dec<Req>:
  match r:
    case W.Got{h, s}:
      W.Got{QPrefix{h}, s}
    case W.Bad{}:
      W.Bad{}

def get_sweep.ents(h: String, r: W.Dec<List<&2, Dc.Ent>>) -> W.Dec<Req>:
  match r:
    case W.Got{es, s}:
      W.Got{QSweep{h, es}, s}
    case W.Bad{}:
      W.Bad{}

def get_sweep(r: W.Dec<String>) -> W.Dec<Req>:
  match r:
    case W.Got{h, s}:
      get_sweep.ents(h, W.get_list(~Dc.Ent, ~get_ent, s))
    case W.Bad{}:
      W.Bad{}

def get_req.tag(t: Nat, s: String) -> W.Dec<Req>:
  match t:
    case 0n:
      get_check(W.get_list(~Dc.Met, ~get_met, s))
    case 1n:
      get_publish(get_pub(W.get_nat(s)))
    case 2n:
      get_answer(W.get_list(~Dc.Fate, ~get_fate, s))
    case 3n:
      get_gate(get_base(W.get_nat(s)))
    case 4n:
      get_seen(W.get_str(s))
    case 5n:
      get_prefix(W.get_str(s))
    case 6n:
      get_sweep(W.get_str(s))
    case 7n+u:
      W.Bad{}

def get_req.start(r: W.Dec<Nat>) -> W.Dec<Req>:
  match r:
    case W.Got{t, s}:
      get_req.tag(t, s)
    case W.Bad{}:
      W.Bad{}

def get_req(s: String) -> W.Dec<Req>:
  get_req.start(W.get_nat(s))

# Replies
# -------

def put_check(c: Dc.Check) -> String:
  match c:
    case Dc.Go{}:
      W.put_nat(0n, "")
    case Dc.Stop{at, why}:
      match why:
        case Dc.Changed{}:
          W.put_nat(1n, W.put_nat(at, W.put_nat(0n, "")))
        case Dc.Taken{}:
          W.put_nat(1n, W.put_nat(at, W.put_nat(1n, "")))

def put_warn(w: Dc.Warn, rest: String) -> String:
  match w:
    case Dc.NoWarn{}:
      W.put_nat(0n, rest)
    case Dc.SyncWarn{}:
      W.put_nat(1n, rest)
    case Dc.RemoveWarn{}:
      W.put_nat(2n, rest)

def put_outcome(o: Dc.Outcome) -> String:
  match o:
    case Dc.Lands{w}:
      W.put_nat(0n, put_warn(w, ""))
    case Dc.Fails{}:
      W.put_nat(1n, "")

def put_note(n: Dc.Note, rest: String) -> String:
  match n:
    case Dc.Untouched{}:
      W.put_nat(0n, rest)
    case Dc.Written{}:
      W.put_nat(1n, rest)
    case Dc.Unwritten{}:
      W.put_nat(2n, rest)
    case Dc.Skipped{at}:
      W.put_nat(3n, W.put_nat(at, rest))

def put_verdict(v: Dc.Verdict) -> String:
  match v:
    case Dc.Failure{}:
      W.put_nat(0n, "")
    case Dc.Summary{ns, p}:
      W.put_nat(1n, W.put_list(~Dc.Note, ~put_note, ns, W.put_bool(p, "")))

def gate.tag(g: Dc.Gate) -> Nat:
  match g:
    case Dc.Proceed{}:
      0n
    case Dc.Unseen{}:
      1n
    case Dc.Stale{}:
      2n

# the reply of a request: the model's choice, encoded
def answer(q: Req) -> String:
  match q:
    case QCheck{ms}:
      put_check(Dc.check(ms))
    case QPublish{p}:
      put_outcome(Dc.outcome(p))
    case QAnswer{fs}:
      put_verdict(Dc.answer(fs))
    case QGate{b, d}:
      W.put_nat(gate.tag(Dc.gate(b, d)), "")
    case QSeen{d, xs}:
      W.put_list(~String, ~W.put_str, Dc.seen(d, xs), "")
    case QPrefix{h}:
      W.put_str(Dc.prefix(h), "")
    case QSweep{h, es}:
      W.put_list(~Nat, ~W.put_nat, Dc.gone(h, es), "")

def ffi.done(q: Req, end: Bool) -> String:
  match end:
    case True{}:
      answer(q)
    case False{}:
      W.err("doc_commit: malformed request")

def ffi.got(r: W.Dec<Req>) -> String:
  match r:
    case W.Got{q, +s}:
      ffi.done(q, W.end(s))
    case W.Bad{}:
      W.err("doc_commit: malformed request")

# the entry: decode the request, answer the model's choice
def ffi(input: String) -> String:
  ffi.got(get_req(input))
