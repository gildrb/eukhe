# ffi_tiny_elect: the entry of the compiled Bend core for one process's
# election of a tiny model's worker (bend/tiny.bend section 3; Rust:
# crates/eukhe-tiny/src/election.rs). Each request names one choice and
# carries what Rust met (crates/eukhe-bend/WIRE.md is the grammar):
#
#   tag 0  elect     a Probe, the process's launch tag (String)
#                    -> Act    0 Join | 1 Replace | 2 Start | 3 Broken
#   tag 1  shut      a Heard   -> Shut   0 Down | 1 Spoke | 2 Cut
#   tag 2  launched  a Fresh, a Launch
#                    -> Got    0 Started | 1 Joined | 2 Replaced
#   tag 3  confirm   a Probe, the process's launch tag
#                    -> Check  0 Serving | 1 Mistagged | 2 Vacant | 3 Faulty
#   tag 4  bind      a Probe (a started worker's own ping)
#                    -> Seat   0 Adopt | 1 Take | 2 Fault
#
#   Probe  0 Missing | 1 Unreachable | 2 Pong{tag: String} | 3 Odd
#          | 4 Garbled | 5 Hung
#   Heard  0 Bye | 1 Other | 2 Eof | 3 Lost
#   Fresh  0 First | 1 Again        Launch  0 Bound | 1 Adopted
#
# Malformed input, or input left after the request, answers the error
# form `E tiny_elect: malformed request`, never a default. Pure: no IO,
# no @unsafe.

import Base
import ./wire.bend as W
import ./tiny.bend as Tn

# A request of the entry
type Req is Data:
  QElect{probe: Tn.Probe, mine: String}
  QShut{heard: Tn.Heard}
  QLaunched{fresh: Tn.Fresh, launch: Tn.Launch}
  QConfirm{probe: Tn.Probe, mine: String}
  QBind{probe: Tn.Probe}

# Requests
# --------

def get_probe.pong(r: W.Dec<String>) -> W.Dec<Tn.Probe>:
  match r:
    case W.Got{t, s}:
      W.Got{Tn.Pong{t}, s}
    case W.Bad{}:
      W.Bad{}

def get_probe.tag(t: Nat, s: String) -> W.Dec<Tn.Probe>:
  match t:
    case 0n:
      W.Got{Tn.Missing{}, s}
    case 1n:
      W.Got{Tn.Unreachable{}, s}
    case 2n:
      get_probe.pong(W.get_str(s))
    case 3n:
      W.Got{Tn.Odd{}, s}
    case 4n:
      W.Got{Tn.Garbled{}, s}
    case 5n:
      W.Got{Tn.Hung{}, s}
    case 6n+u:
      W.Bad{}

def get_probe(r: W.Dec<Nat>) -> W.Dec<Tn.Probe>:
  match r:
    case W.Got{t, s}:
      get_probe.tag(t, s)
    case W.Bad{}:
      W.Bad{}

def get_heard.tag(t: Nat, s: String) -> W.Dec<Tn.Heard>:
  match t:
    case 0n:
      W.Got{Tn.Bye{}, s}
    case 1n:
      W.Got{Tn.Other{}, s}
    case 2n:
      W.Got{Tn.Eof{}, s}
    case 3n:
      W.Got{Tn.Lost{}, s}
    case 4n+u:
      W.Bad{}

def get_heard(r: W.Dec<Nat>) -> W.Dec<Tn.Heard>:
  match r:
    case W.Got{t, s}:
      get_heard.tag(t, s)
    case W.Bad{}:
      W.Bad{}

def get_fresh.tag(t: Nat, s: String) -> W.Dec<Tn.Fresh>:
  match t:
    case 0n:
      W.Got{Tn.First{}, s}
    case 1n:
      W.Got{Tn.Again{}, s}
    case 2n+u:
      W.Bad{}

def get_fresh(r: W.Dec<Nat>) -> W.Dec<Tn.Fresh>:
  match r:
    case W.Got{t, s}:
      get_fresh.tag(t, s)
    case W.Bad{}:
      W.Bad{}

def get_launch.tag(t: Nat, s: String) -> W.Dec<Tn.Launch>:
  match t:
    case 0n:
      W.Got{Tn.Bound{}, s}
    case 1n:
      W.Got{Tn.Adopted{}, s}
    case 2n+u:
      W.Bad{}

def get_launch(r: W.Dec<Nat>) -> W.Dec<Tn.Launch>:
  match r:
    case W.Got{t, s}:
      get_launch.tag(t, s)
    case W.Bad{}:
      W.Bad{}

# a probe and a tag: elect (c = True) or confirm (c = False)
def pm.make(c: Bool, p: Tn.Probe, m: String) -> Req:
  match c:
    case True{}:
      QElect{p, m}
    case False{}:
      QConfirm{p, m}

def get_pm.mine(c: Bool, p: Tn.Probe, r: W.Dec<String>) -> W.Dec<Req>:
  match r:
    case W.Got{m, s}:
      W.Got{pm.make(c, p, m), s}
    case W.Bad{}:
      W.Bad{}

def get_pm(c: Bool, r: W.Dec<Tn.Probe>) -> W.Dec<Req>:
  match r:
    case W.Got{p, s}:
      get_pm.mine(c, p, W.get_str(s))
    case W.Bad{}:
      W.Bad{}

def get_shut(r: W.Dec<Tn.Heard>) -> W.Dec<Req>:
  match r:
    case W.Got{h, s}:
      W.Got{QShut{h}, s}
    case W.Bad{}:
      W.Bad{}

def get_launched.launch(f: Tn.Fresh, r: W.Dec<Tn.Launch>) -> W.Dec<Req>:
  match r:
    case W.Got{l, s}:
      W.Got{QLaunched{f, l}, s}
    case W.Bad{}:
      W.Bad{}

def get_launched(r: W.Dec<Tn.Fresh>) -> W.Dec<Req>:
  match r:
    case W.Got{f, s}:
      get_launched.launch(f, get_launch(W.get_nat(s)))
    case W.Bad{}:
      W.Bad{}

def get_bind(r: W.Dec<Tn.Probe>) -> W.Dec<Req>:
  match r:
    case W.Got{p, s}:
      W.Got{QBind{p}, s}
    case W.Bad{}:
      W.Bad{}

def get_req.tag(t: Nat, s: String) -> W.Dec<Req>:
  match t:
    case 0n:
      get_pm(True{}, get_probe(W.get_nat(s)))
    case 1n:
      get_shut(get_heard(W.get_nat(s)))
    case 2n:
      get_launched(get_fresh(W.get_nat(s)))
    case 3n:
      get_pm(False{}, get_probe(W.get_nat(s)))
    case 4n:
      get_bind(get_probe(W.get_nat(s)))
    case 5n+u:
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

def act.tag(a: Tn.Act) -> Nat:
  match a:
    case Tn.Join{}:
      0n
    case Tn.Replace{}:
      1n
    case Tn.Start{}:
      2n
    case Tn.Broken{}:
      3n

def shut.tag(x: Tn.Shut) -> Nat:
  match x:
    case Tn.Down{}:
      0n
    case Tn.Spoke{}:
      1n
    case Tn.Cut{}:
      2n

def got.tag(g: Tn.Got) -> Nat:
  match g:
    case Tn.Started{}:
      0n
    case Tn.Joined{}:
      1n
    case Tn.Replaced{}:
      2n

def check.tag(c: Tn.Check) -> Nat:
  match c:
    case Tn.Serving{}:
      0n
    case Tn.Mistagged{}:
      1n
    case Tn.Vacant{}:
      2n
    case Tn.Faulty{}:
      3n

def seat.tag(x: Tn.Seat) -> Nat:
  match x:
    case Tn.Adopt{}:
      0n
    case Tn.Take{}:
      1n
    case Tn.Fault{}:
      2n

# the reply of a request: the model's choice, encoded
def answer(q: Req) -> String:
  match q:
    case QElect{p, m}:
      W.put_nat(act.tag(Tn.elect(p, m)), "")
    case QShut{h}:
      W.put_nat(shut.tag(Tn.shut(h)), "")
    case QLaunched{f, l}:
      W.put_nat(got.tag(Tn.launched(f, l)), "")
    case QConfirm{p, m}:
      W.put_nat(check.tag(Tn.confirm(p, m)), "")
    case QBind{p}:
      W.put_nat(seat.tag(Tn.bind(p)), "")

def ffi.done(q: Req, end: Bool) -> String:
  match end:
    case True{}:
      answer(q)
    case False{}:
      W.err("tiny_elect: malformed request")

def ffi.got(r: W.Dec<Req>) -> String:
  match r:
    case W.Got{q, +s}:
      ffi.done(q, W.end(s))
    case W.Bad{}:
      W.err("tiny_elect: malformed request")

# the entry: decode the request, answer the model's choice
def ffi(input: String) -> String:
  ffi.got(get_req(input))
