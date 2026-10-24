# ffi_log: the rules of the commit log of JsonlStorage (bend/log.bend)
# behind the compiled Bend core (crates/eukhe-bend/WIRE.md is the grammar):
#
#   ffi    the open of a file: its length (Nat), then its last
#          newline (Maybe<Nat>: 0 none | 1 the index)      -> a Tail
#   open   the storage's stepper: fsync (Bool)            -> the open's acts
#   step   a commit: the durability of the directory entries
#          of its sidecar files, in order (List<Bool>)     -> the commit's acts
#
# A Tail is 0 (whole), 1 then the length to cut to (torn), or 2 (odd). An
# act is its tag in declaration order (FlushParent 0 .. Ack 6), then the
# sidecar's index for AppendSide (1) and FlushSide (2); a plan answers its
# acts as a list. Malformed input answers the wire's error form, never a
# default; a step with malformed input keeps the state. laws/log.bend
# states the laws of this entry; PROOF.bend proves them. Pure: no IO, no
# @unsafe.

import Base
import ./wire.bend as W
import ./log.bend as M

# The open of a file
# ------------------

# a request: the file's length and its last newline
type Req is Data:
  Req{len: Nat, last: Maybe<&2, Nat>}

def put_tail(t: M.Tail, rest: String) -> String:
  match t:
    case M.Whole{}:
      W.put_nat(0n, rest)
    case M.Torn{to}:
      W.put_nat(1n, W.put_nat(to, rest))
    case M.Odd{}:
      W.put_nat(2n, rest)

def get_last.some(r: W.Dec<Nat>) -> W.Dec<Maybe<&2, Nat>>:
  match r:
    case W.Got{n, s}:
      W.Got{Some{n}, s}
    case W.Bad{}:
      W.Bad{}

def get_last.tag(r: W.Dec<Nat>) -> W.Dec<Maybe<&2, Nat>>:
  match r:
    case W.Got{t, s}:
      match t:
        case 0n:
          W.Got{None{}, s}
        case 1n:
          get_last.some(W.get_nat(s))
        case 2n+k:
          W.Bad{}
    case W.Bad{}:
      W.Bad{}

def get_last(s: String) -> W.Dec<Maybe<&2, Nat>>:
  get_last.tag(W.get_nat(s))

def get_req.last(len: Nat, r: W.Dec<Maybe<&2, Nat>>) -> W.Dec<Req>:
  match r:
    case W.Got{m, s}:
      W.Got{Req{len, m}, s}
    case W.Bad{}:
      W.Bad{}

def get_req.len(r: W.Dec<Nat>) -> W.Dec<Req>:
  match r:
    case W.Got{n, s}:
      get_req.last(n, get_last(s))
    case W.Bad{}:
      W.Bad{}

def get_req(s: String) -> W.Dec<Req>:
  get_req.len(W.get_nat(s))

def ffi.end(done: Bool, q: Req) -> String:
  match done:
    case True{}:
      match q:
        case Req{len, last}:
          put_tail(M.tail(len, last), "")
    case False{}:
      W.err("log: input left over")

def ffi.go(r: W.Dec<Req>) -> String:
  match r:
    case W.Got{q, s}:
      ffi.end(W.end(s), q)
    case W.Bad{}:
      W.err("log: malformed request")

# the open of a file: its facts in, what the open does with it out
def ffi(input: String) -> String:
  ffi.go(get_req(input))

# The plan
# --------

def put_act(a: M.Act, rest: String) -> String:
  match a:
    case M.FlushParent{}:
      W.put_nat(0n, rest)
    case M.AppendSide{i}:
      W.put_nat(1n, W.put_nat(i, rest))
    case M.FlushSide{i}:
      W.put_nat(2n, W.put_nat(i, rest))
    case M.FlushDir{}:
      W.put_nat(3n, rest)
    case M.AppendMain{}:
      W.put_nat(4n, rest)
    case M.FlushMain{}:
      W.put_nat(5n, rest)
    case M.Ack{}:
      W.put_nat(6n, rest)

# the stepper's state: the storage, or a refused open
type St is Data:
  Running{s: M.Store}
  Shut{}

# a plan's storage and its acts
def reply(p: M.Plan) -> St & String:
  match p:
    case M.Plan{s, acts}:
      (Running{s}, W.put_list(~M.Act, ~put_act, acts, ""))

def open.end(done: Bool, fsync: Bool) -> St & String:
  match done:
    case True{}:
      reply(M.Store.open(fsync))
    case False{}:
      (Shut{}, W.err("log: input left over"))

def open.go(r: W.Dec<Bool>) -> St & String:
  match r:
    case W.Got{b, s}:
      open.end(W.end(s), b)
    case W.Bad{}:
      (Shut{}, W.err("log: malformed open"))

# open: fsync in; the storage and the open's acts out
def open(input: String) -> St & String:
  open.go(W.get_bool(input))

def step.end(done: Bool, s: M.Store, ds: List<&2, Bool>) -> St & String:
  match done:
    case True{}:
      reply(M.Store.commit(s, ds))
    case False{}:
      (Running{s}, W.err("log: input left over"))

def step.go(s: M.Store, r: W.Dec<List<&2, Bool>>) -> St & String:
  match r:
    case W.Got{ds, rest}:
      step.end(W.end(rest), s, ds)
    case W.Bad{}:
      (Running{s}, W.err("log: malformed commit"))

# step: a commit's sidecar entries in; the storage after it and the
# commit's acts out
def step(st: St, input: String) -> St & String:
  match st:
    case Running{s}:
      step.go(s, W.get_list(~Bool, ~W.get_bool, input))
    case Shut{}:
      (Shut{}, W.err("log: the open was refused"))
