# ffi_infer: the entry of the compiled Bend core for the strict schema
# plan of a request (bend/infer.bend section 3, `plan`; crates/eukhe-ai
# `api/constrained_sampling.rs`). One request, one reply, in the wire
# format of bend/wire.bend:
#
#   request (a record)                                reply (a constructor)
#   (cap: Maybe<Nat>, tools: List<Tool>,              0 Fits{loose: List<Nat>}
#    need: List<Nat>)                                 1 Over{id: Nat}
#
# A tool is the record (id: Nat, prio: Nat); need holds the ids of the
# tools that require a strict schema. A malformed request, or one with
# input left over, answers the error form. Pure: no IO, no @unsafe, no
# foreign effect.

import Base
import ./wire.bend as W
import ./infer.bend as If

# Decoding
# --------

# two decoded values, in order
type P2<-A: Data, -B: Data> is Data:
  P2{fst: A, snd: B}

# the value of d paired with the next value, read by get from d's rest
def seq.fin(~A: Data, ~B: Data, a: A, d: W.Dec<B>) -> W.Dec<P2<A, B>>:
  match d:
    case W.Got{b, r}:
      W.Got{P2{a, b}, r}
    case W.Bad{}:
      W.Bad{}

def seq(~A: Data, ~B: Data, ~get: String -> W.Dec<B>, d: W.Dec<A>) -> W.Dec<P2<A, B>>:
  match d:
    case W.Got{a, r}:
      seq.fin(~A, ~B, a, get(r))
    case W.Bad{}:
      W.Bad{}

# a Maybe<Nat>: 0 None, 1 then the Nat
def get_mnat.some(d: W.Dec<Nat>) -> W.Dec<Maybe<&2, Nat>>:
  match d:
    case W.Got{n, r}:
      W.Got{Some{n}, r}
    case W.Bad{}:
      W.Bad{}

def get_mnat.tag(t: Nat, s: String) -> W.Dec<Maybe<&2, Nat>>:
  match t:
    case 0n:
      W.Got{None{}, s}
    case 1n+p:
      match p:
        case 0n:
          get_mnat.some(W.get_nat(s))
        case 1n+q:
          W.Bad{}

def get_mnat.go(d: W.Dec<Nat>) -> W.Dec<Maybe<&2, Nat>>:
  match d:
    case W.Got{t, r}:
      get_mnat.tag(t, r)
    case W.Bad{}:
      W.Bad{}

def get_mnat(s: String) -> W.Dec<Maybe<&2, Nat>>:
  get_mnat.go(W.get_nat(s))

# a tool: its id, then its priority
def get_tool.of(d: W.Dec<P2<Nat, Nat>>) -> W.Dec<If.Tool>:
  match d:
    case W.Got{q, r}:
      P2{i, p} = q
      W.Got{If.Tool{i, p}, r}
    case W.Bad{}:
      W.Bad{}

def get_tool(s: String) -> W.Dec<If.Tool>:
  get_tool.of(seq(~Nat, ~Nat, ~W.get_nat, W.get_nat(s)))

def get_tools(s: String) -> W.Dec<List<&2, If.Tool>>:
  W.get_list(~If.Tool, ~get_tool, s)

def get_ids(s: String) -> W.Dec<List<&2, Nat>>:
  W.get_list(~Nat, ~W.get_nat, s)

# Requests
# --------

type Req is Data:
  Req{cap: Maybe<&2, Nat>, tools: List<&2, If.Tool>, need: List<&2, Nat>}

def get_req.of(d: W.Dec<P2<P2<Maybe<&2, Nat>, List<&2, If.Tool>>, List<&2, Nat>>>) -> W.Dec<Req>:
  match d:
    case W.Got{q, r}:
      P2{q2, need} = q
      P2{cap, ts} = q2
      W.Got{Req{cap, ts, need}, r}
    case W.Bad{}:
      W.Bad{}

# a request
def get_req(s: String) -> W.Dec<Req>:
  get_req.of(seq(~P2<Maybe<&2, Nat>, List<&2, If.Tool>>, ~List<&2, Nat>, ~get_ids, seq(~Maybe<&2, Nat>, ~List<&2, If.Tool>, ~get_tools, get_mnat(s))))

# Encoding
# --------
# The request as Rust's `Writer` spells it (`api/constrained_sampling.rs`):
# the inverse of get_req, used by the laws (LAWS.bend `core entries`).

def put_mnat(m: Maybe<&2, Nat>, rest: String) -> String:
  match m:
    case None{}:
      W.put_nat(0n, rest)
    case Some{n}:
      W.put_nat(1n, W.put_nat(n, rest))

def put_tool(t: If.Tool, rest: String) -> String:
  match t:
    case If.Tool{i, p}:
      W.put_nat(i, W.put_nat(p, rest))

def put_req(q: Req, rest: String) -> String:
  match q:
    case Req{cap, ts, need}:
      put_mnat(cap, W.put_list(~If.Tool, ~put_tool, ts, W.put_list(~Nat, ~W.put_nat, need, rest)))

# Replies
# -------

def put_plan(p: If.Plan, rest: String) -> String:
  match p:
    case If.Fits{ls}:
      W.put_nat(0n, W.put_list(~Nat, ~W.put_nat, ls, rest))
    case If.Over{i}:
      W.put_nat(1n, W.put_nat(i, rest))

# the reply to a request
def answer(q: Req) -> String:
  match q:
    case Req{cap, +ts, +need}:
      put_plan(If.plan(cap, ts, need), "")

# whole is W.end(rest): nothing is left after the request
def ffi.done(whole: Bool, q: Req) -> String:
  match whole:
    case True{}:
      answer(q)
    case False{}:
      W.err("strict plan request: input left over")

def ffi.go(d: W.Dec<Req>) -> String:
  match d:
    case W.Got{q, r}:
      ffi.done(W.end(r), q)
    case W.Bad{}:
      W.err("strict plan request: malformed")

# the entry: decode the request, answer it
def ffi(input: String) -> String:
  ffi.go(get_req(input))
