# ffi_director: the entry of the Director stack (bend/director.bend) in
# the compiled Bend core. Rust (crates/eukhe-core/src/durable/directors)
# sends one loop step and reads the loop after it.
#
# Request (crates/eukhe-bend/WIRE.md): a record
#   cap: Nat, loop: Loop, verdicts: List<Verdict>
# with
#   Layer   = a record (kind: Nat, budget: Nat)
#   Verdict = tag 0 Defer | 1 Again | 2 Yield | 3 Stack (Layer) | 4 Leave
#             | 5 Abort | 6 Lead
#   Out     = tag 0 Cont | 1 Hand | 2 Failed
#   Loop    = a record (left: Nat, stack: List<Layer> top first,
#             end: Maybe<Out>)
# Reply: the Loop after D.tick(cap, loop, verdicts).

import Base
import ./wire.bend as W
import ./director.bend as D

# Layers
# ------

def put_layer(l: D.Layer, rest: String) -> String:
  match l:
    case D.Layer{k, b}:
      W.put_nat(k, W.put_nat(b, rest))

def get_layer.b(k: Nat, r: W.Dec<Nat>) -> W.Dec<D.Layer>:
  match r:
    case W.Got{b, s}:
      W.Got{D.Layer{k, b}, s}
    case W.Bad{}:
      W.Bad{}

def get_layer.k(r: W.Dec<Nat>) -> W.Dec<D.Layer>:
  match r:
    case W.Got{k, s}:
      get_layer.b(k, W.get_nat(s))
    case W.Bad{}:
      W.Bad{}

def get_layer(s: String) -> W.Dec<D.Layer>:
  get_layer.k(W.get_nat(s))

# Verdicts
# --------

def put_verdict(v: D.Verdict, rest: String) -> String:
  match v:
    case D.Defer{}:
      W.put_nat(0n, rest)
    case D.Again{}:
      W.put_nat(1n, rest)
    case D.Yield{}:
      W.put_nat(2n, rest)
    case D.Stack{l}:
      W.put_nat(3n, put_layer(l, rest))
    case D.Leave{}:
      W.put_nat(4n, rest)
    case D.Abort{}:
      W.put_nat(5n, rest)
    case D.Lead{}:
      W.put_nat(6n, rest)

def get_verdict.stack(r: W.Dec<D.Layer>) -> W.Dec<D.Verdict>:
  match r:
    case W.Got{l, s}:
      W.Got{D.Stack{l}, s}
    case W.Bad{}:
      W.Bad{}

def get_verdict.tag(t: Nat, s: String) -> W.Dec<D.Verdict>:
  match t:
    case 0n:
      W.Got{D.Defer{}, s}
    case 1n:
      W.Got{D.Again{}, s}
    case 2n:
      W.Got{D.Yield{}, s}
    case 3n:
      get_verdict.stack(get_layer(s))
    case 4n:
      W.Got{D.Leave{}, s}
    case 5n:
      W.Got{D.Abort{}, s}
    case 6n:
      W.Got{D.Lead{}, s}
    case 7n+x:
      W.Bad{}

def get_verdict.go(r: W.Dec<Nat>) -> W.Dec<D.Verdict>:
  match r:
    case W.Got{t, s}:
      get_verdict.tag(t, s)
    case W.Bad{}:
      W.Bad{}

def get_verdict(s: String) -> W.Dec<D.Verdict>:
  get_verdict.go(W.get_nat(s))

# Outcomes
# --------

def put_out(o: D.Out, rest: String) -> String:
  match o:
    case D.Cont{}:
      W.put_nat(0n, rest)
    case D.Hand{}:
      W.put_nat(1n, rest)
    case D.Failed{}:
      W.put_nat(2n, rest)

def put_end(e: Maybe<&2, D.Out>, rest: String) -> String:
  match e:
    case None{}:
      W.put_nat(0n, rest)
    case Some{o}:
      W.put_nat(1n, put_out(o, rest))

def get_end.out(t: Nat, s: String) -> W.Dec<Maybe<&2, D.Out>>:
  match t:
    case 0n:
      W.Got{Some{D.Cont{}}, s}
    case 1n:
      W.Got{Some{D.Hand{}}, s}
    case 2n:
      W.Got{Some{D.Failed{}}, s}
    case 3n+x:
      W.Bad{}

def get_end.some(r: W.Dec<Nat>) -> W.Dec<Maybe<&2, D.Out>>:
  match r:
    case W.Got{t, s}:
      get_end.out(t, s)
    case W.Bad{}:
      W.Bad{}

def get_end.tag(t: Nat, s: String) -> W.Dec<Maybe<&2, D.Out>>:
  match t:
    case 0n:
      W.Got{None{}, s}
    case 1n:
      get_end.some(W.get_nat(s))
    case 2n+x:
      W.Bad{}

def get_end.go(r: W.Dec<Nat>) -> W.Dec<Maybe<&2, D.Out>>:
  match r:
    case W.Got{t, s}:
      get_end.tag(t, s)
    case W.Bad{}:
      W.Bad{}

def get_end(s: String) -> W.Dec<Maybe<&2, D.Out>>:
  get_end.go(W.get_nat(s))

# Loops
# -----

def put_loop(l: D.Loop, rest: String) -> String:
  match l:
    case D.Loop{n, st, e}:
      W.put_nat(n, W.put_list(~D.Layer, ~put_layer, st, put_end(e, rest)))

def get_loop.end(n: Nat, st: List<&2, D.Layer>, r: W.Dec<Maybe<&2, D.Out>>) -> W.Dec<D.Loop>:
  match r:
    case W.Got{e, s}:
      W.Got{D.Loop{n, st, e}, s}
    case W.Bad{}:
      W.Bad{}

def get_loop.stack(n: Nat, r: W.Dec<List<&2, D.Layer>>) -> W.Dec<D.Loop>:
  match r:
    case W.Got{st, s}:
      get_loop.end(n, st, get_end(s))
    case W.Bad{}:
      W.Bad{}

def get_loop.left(r: W.Dec<Nat>) -> W.Dec<D.Loop>:
  match r:
    case W.Got{n, s}:
      get_loop.stack(n, W.get_list(~D.Layer, ~get_layer, s))
    case W.Bad{}:
      W.Bad{}

def get_loop(s: String) -> W.Dec<D.Loop>:
  get_loop.left(W.get_nat(s))

# The request
# -----------

type Req is Data:
  Req{cap: Nat, loop: D.Loop, verdicts: List<&2, D.Verdict>}

def put_req(q: Req, rest: String) -> String:
  match q:
    case Req{c, l, vs}:
      W.put_nat(c, put_loop(l, W.put_list(~D.Verdict, ~put_verdict, vs, rest)))

def get_req.vs(c: Nat, l: D.Loop, r: W.Dec<List<&2, D.Verdict>>) -> W.Dec<Req>:
  match r:
    case W.Got{vs, s}:
      W.Got{Req{c, l, vs}, s}
    case W.Bad{}:
      W.Bad{}

def get_req.loop(c: Nat, r: W.Dec<D.Loop>) -> W.Dec<Req>:
  match r:
    case W.Got{l, s}:
      get_req.vs(c, l, W.get_list(~D.Verdict, ~get_verdict, s))
    case W.Bad{}:
      W.Bad{}

def get_req.cap(r: W.Dec<Nat>) -> W.Dec<Req>:
  match r:
    case W.Got{c, s}:
      get_req.loop(c, get_loop(s))
    case W.Bad{}:
      W.Bad{}

def get_req(s: String) -> W.Dec<Req>:
  get_req.cap(W.get_nat(s))

# The entry
# ---------

def ffi.run(q: Req) -> String:
  match q:
    case Req{c, l, vs}:
      put_loop(D.tick(c, l, vs), "")

def ffi.whole(q: Req, done: Bool) -> String:
  match done:
    case True{}:
      ffi.run(q)
    case False{}:
      W.err("director: input left over")

def ffi.go(r: W.Dec<Req>) -> String:
  match r:
    case W.Got{q, s}:
      ffi.whole(q, W.end(s))
    case W.Bad{}:
      W.err("director: malformed request")

# one loop step: the request in, the loop after it out
def ffi(input: String) -> String:
  ffi.go(get_req(input))
