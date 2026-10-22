# ffi_tiny: the entry of the compiled Bend core for a tiny task's model
# (bend/tiny.bend `pick`; crates/eukhe-tiny/src/roles.rs `pick`). The
# request is the chain and the available models, each interned by Rust
# (a candidate is the index of its first equal one); the reply is the
# pick. The wire format is bend/wire.bend; malformed input answers the
# error form.
#
#   request  Req{chain: List<Nat>, up: List<Nat>}   (a record)
#   reply    Pick: 0 Use{model: Nat} | 1 Unavailable

import Base
import ./wire.bend as W
import ./tiny.bend as Tn

type Req is Data:
  Req{chain: List<&2, Nat>, up: List<&2, Nat>}

def put_ids(xs: List<&2, Nat>, rest: String) -> String:
  W.put_list(~Nat, ~W.put_nat, xs, rest)

def get_ids(s: String) -> W.Dec<List<&2, Nat>>:
  W.get_list(~Nat, ~W.get_nat, s)

def put_req(q: Req, rest: String) -> String:
  match q:
    case Req{c, u}:
      put_ids(c, put_ids(u, rest))

def get_req.up(c: List<&2, Nat>, r: W.Dec<List<&2, Nat>>) -> W.Dec<Req>:
  match r:
    case W.Got{u, s}:
      W.Got{Req{c, u}, s}
    case W.Bad{}:
      W.Bad{}

def get_req.chain(r: W.Dec<List<&2, Nat>>) -> W.Dec<Req>:
  match r:
    case W.Got{c, s}:
      get_req.up(c, get_ids(s))
    case W.Bad{}:
      W.Bad{}

def get_req(s: String) -> W.Dec<Req>:
  get_req.chain(get_ids(s))

def put_pick(p: Tn.Pick, rest: String) -> String:
  match p:
    case Tn.Use{m}:
      W.put_nat(0n, W.put_nat(m, rest))
    case Tn.Unavailable{}:
      W.put_nat(1n, rest)

def get_pick.use(r: W.Dec<Nat>) -> W.Dec<Tn.Pick>:
  match r:
    case W.Got{m, s}:
      W.Got{Tn.Use{m}, s}
    case W.Bad{}:
      W.Bad{}

def get_pick.tag(r: W.Dec<Nat>) -> W.Dec<Tn.Pick>:
  match r:
    case W.Got{t, s}:
      match t:
        case 0n:
          get_pick.use(W.get_nat(s))
        case 1n+u:
          match u:
            case 0n:
              W.Got{Tn.Unavailable{}, s}
            case 1n+v:
              W.Bad{}
    case W.Bad{}:
      W.Bad{}

def get_pick(s: String) -> W.Dec<Tn.Pick>:
  get_pick.tag(W.get_nat(s))

# the reply to a request read whole (done: nothing is left)
def reply(done: Bool, q: Req) -> String:
  match done:
    case True{}:
      match q:
        case Req{c, u}:
          put_pick(Tn.pick(c, u), SNil{})
    case False{}:
      W.err("tiny: input left over")

def answer(r: W.Dec<Req>) -> String:
  match r:
    case W.Got{q, s}:
      reply(W.end(s), q)
    case W.Bad{}:
      W.err("tiny: malformed request")

def ffi(input: String) -> String:
  answer(get_req(input))
