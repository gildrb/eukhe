# ffi_tools: the entry of the compiled Bend core for an internal URL's
# path (bend/tools.bend section 3 `resolve`; crates/eukhe-docs/src/url.rs
# `walk`). The request is the path's segments (Rust splits at `/`; a name
# is the index of its segment), each a code: 0 Up (`..`), 1 Here (`.` or
# empty), 2 + n Name{n}. The reply is the names the path reaches, deepest
# first, or none when it goes above its root. The wire format is
# bend/wire.bend; malformed input answers the error form.
#
#   request  List<Nat>                         (the segment codes)
#   reply    0 (above the root) | 1 then List<Nat> (the names, deepest first)

import Base
import ./wire.bend as W
import ./tools.bend as Tl

def code(g: Tl.Seg) -> Nat:
  match g:
    case Tl.Up{}:
      0n
    case Tl.Here{}:
      1n
    case Tl.Name{n}:
      2n+n

def codes(segs: List<&2, Tl.Seg>) -> List<&2, Nat>:
  match segs:
    case Nil{}:
      Nil{}
    case g <> rest:
      code(g) <> codes(rest)

def seg(c: Nat) -> Tl.Seg:
  match c:
    case 0n:
      Tl.Up{}
    case 1n+a:
      match a:
        case 0n:
          Tl.Here{}
        case 1n+n:
          Tl.Name{n}

def segs(cs: List<&2, Nat>) -> List<&2, Tl.Seg>:
  match cs:
    case Nil{}:
      Nil{}
    case c <> rest:
      seg(c) <> segs(rest)

def put_req(gs: List<&2, Tl.Seg>, rest: String) -> String:
  W.put_list(~Nat, ~W.put_nat, codes(gs), rest)

def get_req.of(r: W.Dec<List<&2, Nat>>) -> W.Dec<List<&2, Tl.Seg>>:
  match r:
    case W.Got{cs, s}:
      W.Got{segs(cs), s}
    case W.Bad{}:
      W.Bad{}

def get_req(s: String) -> W.Dec<List<&2, Tl.Seg>>:
  get_req.of(W.get_list(~Nat, ~W.get_nat, s))

def put_names(m: Maybe<&2, List<&2, Nat>>, rest: String) -> String:
  match m:
    case None{}:
      W.put_nat(0n, rest)
    case Some{xs}:
      W.put_nat(1n, W.put_list(~Nat, ~W.put_nat, xs, rest))

# the reply to a request read whole (done: nothing is left)
def reply(done: Bool, gs: List<&2, Tl.Seg>) -> String:
  match done:
    case True{}:
      put_names(Tl.resolve(gs), "")
    case False{}:
      W.err("tools: input left over")

def answer(r: W.Dec<List<&2, Tl.Seg>>) -> String:
  match r:
    case W.Got{gs, s}:
      reply(W.end(s), gs)
    case W.Bad{}:
      W.err("tools: malformed request")

def ffi(input: String) -> String:
  answer(get_req(input))
