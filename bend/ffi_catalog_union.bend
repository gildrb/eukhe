# ffi_catalog_union: the entry of the compiled Bend core for the built-in
# model catalog (bend/catalog_union.bend `fast`, which law union_fast pins
# to `union`; crates/eukhe-models/src/effective.rs `effective_catalog`).
# The request is the two sources projected by Rust (key and api interned,
# data the entry's place, each optional field the place it comes from when
# stated); the reply is the union. An entry crosses as seven Nats: key,
# api, data, then each optional field (0 none, 1 + v the value v). The
# wire format is bend/wire.bend; malformed input answers the error form.
#
#   request  List<Nat> List<Nat>      (the bundle, the compiled catalog)
#   reply    List<Nat>                (the union)

import Base
import ./wire.bend as W
import ./catalog_union.bend as CU

def opt(m: Maybe<&2, Nat>) -> Nat:
  match m:
    case None{}:
      0n
    case Some{v}:
      1n+v

def opt.of(n: Nat) -> Maybe<&2, Nat>:
  match n:
    case 0n:
      None{}
    case 1n+v:
      Some{v}

# the entries of es, seven Nats each, then rest
def ents(es: List<&2, CU.Ent>) -> List<&2, Nat>:
  match es:
    case Nil{}:
      Nil{}
    case CU.Ent{k, a, d, t, c, f, h} <> rest:
      k <> a <> d <> opt(t) <> opt(c) <> opt(f) <> opt(h) <> ents(rest)

def ents.cons(e: CU.Ent, m: Maybe<&2, List<&2, CU.Ent>>) -> Maybe<&2, List<&2, CU.Ent>>:
  match m:
    case None{}:
      None{}
    case Some{es}:
      Some{e <> es}

# the entries ns spells, or none when its length is not a multiple of 7
def ents.of(ns: List<&2, Nat>) -> Maybe<&2, List<&2, CU.Ent>>:
  match ns:
    case Nil{}:
      Some{Nil{}}
    case k <> n1:
      match n1:
        case Nil{}:
          None{}
        case a <> n2:
          match n2:
            case Nil{}:
              None{}
            case d <> n3:
              match n3:
                case Nil{}:
                  None{}
                case t <> n4:
                  match n4:
                    case Nil{}:
                      None{}
                    case c <> n5:
                      match n5:
                        case Nil{}:
                          None{}
                        case f <> n6:
                          match n6:
                            case Nil{}:
                              None{}
                            case h <> rest:
                              ents.cons(CU.Ent{k, a, d, opt.of(t), opt.of(c), opt.of(f), opt.of(h)}, ents.of(rest))

def put_ns(xs: List<&2, Nat>, rest: String) -> String:
  W.put_list(~Nat, ~W.put_nat, xs, rest)

type Req is Data:
  Req{bundled: List<&2, CU.Ent>, compiled: List<&2, CU.Ent>}

def put_req(q: Req, rest: String) -> String:
  match q:
    case Req{b, c}:
      put_ns(ents(b), put_ns(ents(c), rest))

def get_req.both(mb: Maybe<&2, List<&2, CU.Ent>>, mc: Maybe<&2, List<&2, CU.Ent>>, s: String) -> W.Dec<Req>:
  match mb mc:
    case Some{b} Some{c}:
      W.Got{Req{b, c}, s}
    case Some{b} None{}:
      W.Bad{}
    case None{} Some{c}:
      W.Bad{}
    case None{} None{}:
      W.Bad{}

def get_req.c(b: List<&2, Nat>, r: W.Dec<List<&2, Nat>>) -> W.Dec<Req>:
  match r:
    case W.Got{c, s}:
      get_req.both(ents.of(b), ents.of(c), s)
    case W.Bad{}:
      W.Bad{}

def get_req.b(r: W.Dec<List<&2, Nat>>) -> W.Dec<Req>:
  match r:
    case W.Got{b, s}:
      get_req.c(b, W.get_list(~Nat, ~W.get_nat, s))
    case W.Bad{}:
      W.Bad{}

def get_req(s: String) -> W.Dec<Req>:
  get_req.b(W.get_list(~Nat, ~W.get_nat, s))

# the reply to a request read whole (done: nothing is left)
def reply(done: Bool, q: Req) -> String:
  match done:
    case True{}:
      match q:
        case Req{b, c}:
          put_ns(ents(CU.fast(b, c)), "")
    case False{}:
      W.err("catalog_union: input left over")

def answer(r: W.Dec<Req>) -> String:
  match r:
    case W.Got{q, s}:
      reply(W.end(s), q)
    case W.Bad{}:
      W.err("catalog_union: malformed request")

def ffi(input: String) -> String:
  answer(get_req(input))
