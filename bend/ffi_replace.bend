# ffi_replace: the compiled core's entry for the launcher's replacement
# verdict (bend/replace.bend), called by crates/eukhe-tui
# (`daemon_build.rs`: `relation`, `replacement_verdict`). The wire format
# is bend/wire.bend (crates/eukhe-bend/WIRE.md).
#
# A request is one constructor:
#   0 Relation{client, daemon, same}         answers the Rel tag
#   1 Verdict{client, daemon, same, caller}  answers the Verdict
# client and daemon are the versions (the hello `appVersion`; Rust sends
# the first 65 chars, which decide the rank: law replace_rank_cut); same
# says whether the build ids are equal: the model reads the ids only
# through that equality (laws replace_ffi_relation, replace_ffi_verdict).
# Rel tags: 0 Same, 1 Older, 2 Newer, 3 Other. Verdict: tag 0 Replace, or
# tag 1 Keep then the Rel tag. Caller tags: 0 Interactive, 1 Background.
# A malformed request (or input left over) answers the error form, never
# a default.

import Base
import ./wire.bend as W
import ./replace.bend as Rp

type Req is Data:
  ReqRelation{client: String, daemon: String, same: Bool}
  ReqVerdict{client: String, daemon: String, same: Bool, caller: Rp.Caller}

# Encoders
# --------

def put_caller(k: Rp.Caller, rest: String) -> String:
  match k:
    case Rp.Interactive{}:
      W.put_nat(0n, rest)
    case Rp.Background{}:
      W.put_nat(1n, rest)

def put_rel(r: Rp.Rel, rest: String) -> String:
  match r:
    case Rp.Same{}:
      W.put_nat(0n, rest)
    case Rp.Older{}:
      W.put_nat(1n, rest)
    case Rp.Newer{}:
      W.put_nat(2n, rest)
    case Rp.Other{}:
      W.put_nat(3n, rest)

def put_verdict(v: Rp.Verdict, rest: String) -> String:
  match v:
    case Rp.Replace{}:
      W.put_nat(0n, rest)
    case Rp.Keep{r}:
      W.put_nat(1n, put_rel(r, rest))

# the encoding of a request (what Rust writes)
def put_req(q: Req, rest: String) -> String:
  match q:
    case ReqRelation{c, d, same}:
      W.put_nat(0n, W.put_str(c, W.put_str(d, W.put_bool(same, rest))))
    case ReqVerdict{c, d, same, k}:
      W.put_nat(1n, W.put_str(c, W.put_str(d, W.put_bool(same, put_caller(k, rest)))))

# Decoders
# --------

def get_caller.tag(n: Nat, s: String) -> W.Dec<Rp.Caller>:
  match n:
    case 0n:
      W.Got{Rp.Interactive{}, s}
    case 1n+a:
      match a:
        case 0n:
          W.Got{Rp.Background{}, s}
        case 1n+b:
          W.Bad{}

def get_caller.of(r: W.Dec<Nat>) -> W.Dec<Rp.Caller>:
  match r:
    case W.Got{n, s}:
      get_caller.tag(n, s)
    case W.Bad{}:
      W.Bad{}

def get_caller(s: String) -> W.Dec<Rp.Caller>:
  get_caller.of(W.get_nat(s))

def get_relation.same(c: String, d: String, r: W.Dec<Bool>) -> W.Dec<Req>:
  match r:
    case W.Got{same, s}:
      W.Got{ReqRelation{c, d, same}, s}
    case W.Bad{}:
      W.Bad{}

def get_relation.d(c: String, r: W.Dec<String>) -> W.Dec<Req>:
  match r:
    case W.Got{d, s}:
      get_relation.same(c, d, W.get_bool(s))
    case W.Bad{}:
      W.Bad{}

def get_relation(r: W.Dec<String>) -> W.Dec<Req>:
  match r:
    case W.Got{c, s}:
      get_relation.d(c, W.get_str(s))
    case W.Bad{}:
      W.Bad{}

def get_verdict.k(c: String, d: String, same: Bool, r: W.Dec<Rp.Caller>) -> W.Dec<Req>:
  match r:
    case W.Got{k, s}:
      W.Got{ReqVerdict{c, d, same, k}, s}
    case W.Bad{}:
      W.Bad{}

def get_verdict.same(c: String, d: String, r: W.Dec<Bool>) -> W.Dec<Req>:
  match r:
    case W.Got{same, s}:
      get_verdict.k(c, d, same, get_caller(s))
    case W.Bad{}:
      W.Bad{}

def get_verdict.d(c: String, r: W.Dec<String>) -> W.Dec<Req>:
  match r:
    case W.Got{d, s}:
      get_verdict.same(c, d, W.get_bool(s))
    case W.Bad{}:
      W.Bad{}

def get_verdict(r: W.Dec<String>) -> W.Dec<Req>:
  match r:
    case W.Got{c, s}:
      get_verdict.d(c, W.get_str(s))
    case W.Bad{}:
      W.Bad{}

def get_req.tag(n: Nat, s: String) -> W.Dec<Req>:
  match n:
    case 0n:
      get_relation(W.get_str(s))
    case 1n+a:
      match a:
        case 0n:
          get_verdict(W.get_str(s))
        case 1n+b:
          W.Bad{}

def get_req.of(r: W.Dec<Nat>) -> W.Dec<Req>:
  match r:
    case W.Got{n, s}:
      get_req.tag(n, s)
    case W.Bad{}:
      W.Bad{}

# the request at the head of s (what the entry reads)
def get_req(s: String) -> W.Dec<Req>:
  get_req.of(W.get_nat(s))

# The entry
# ---------

# the relation of a daemon of version d to a client of version c, with
# equal build ids exactly when same (Rp.relation reads the ids only so)
def relation(+c: String, +d: String, same: Bool) -> Rp.Rel:
  +rc = Rp.rank(c)
  +rd = Rp.rank(d)
  Rp.rel.put(same, Rp.lt(rd, rc), Rp.lt(rc, rd))

# the model's answer to a request, encoded
def answer(q: Req) -> String:
  match q:
    case ReqRelation{c, d, same}:
      put_rel(relation(c, d, same), SNil{})
    case ReqVerdict{c, d, same, k}:
      put_verdict(Rp.verdict.put(relation(c, d, same), k), SNil{})

def ffi.whole(q: Req, whole: Bool) -> String:
  match whole:
    case True{}:
      answer(q)
    case False{}:
      W.err("replace: input left over")

def ffi.of(r: W.Dec<Req>) -> String:
  match r:
    case W.Got{q, s}:
      ffi.whole(q, W.end(s))
    case W.Bad{}:
      W.err("replace: malformed request")

def ffi(input: String) -> String:
  ffi.of(get_req(input))
