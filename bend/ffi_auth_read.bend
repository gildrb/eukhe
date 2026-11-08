# ffi_auth_read: the compiled Bend core's entry for the judgments of the
# OAuth refresh on what a read of the auth document found
# (bend/auth_flight.bend section The reads the Rust judges). Rust
# `auth::flight` calls it at the load, the leader's check and the store
# of a refresh, and the auth lookup before it starts one.
#
# Call (crates/eukhe-bend/WIRE.md): a tag, what the read is for: 0 the
# load, 1 the leader's check, 2 the store; the clock (ms since the epoch,
# a Nat); what the read found: a tag, 0 the document could not be read, 1
# no credential, 2 a credential that is not OAuth, 3 an OAuth credential
# (then its expiry, ms since the epoch, a Nat).
# Reply: a tag, the verdict: 0 serve, 1 refresh, 2 refuse, 3 keep the
# peer's credential, 4 write the fetched one.
#
# Malformed input answers the error form "auth_read: malformed request".

import Base
import ./wire.bend as W
import ./auth_flight.bend as M

def get_read.oauth(r: W.Dec<Nat>) -> W.Dec<M.Read>:
  match r:
    case W.Got{e, s}:
      W.Got{M.Oauth{e}, s}
    case W.Bad{}:
      W.Bad{}

def get_read.tag(t: Nat, s: String) -> W.Dec<M.Read>:
  match t:
    case 0n:
      W.Got{M.Unread{}, s}
    case 1n:
      W.Got{M.NoCred{}, s}
    case 2n:
      W.Got{M.NotOauth{}, s}
    case 3n:
      get_read.oauth(W.get_nat(s))
    case 4n+p:
      W.Bad{}

def get_read(r: W.Dec<Nat>) -> W.Dec<M.Read>:
  match r:
    case W.Got{t, s}:
      get_read.tag(t, s)
    case W.Bad{}:
      W.Bad{}

def get_query.read(a: M.Ask, now: Nat, r: W.Dec<M.Read>) -> W.Dec<M.Query>:
  match r:
    case W.Got{x, s}:
      W.Got{M.Query{a, now, x}, s}
    case W.Bad{}:
      W.Bad{}

def get_query.now(a: M.Ask, r: W.Dec<Nat>) -> W.Dec<M.Query>:
  match r:
    case W.Got{now, s}:
      get_query.read(a, now, get_read(W.get_nat(s)))
    case W.Bad{}:
      W.Bad{}

def get_query.tag(t: Nat, s: String) -> W.Dec<M.Query>:
  match t:
    case 0n:
      get_query.now(M.AskLoad{}, W.get_nat(s))
    case 1n:
      get_query.now(M.AskCheck{}, W.get_nat(s))
    case 2n:
      get_query.now(M.AskStore{}, W.get_nat(s))
    case 3n+p:
      W.Bad{}

def get_query(r: W.Dec<Nat>) -> W.Dec<M.Query>:
  match r:
    case W.Got{t, s}:
      get_query.tag(t, s)
    case W.Bad{}:
      W.Bad{}

def put_verdict(v: M.Verdict) -> String:
  match v:
    case M.Serve{}:
      W.put_nat(0n, "")
    case M.Refresh{}:
      W.put_nat(1n, "")
    case M.Refuse{}:
      W.put_nat(2n, "")
    case M.KeepPeer{}:
      W.put_nat(3n, "")
    case M.Write{}:
      W.put_nat(4n, "")

def ffi.fin(done: Bool, q: M.Query) -> String:
  match done:
    case True{}:
      put_verdict(M.judge(q))
    case False{}:
      W.err("auth_read: malformed request")

def ffi.go(r: W.Dec<M.Query>) -> String:
  match r:
    case W.Got{q, s}:
      ffi.fin(W.end(s), q)
    case W.Bad{}:
      W.err("auth_read: malformed request")

def ffi(input: String) -> String:
  ffi.go(get_query(W.get_nat(input)))
