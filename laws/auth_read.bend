# eukhe: the laws of area auth_read

import Base
import ../bend/auth_flight.bend as F
import ../bend/ffi_auth_read.bend as FR
import ../bend/wire.bend as Wr
import ./base.bend as LawsBase

# ---- auth_read ----

# LAWS (A1): what a read of the auth document means to the OAuth refresh.
# The Rust refresh (crates/eukhe-core/src/auth/flight.rs) and the auth
# lookup (crates/eukhe-core/src/auth/manager/lookup.rs) read the document
# and hand the entry bend/ffi_auth_read.bend (a call) what they found
# under the provider and their clock; the entry answers what the read
# means: serve the credential, refresh, refuse to refresh, keep a peer's
# credential, write the fetched one. No Rust copy of the judgment: the
# Rust only reads, fetches and writes. PROOF.bend proves the laws (as
# AuthRead.<law>) with the lemmas of proof/auth_read/.
#
# The spec spells requests and reads replies with the wire primitives
# (bend/wire.bend), never with the entry's own codec. A read credential is
# fresh, for the model's store (bend/auth_flight.bend `Sto.fresh`), when it
# is an OAuth credential that expires after the clock (ar_fresh); the
# `*_is_model` laws tie each verdict to the model's step on such a store.

# Terms
# -----

# the tag Rust writes for what a read is for
def ar_ask_tag(a: F.Ask) -> Nat:
  match a:
    case F.AskLoad{}:
      0n
    case F.AskCheck{}:
      1n
    case F.AskStore{}:
      2n

# what a read found, as Rust writes it
def ar_spell_read(r: F.Read) -> String:
  match r:
    case F.Unread{}:
      Wr.put_nat(0n, "")
    case F.NoCred{}:
      Wr.put_nat(1n, "")
    case F.NotOauth{}:
      Wr.put_nat(2n, "")
    case F.Oauth{e}:
      Wr.put_nat(3n, Wr.put_nat(e, ""))

# the request Rust writes: what the read is for, the clock, what it found
def ar_spell(a: F.Ask, now: Nat, r: F.Read) -> String:
  Wr.put_nat(ar_ask_tag(a), Wr.put_nat(now, ar_spell_read(r)))

# an OAuth credential's expiry fits the wire
def ar_read_fits(r: F.Read) -> Bool:
  match r:
    case F.Unread{}:
      True{}
    case F.NoCred{}:
      True{}
    case F.NotOauth{}:
      True{}
    case F.Oauth{e}:
      LawsBase.wire_fits(e)

# a read credential is fresh at now: it is OAuth and expires after now
def ar_fresh(now: Nat, r: F.Read) -> Bool:
  match r:
    case F.Unread{}:
      False{}
    case F.NoCred{}:
      False{}
    case F.NotOauth{}:
      False{}
    case F.Oauth{e}:
      Nat.is_lt(now, e)

# the reply yes when b holds, else no
def ar_pick(b: Bool, yes: Nat, no: Nat) -> String:
  match b:
    case True{}:
      Wr.put_nat(yes, "")
    case False{}:
      Wr.put_nat(no, "")

# the load: a fresh OAuth credential serves (0), an expired one refreshes
# (1); with no OAuth credential no refresh can start (2)
def ar_reply.load(now: Nat, r: F.Read) -> String:
  match r:
    case F.Unread{}:
      Wr.put_nat(2n, "")
    case F.NoCred{}:
      Wr.put_nat(2n, "")
    case F.NotOauth{}:
      Wr.put_nat(2n, "")
    case F.Oauth{e}:
      ar_pick(Nat.is_lt(now, e), 0n, 1n)

# the reply: the load as above; the check serves a fresh credential (0)
# and refreshes otherwise (1); the store keeps a peer's fresh credential
# (3) and writes otherwise (4)
def ar_reply(a: F.Ask, +now: Nat, +r: F.Read) -> String:
  match a:
    case F.AskLoad{}:
      ar_reply.load(now, r)
    case F.AskCheck{}:
      ar_pick(ar_fresh(now, r), 0n, 1n)
    case F.AskStore{}:
      ar_pick(ar_fresh(now, r), 3n, 4n)

def ar_reply_q(q: F.Query) -> String:
  match q:
    case F.Query{a, now, r}:
      ar_reply(a, now, r)

# The reader: the requests Rust writes, as the wire primitives read them

def ar_read.oauth(r: Wr.Dec<Nat>) -> Wr.Dec<F.Read>:
  match r:
    case Wr.Got{e, s}:
      Wr.Got{F.Oauth{e}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def ar_read.found(t: Nat, s: String) -> Wr.Dec<F.Read>:
  match t:
    case 0n:
      Wr.Got{F.Unread{}, s}
    case 1n:
      Wr.Got{F.NoCred{}, s}
    case 2n:
      Wr.Got{F.NotOauth{}, s}
    case 3n:
      ar_read.oauth(Wr.get_nat(s))
    case 4n+p:
      Wr.Bad{}

def ar_read.read(r: Wr.Dec<Nat>) -> Wr.Dec<F.Read>:
  match r:
    case Wr.Got{t, s}:
      ar_read.found(t, s)
    case Wr.Bad{}:
      Wr.Bad{}

def ar_read.query(a: F.Ask, now: Nat, r: Wr.Dec<F.Read>) -> Wr.Dec<F.Query>:
  match r:
    case Wr.Got{x, s}:
      Wr.Got{F.Query{a, now, x}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def ar_read.now(a: F.Ask, r: Wr.Dec<Nat>) -> Wr.Dec<F.Query>:
  match r:
    case Wr.Got{now, s}:
      ar_read.query(a, now, ar_read.read(Wr.get_nat(s)))
    case Wr.Bad{}:
      Wr.Bad{}

def ar_read.tag(t: Nat, s: String) -> Wr.Dec<F.Query>:
  match t:
    case 0n:
      ar_read.now(F.AskLoad{}, Wr.get_nat(s))
    case 1n:
      ar_read.now(F.AskCheck{}, Wr.get_nat(s))
    case 2n:
      ar_read.now(F.AskStore{}, Wr.get_nat(s))
    case 3n+p:
      Wr.Bad{}

def ar_read.go(r: Wr.Dec<Nat>) -> Wr.Dec<F.Query>:
  match r:
    case Wr.Got{t, s}:
      ar_read.tag(t, s)
    case Wr.Bad{}:
      Wr.Bad{}

def ar_whole(whole: Bool, q: F.Query) -> Maybe<&2, F.Query>:
  match whole:
    case True{}:
      Some{q}
    case False{}:
      None{}

def ar_read.whole(r: Wr.Dec<F.Query>) -> Maybe<&2, F.Query>:
  match r:
    case Wr.Got{q, s}:
      ar_whole(Wr.end(s), q)
    case Wr.Bad{}:
      None{}

# the read to judge, when s is exactly one request
def ar_read(s: String) -> Maybe<&2, F.Query>:
  ar_read.whole(ar_read.go(Wr.get_nat(s)))

# The replies, as Rust reads them, and the model's steps they stand for

def ar_code.whole(whole: Bool, t: Nat) -> Maybe<&2, Nat>:
  match whole:
    case True{}:
      Some{t}
    case False{}:
      None{}

def ar_code.go(r: Wr.Dec<Nat>) -> Maybe<&2, Nat>:
  match r:
    case Wr.Got{t, s}:
      ar_code.whole(Wr.end(s), t)
    case Wr.Bad{}:
      None{}

# the verdict a reply spells, when it is exactly one tag
def ar_code(s: String) -> Maybe<&2, Nat>:
  ar_code.go(Wr.get_nat(s))

# the leg after the load the verdict m directs, on a stored credential c:
# 0 serves c, 1 boards; any other leaves the caller at its load
def ar_load_leg(m: Maybe<&2, Nat>, c: Nat) -> F.Leg:
  match m:
    case None{}:
      F.Load{}
    case Some{t}:
      match t:
        case 0n:
          F.Served{None{}, F.Ok{c}}
        case 1n:
          F.Board{}
        case 2n+q:
          F.Load{}

# the leg after the leader's check of flight f the verdict m directs, on a
# stored credential c: 0 lands the flight on c, 1 fetches; any other
# leaves the leader at its load
def ar_check_leg(m: Maybe<&2, Nat>, f: Nat, c: Nat) -> F.Leg:
  match m:
    case None{}:
      F.Load{}
    case Some{t}:
      match t:
        case 0n:
          F.Land{f, F.Ok{c}}
        case 1n:
          F.Fetch{f}
        case 2n+q:
          F.Load{}

# the store of flight f's fetched credential c, over a store holding the
# credential p, the verdict m directs, and what the store holds after it:
# 3 keeps p and lands on it, 4 writes c and lands on it; any other leaves
# the leader at its load and the store as it was
def ar_store_adv(m: Maybe<&2, Nat>, +f: Nat, +p: Nat, +c: Nat, +fresh: Bool, fl: Bool, ld: List<&2, F.Out>, n: Nat) -> F.Adv:
  match m:
    case None{}:
      F.Adv{F.Load{}, F.W{F.Sto{p, fresh}, fl, ld, n}}
    case Some{t}:
      match t:
        case 0n:
          F.Adv{F.Load{}, F.W{F.Sto{p, fresh}, fl, ld, n}}
        case 1n:
          F.Adv{F.Load{}, F.W{F.Sto{p, fresh}, fl, ld, n}}
        case 2n:
          F.Adv{F.Load{}, F.W{F.Sto{p, fresh}, fl, ld, n}}
        case 3n:
          F.Adv{F.Land{f, F.Ok{p}}, F.W{F.Sto{p, True{}}, fl, ld, n}}
        case 4n:
          F.Adv{F.Land{f, F.Ok{c}}, F.W{F.Sto{c, True{}}, fl, ld, n}}
        case 5n+q:
          F.Adv{F.Load{}, F.W{F.Sto{p, fresh}, fl, ld, n}}

# Laws
# ----

# LAW auth_read_answers: on every request Rust writes (its clock and expiry
# within the wire), the entry answers the verdict: the load serves a fresh
# OAuth credential, refreshes an expired one and refuses to refresh
# anything else (an unreadable document, no credential, an API key); the
# check serves a fresh credential and refreshes otherwise; the store keeps
# a peer's fresh credential and writes otherwise
# EXCLUDES: a misread clock or expiry; an expired credential served (an
#   off-by-one at the expiry instant included); a refresh started on an
#   API key, a missing credential or an unreadable document; a second
#   fetch after a flight stored a fresh credential; a peer's fresher
#   credential overwritten; an expired or non-OAuth credential kept
law auth_read_answers:
  for +a: F.Ask
  for +now: Nat
  for +r: F.Read
  for fnow: {LawsBase.wire_fits(now) == True{} : Bool}
  for fr: {ar_read_fits(r) == True{} : Bool}
  {FR.ffi(ar_spell(a, now, r)) == ar_reply(a, now, r) : String}

# LAW auth_read_reads: every input that is exactly one request (as the wire
# primitives read it) gets the verdict on it
# EXCLUDES: a verdict on another reading of the input
law auth_read_reads:
  for +s: String
  for +q: F.Query
  for got: {ar_read(s) == Some{q} : Maybe<&2, F.Query>}
  {FR.ffi(s) == ar_reply_q(q) : String}

# LAW auth_read_malformed_exact: every input that is not exactly one request
# gets exactly the error form 'E ', then "auth_read: malformed request"
# EXCLUDES: a guessed verdict for garbage, a request with input after it
#   answered
law auth_read_malformed_exact:
  for +s: String
  for no: {ar_read(s) == None{} : Maybe<&2, F.Query>}
  {FR.ffi(s) == SCon{'E', SCon{' ', "auth_read: malformed request"}} : String}

# LAW auth_read_load_is_model: the verdict on a load of an OAuth credential
# directs the model's load (adv.load) on a store holding it, fresh when it
# expires after the clock
# EXCLUDES: a load verdict that serves what the model refreshes or the
#   reverse, so the A1 laws would not hold of the Rust refresh
law auth_read_load_is_model:
  for +now: Nat
  for +e: Nat
  for +c: Nat
  for +w: F.W
  for fnow: {LawsBase.wire_fits(now) == True{} : Bool}
  for fe: {LawsBase.wire_fits(e) == True{} : Bool}
  {ar_load_leg(ar_code(FR.ffi(ar_spell(F.AskLoad{}, now, F.Oauth{e}))), c) == F.Adv.l(F.adv.load(F.Sto{c, ar_fresh(now, F.Oauth{e})}, w)) : F.Leg}

# LAW auth_read_check_is_model: the verdict on the leader's check of any
# read directs the model's check (adv.check) on a store holding it, fresh
# when it is an OAuth credential that expires after the clock
# EXCLUDES: a check that fetches again over a fresh credential (a wasted
#   single-use refresh token) or lands the flight on an expired one
law auth_read_check_is_model:
  for +now: Nat
  for +r: F.Read
  for +f: Nat
  for +c: Nat
  for +w: F.W
  for fnow: {LawsBase.wire_fits(now) == True{} : Bool}
  for fr: {ar_read_fits(r) == True{} : Bool}
  {ar_check_leg(ar_code(FR.ffi(ar_spell(F.AskCheck{}, now, r))), f, c) == F.Adv.l(F.adv.check(f, F.Sto{c, ar_fresh(now, r)}, w)) : F.Leg}

# LAW auth_read_store_is_model: the verdict on the store's read of the
# credential p a peer may have stored directs the model's store
# (adv.store) of the fetched credential c: the leg (the flight lands on
# p or on c) and what the store holds after it
# EXCLUDES: a peer's fresh credential overwritten (the peer's single-use
#   refresh token lost), an expired or non-OAuth credential kept instead
#   of the fetched one, a store that lands on another credential than it
#   leaves stored
law auth_read_store_is_model:
  for +now: Nat
  for +r: F.Read
  for +f: Nat
  for +p: Nat
  for +c: Nat
  for +fl: Bool
  for +ld: List<&2, F.Out>
  for +n: Nat
  for fnow: {LawsBase.wire_fits(now) == True{} : Bool}
  for fr: {ar_read_fits(r) == True{} : Bool}
  {ar_store_adv(ar_code(FR.ffi(ar_spell(F.AskStore{}, now, r))), f, p, c, ar_fresh(now, r), fl, ld, n) == F.adv.store(f, c, F.W{F.Sto{p, ar_fresh(now, r)}, fl, ld, n}) : F.Adv}

# LAW auth_read_example: anchor: the strings Rust writes and the replies
# it reads: a load at 5 of an OAuth credential expiring at 9 serves, at 9
# refreshes, of no credential refuses; a check of an API key refreshes and
# of a fresh credential serves; a store over a fresh peer credential keeps
# it, over an expired one or an unreadable document writes; an unknown
# ask, an unknown read and input left over are refused
# EXCLUDES: a tag numbering or field order other than Rust's
law auth_read_example:
  {[FR.ffi("0,5,3,9,"), FR.ffi("0,9,3,9,"), FR.ffi("0,5,1,"), FR.ffi("1,5,2,"), FR.ffi("1,5,3,9,"), FR.ffi("2,5,3,9,"), FR.ffi("2,9,3,9,"), FR.ffi("2,5,0,")] == ["0,", "1,", "2,", "1,", "0,", "3,", "4,", "4,"] : List<&2, String>} &
  {[FR.ffi("3,5,0,"), FR.ffi("0,5,4,"), FR.ffi("0,5,0,x")] == [Wr.err("auth_read: malformed request"), Wr.err("auth_read: malformed request"), Wr.err("auth_read: malformed request")] : List<&2, String>}
