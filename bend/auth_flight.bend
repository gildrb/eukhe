# auth_flight: the model of the OAuth refresh of one provider's stored
# credential, and the desk the Rust refresh runs (section The desk the
# Rust runs, compiled through bend/ffi_auth_flight.bend). The Rust code
# (crates/eukhe-core/src/auth/flight.rs) runs the callers on threads,
# reads, fetches and writes, sends the desk each caller's events in the
# order they come and does what it answers; the desk decides who leads,
# who joins, when a flight lands and whom it serves. laws/auth_flight.bend
# ties the desk to the model's steps for every order of events.
#
# Each caller takes its refresh one step at a time. A caller loads the
# stored credential and is served it when it is fresh. Otherwise it boards:
# it joins the flight in flight, or it starts a flight and leads it. The
# leader checks the store again, fetches a new credential, stores it, and
# lands the flight with its outcome; each caller that joined the flight
# takes that outcome. Between any two steps, a peer process can store a
# fresh credential, and the stored credential can expire.
#
# Flights are numbered in the order they start; flight f's outcome is at
# index f of the landed outcomes. Credentials and failed fetches are
# numbered: the n-th fetch gives credential n or failure n, and a peer
# stores the stored credential's number plus one (a newer credential).

import Base

# what a refresh gives its caller: credential c, or failure e
type Out is Data:
  Ok{c: Nat}
  Err{e: Nat}

# where one caller's refresh stands: f is the flight it leads or joined;
# `via` of a finished refresh is that flight (None: the load served it)
type Leg is Data:
  Load{}
  Board{}
  Check{f: Nat}
  Fetch{f: Nat}
  Store{f: Nat, c: Nat}
  Land{f: Nat, o: Out}
  Waiting{f: Nat}
  Served{via: Maybe<&2, Nat>, o: Out}

# the stored credential, and whether it is fresh
type Sto is Data:
  Sto{c: Nat, fresh: Bool}

# the world: the store, whether a flight is in flight, the landed
# outcomes, the fetches made
type W is Data:
  W{sto: Sto, fl: Bool, landed: List<&2, Out>, n: Nat}

# the world and the callers, in the order they arrived
type St is Data:
  St{w: W, cs: List<&2, Leg>}

# a caller arrives; caller k takes its next step (a fetch at this step
# succeeds when ok); a peer stores a fresh credential; the stored
# credential expires
type Ev is Data:
  Arrive{}
  Step{k: Nat, ok: Bool}
  Peer{}
  Expire{}

# a caller's leg and the world after its step
type Adv is Data:
  Adv{l: Leg, w: W}

def Sto.c(s: Sto) -> Nat:
  match s:
    case Sto{c, f}:
      c

def Sto.fresh(s: Sto) -> Bool:
  match s:
    case Sto{c, f}:
      f

def W.sto(w: W) -> Sto:
  match w:
    case W{s, fl, ld, n}:
      s

def W.fl(w: W) -> Bool:
  match w:
    case W{s, fl, ld, n}:
      fl

def W.landed(w: W) -> List<&2, Out>:
  match w:
    case W{s, fl, ld, n}:
      ld

def W.n(w: W) -> Nat:
  match w:
    case W{s, fl, ld, n}:
      n

def St.w(s: St) -> W:
  match s:
    case St{w, cs}:
      w

def St.cs(s: St) -> List<&2, Leg>:
  match s:
    case St{w, cs}:
      cs

def Adv.l(a: Adv) -> Leg:
  match a:
    case Adv{l, w}:
      l

def Adv.w(a: Adv) -> W:
  match a:
    case Adv{l, w}:
      w

# The steps of a caller
# ---------------------

# load: a fresh stored credential is served
def adv.load(s: Sto, +w: W) -> Adv:
  match s:
    case Sto{c, fresh}:
      match fresh:
        case True{}:
          Adv{Served{None{}, Ok{c}}, w}
        case False{}:
          Adv{Board{}, w}

# board: join the flight in flight, or start the next flight and lead it
def adv.board(w: W) -> Adv:
  match w:
    case W{s, fl, +ld, n}:
      match fl:
        case True{}:
          Adv{Waiting{List.length(&2, Out, ld)}, W{s, True{}, ld, n}}
        case False{}:
          Adv{Check{List.length(&2, Out, ld)}, W{s, True{}, ld, n}}

# check: a credential stored fresh since the load lands the flight
def adv.check(+f: Nat, s: Sto, +w: W) -> Adv:
  match s:
    case Sto{c, fresh}:
      match fresh:
        case True{}:
          Adv{Land{f, Ok{c}}, w}
        case False{}:
          Adv{Fetch{f}, w}

# fetch: the next credential, or the next failure
def adv.fetch(+f: Nat, w: W, ok: Bool) -> Adv:
  match w:
    case W{s, fl, ld, +n}:
      match ok:
        case True{}:
          Adv{Store{f, 1n+n}, W{s, fl, ld, 1n+n}}
        case False{}:
          Adv{Land{f, Err{1n+n}}, W{s, fl, ld, 1n+n}}

# store: a fresh credential a peer stored stands; else the fetched one
# is stored
def adv.store(+f: Nat, +c: Nat, w: W) -> Adv:
  match w:
    case W{s, fl, ld, n}:
      match s:
        case Sto{+p, fresh}:
          match fresh:
            case True{}:
              Adv{Land{f, Ok{p}}, W{Sto{p, True{}}, fl, ld, n}}
            case False{}:
              Adv{Land{f, Ok{c}}, W{Sto{c, True{}}, fl, ld, n}}

# land: the flight ends with its outcome
def adv.land(+f: Nat, +o: Out, w: W) -> Adv:
  match w:
    case W{s, fl, ld, n}:
      Adv{Served{Some{f}, o}, W{s, False{}, List.append(&2, Out, ld, [o]), n}}

def adv.wait.got(+f: Nat, m: Maybe<&2, Out>, +w: W) -> Adv:
  match m:
    case None{}:
      Adv{Waiting{f}, w}
    case Some{o}:
      Adv{Served{Some{f}, o}, w}

# wait: the flight's outcome, once it landed
def adv.wait(+f: Nat, +w: W) -> Adv:
  adv.wait.got(f, List.get(&2, Out, W.landed(w), f), w)

def adv(l: Leg, ok: Bool, +w: W) -> Adv:
  match l:
    case Load{}:
      adv.load(W.sto(w), w)
    case Board{}:
      adv.board(w)
    case Check{f}:
      adv.check(f, W.sto(w), w)
    case Fetch{f}:
      adv.fetch(f, w, ok)
    case Store{f, c}:
      adv.store(f, c, w)
    case Land{f, o}:
      adv.land(f, o, w)
    case Waiting{f}:
      adv.wait(f, w)
    case Served{v, o}:
      Adv{Served{v, o}, w}

# The events
# ----------

# caller k takes the leg its step gives; the others stay
def put(+k: Nat, a: Adv, +cs: List<&2, Leg>) -> St:
  match a:
    case Adv{l, w}:
      St{w, List.append(&2, Leg, List.take(&2, Leg, cs, k), l <> List.drop(&2, Leg, cs, 1n+k))}

def step.at(m: Maybe<&2, Leg>, +k: Nat, ok: Bool, +w: W, +cs: List<&2, Leg>) -> St:
  match m:
    case None{}:
      St{w, cs}
    case Some{l}:
      put(k, adv(l, ok, w), cs)

def step(s: St, e: Ev) -> St:
  match s:
    case St{w, +cs}:
      match w:
        case W{sto, +fl, +ld, +n}:
          match sto:
            case Sto{+c, +fresh}:
              match e:
                case Arrive{}:
                  St{W{Sto{c, fresh}, fl, ld, n}, List.append(&2, Leg, cs, [Load{}])}
                case Step{+k, ok}:
                  step.at(List.get(&2, Leg, cs, k), k, ok, W{Sto{c, fresh}, fl, ld, n}, cs)
                case Peer{}:
                  St{W{Sto{1n+c, True{}}, fl, ld, n}, cs}
                case Expire{}:
                  St{W{Sto{c, False{}}, fl, ld, n}, cs}

# the state after evs, from s
def go(evs: List<&2, Ev>, s: St) -> St:
  match evs:
    case Nil{}:
      s
    case e <> rest:
      go(rest, step(s, e))

# no caller yet; the store holds credential 0, expired
def St.new() -> St:
  St{W{Sto{0n, False{}}, False{}, Nil{}, 0n}, Nil{}}

def run(evs: List<&2, Ev>) -> St:
  go(evs, St.new())

# What the laws speak of
# ----------------------

def le(a: Nat, b: Nat) -> Bool:
  match a b:
    case 0n _:
      True{}
    case 1n+p 0n:
      False{}
    case 1n+p 1n+q:
      le(p, q)

def fetching.of(l: Leg) -> Nat:
  match l:
    case Fetch{f}:
      1n
    case _:
      0n

# the callers that fetch now
def fetching(cs: List<&2, Leg>) -> Nat:
  match cs:
    case Nil{}:
      0n
    case l <> t:
      Nat.add(fetching.of(l), fetching(t))

# the flight a caller leads
def led(l: Leg) -> Maybe<&2, Nat>:
  match l:
    case Check{f}:
      Some{f}
    case Fetch{f}:
      Some{f}
    case Store{f, c}:
      Some{f}
    case Land{f, o}:
      Some{f}
    case _:
      None{}

# a caller that arrives in s and takes a step is served the stored
# credential, and it is c or a newer one
def After(+c: Nat, +s: St, ok: Bool) -> Type:
  +k = List.length(&2, Leg, St.cs(s))
  +stored = Sto.c(W.sto(St.w(s)))
  ({List.get(&2, Leg, St.cs(step(step(s, Arrive{}), Step{k, ok})), k) == Some{Served{None{}, Ok{stored}}} : Maybe<&2, Leg>} & {le(c, stored) == True{} : Bool})

# The desk the Rust runs
# ----------------------
# The Rust refresh keeps one desk per auth document behind a mutex (the
# stepper of bend/ffi_auth_flight.bend). Each caller's thread sends the
# desk its caller's events in the order they come (it arrives; its read,
# fetch or write found something; it unwinds) and does what the desk
# answers: load, check, fetch, store, wait, done, failed. Who leads a
# provider's flight, who joins it, when it lands and whom it serves is
# decided here; the threads only read, fetch, write and pass each answer
# to its caller. Credentials and failures stay in the Rust: an answer
# that serves or stores one means the payload of the event it answers
# (what the reporting caller found), so every caller of a flight is
# served the payload of the event that lands it.

# where a live caller stands: asked to load; leading its provider's
# flight at its check, its fetch or its store; waiting for its provider's
# flight to land
type At is Data:
  Loads{}
  Checks{}
  Fetches{}
  Stores{}
  Waits{}

# a live caller: its number, its provider, where it stands
type Cl is Data:
  Cl{k: Nat, p: String, at: At}

# the live callers, newest first, and the next caller's number
type Desk is Data:
  Desk{cs: List<&2, Cl>, m: Nat}

# what a caller's read, fetch or write found: the load a fresh credential,
# an expired one, or no refresh can start; the check a fresh credential or
# none; the fetch a credential or a failure; the store its outcome (the
# credential stored, a peer's fresher one, or why the write failed)
type Fd is Data:
  LoadFresh{}
  LoadExpired{}
  LoadFailed{}
  CheckFresh{}
  CheckExpired{}
  FetchOk{}
  FetchFailed{}
  Stored{}

# a caller arrives for provider p; caller k found fd; caller k unwinds
# (it leaves with no outcome); how many wait on p's flight
type DEv is Data:
  Comes{p: String}
  Found{k: Nat, fd: Fd}
  Unwinds{k: Nat}
  Joiners{p: String}

# what a caller does next: load, check, fetch, store this event's
# credential, wait, done with this event's payload, or failed with e
type Act is Data:
  DoLoad{}
  DoCheck{}
  DoFetch{}
  DoStore{}
  DoWait{}
  DoDone{}
  DoFail{e: String}

type To is Data:
  To{k: Nat, a: Act}

# the desk's answer: what callers do; how many wait on a provider's
# flight (none when it has no flight); out of turn (the event names no
# live caller, or one whose place takes no such event)
type DOut is Data:
  Acts{xs: List<&2, To>}
  Joined{j: Maybe<&2, Nat>}
  Off{}

type DRes is Data:
  DRes{d: Desk, o: DOut}

# no caller yet
def Desk.new() -> Desk:
  Desk{Nil{}, 0n}

def Cl.k(x: Cl) -> Nat:
  match x:
    case Cl{k, p, a}:
      k

# what the callers waiting on p's flight are served when its leader
# unwinds with no outcome
def gone(p: String) -> String:
  String.append("the token refresh of ", String.append(p, " ended without an outcome"))

# a caller at a leads its provider's flight
def leads(a: At) -> Bool:
  match a:
    case Loads{}:
      False{}
    case Checks{}:
      True{}
    case Fetches{}:
      True{}
    case Stores{}:
      True{}
    case Waits{}:
      False{}

# the step a place takes a found at: 0 the load, 1 the check, 2 the
# fetch, 3 the store (4: a waiting caller takes none)
def At.tag(a: At) -> Nat:
  match a:
    case Loads{}:
      0n
    case Checks{}:
      1n
    case Fetches{}:
      2n
    case Stores{}:
      3n
    case Waits{}:
      4n

def Fd.tag(fd: Fd) -> Nat:
  match fd:
    case LoadFresh{}:
      0n
    case LoadExpired{}:
      0n
    case LoadFailed{}:
      0n
    case CheckFresh{}:
      1n
    case CheckExpired{}:
      1n
    case FetchOk{}:
      2n
    case FetchFailed{}:
      2n
    case Stored{}:
      3n

def find.at(hit: Bool, x: Cl, r: Maybe<&2, Cl>) -> Maybe<&2, Cl>:
  match hit:
    case True{}:
      Some{x}
    case False{}:
      r

# caller k
def find(+k: Nat, cs: List<&2, Cl>) -> Maybe<&2, Cl>:
  match cs:
    case Nil{}:
      None{}
    case +x <> t:
      find.at(Nat.is_eq(Cl.k(x), k), x, find(k, t))

def set.at(hit: Bool, x: Cl, +a: At, t: List<&2, Cl>, r: List<&2, Cl>) -> List<&2, Cl>:
  match hit:
    case True{}:
      match x:
        case Cl{j, p, o}:
          Cl{j, p, a} <> t
    case False{}:
      x <> r

# caller k stands at a
def set(+k: Nat, +a: At, cs: List<&2, Cl>) -> List<&2, Cl>:
  match cs:
    case Nil{}:
      Nil{}
    case +x <> +t:
      set.at(Nat.is_eq(Cl.k(x), k), x, a, t, set(k, a, t))

def cut.at(hit: Bool, x: Cl, t: List<&2, Cl>, r: List<&2, Cl>) -> List<&2, Cl>:
  match hit:
    case True{}:
      t
    case False{}:
      x <> r

# caller k leaves
def cut(+k: Nat, cs: List<&2, Cl>) -> List<&2, Cl>:
  match cs:
    case Nil{}:
      Nil{}
    case +x <> +t:
      cut.at(Nat.is_eq(Cl.k(x), k), x, t, cut(k, t))

# x waits on p's flight
def waits(+p: String, x: Cl) -> Bool:
  match x:
    case Cl{j, q, a}:
      match a:
        case Loads{}:
          False{}
        case Checks{}:
          False{}
        case Fetches{}:
          False{}
        case Stores{}:
          False{}
        case Waits{}:
          String.eq(q, p)

# x leads p's flight
def lead(+p: String, x: Cl) -> Bool:
  match x:
    case Cl{j, q, a}:
      Bool.and(leads(a), String.eq(q, p))

# p has a flight in flight
def inflight(+p: String, cs: List<&2, Cl>) -> Bool:
  match cs:
    case Nil{}:
      False{}
    case +x <> t:
      Bool.or(lead(p, x), inflight(p, t))

def unwait.at(hit: Bool, x: Cl, r: List<&2, Cl>) -> List<&2, Cl>:
  match hit:
    case True{}:
      r
    case False{}:
      x <> r

# the callers waiting on p's flight leave
def unwait(+p: String, cs: List<&2, Cl>) -> List<&2, Cl>:
  match cs:
    case Nil{}:
      Nil{}
    case +x <> t:
      unwait.at(waits(p, x), x, unwait(p, t))

def wake.at(hit: Bool, x: Cl, +a: Act, r: List<&2, To>) -> List<&2, To>:
  match hit:
    case True{}:
      To{Cl.k(x), a} <> r
    case False{}:
      r

# each caller waiting on p's flight does a
def wake(+p: String, +a: Act, cs: List<&2, Cl>) -> List<&2, To>:
  match cs:
    case Nil{}:
      Nil{}
    case +x <> t:
      wake.at(waits(p, x), x, a, wake(p, a, t))

def joined.at(hit: Bool, r: Nat) -> Nat:
  match hit:
    case True{}:
      1n+r
    case False{}:
      r

# how many wait on p's flight
def joined(+p: String, cs: List<&2, Cl>) -> Nat:
  match cs:
    case Nil{}:
      0n
    case +x <> t:
      joined.at(waits(p, x), joined(p, t))

# the leader k of p's flight lands it: k and every caller waiting on the
# flight are done with this event's payload, and leave
def land(+k: Nat, +p: String, cs: List<&2, Cl>, m: Nat) -> DRes:
  +rest = cut(k, cs)
  DRes{Desk{unwait(p, rest), m}, Acts{To{k, DoDone{}} <> wake(p, DoDone{}, rest)}}

# caller k's credential expired: it joins p's flight in flight, or leads
# a new one
def board(fl: Bool, +k: Nat, cs: List<&2, Cl>, m: Nat) -> DRes:
  match fl:
    case True{}:
      DRes{Desk{set(k, Waits{}, cs), m}, Acts{[To{k, DoWait{}}]}}
    case False{}:
      DRes{Desk{set(k, Checks{}, cs), m}, Acts{[To{k, DoCheck{}}]}}

# caller k of provider p found fd, at the step its place takes it: a fresh
# credential at the load, or no refresh at all, is done; an expired one
# boards; the leader's check lands on a fresh credential and fetches
# otherwise; a fetched credential is stored, a failed fetch lands; the
# store's outcome lands
def found.go(fd: Fd, +k: Nat, +p: String, +cs: List<&2, Cl>, +m: Nat) -> DRes:
  match fd:
    case LoadFresh{}:
      DRes{Desk{cut(k, cs), m}, Acts{[To{k, DoDone{}}]}}
    case LoadExpired{}:
      board(inflight(p, cs), k, cs, m)
    case LoadFailed{}:
      DRes{Desk{cut(k, cs), m}, Acts{[To{k, DoDone{}}]}}
    case CheckFresh{}:
      land(k, p, cs, m)
    case CheckExpired{}:
      DRes{Desk{set(k, Fetches{}, cs), m}, Acts{[To{k, DoFetch{}}]}}
    case FetchOk{}:
      DRes{Desk{set(k, Stores{}, cs), m}, Acts{[To{k, DoStore{}}]}}
    case FetchFailed{}:
      land(k, p, cs, m)
    case Stored{}:
      land(k, p, cs, m)

def found.fit(fit: Bool, fd: Fd, +k: Nat, +p: String, +cs: List<&2, Cl>, +m: Nat) -> DRes:
  match fit:
    case True{}:
      found.go(fd, k, p, cs, m)
    case False{}:
      DRes{Desk{cs, m}, Off{}}

def found(r: Maybe<&2, Cl>, +fd: Fd, +k: Nat, +cs: List<&2, Cl>, +m: Nat) -> DRes:
  match r:
    case None{}:
      DRes{Desk{cs, m}, Off{}}
    case Some{x}:
      match x:
        case Cl{j, p, a}:
          found.fit(Nat.is_eq(At.tag(a), Fd.tag(fd)), fd, k, p, cs, m)

# caller k of provider p unwinds: a leader's flight lands with the failure
# `gone`, served to every caller waiting on it; any other caller just
# leaves
def unwind.at(lead: Bool, +k: Nat, +p: String, cs: List<&2, Cl>, m: Nat) -> DRes:
  match lead:
    case True{}:
      +rest = cut(k, cs)
      DRes{Desk{unwait(p, rest), m}, Acts{wake(p, DoFail{gone(p)}, rest)}}
    case False{}:
      DRes{Desk{cut(k, cs), m}, Acts{Nil{}}}

def unwind(r: Maybe<&2, Cl>, +k: Nat, +cs: List<&2, Cl>, +m: Nat) -> DRes:
  match r:
    case None{}:
      DRes{Desk{cs, m}, Off{}}
    case Some{x}:
      match x:
        case Cl{j, p, a}:
          unwind.at(leads(a), k, p, cs, m)

def joiners(fl: Bool, +p: String, cs: List<&2, Cl>) -> Maybe<&2, Nat>:
  match fl:
    case True{}:
      Some{joined(p, cs)}
    case False{}:
      None{}

# the desk after event e, and its answer: an arrival is the next caller,
# asked to load; a found or an unwind of a live caller is decided above;
# an event naming no live caller is out of turn and changes nothing;
# joiners counts the callers waiting on p's flight
def desk.step(d: Desk, e: DEv) -> DRes:
  match d:
    case Desk{+cs, +m}:
      match e:
        case Comes{p}:
          DRes{Desk{Cl{m, p, Loads{}} <> cs, 1n+m}, Acts{[To{m, DoLoad{}}]}}
        case Found{+k, fd}:
          found(find(k, cs), fd, k, cs, m)
        case Unwinds{+k}:
          unwind(find(k, cs), k, cs, m)
        case Joiners{+p}:
          DRes{Desk{cs, m}, Joined{joiners(inflight(p, cs), p, cs)}}
