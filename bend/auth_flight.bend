# auth_flight: the model of the OAuth refresh of one provider's stored
# credential. The Rust code is `Leg::advance` and `FlightBook::advance`
# (crates/eukhe-core/src/auth/flight.rs); the bridge
# (bend/bridge_auth_flight.bend, crates/eukhe-core/src/auth/flight/bridge.rs)
# runs both on the same events.
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
