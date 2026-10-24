# auth_flight: the model of the OAuth refresh of one provider's stored
# credential, and the decisions the Rust refresh takes at each step. The
# Rust code (crates/eukhe-core/src/auth/flight.rs) runs the callers on
# threads and moves the bytes; it asks `next` and `book.step` (section The
# decisions the Rust takes, compiled through bend/ffi_auth_flight.bend)
# what follows each step. The bridge (bridge/bridge_auth_flight.bend,
# crates/eukhe-core/src/auth/flight/bridge.rs) runs the Rust dispatch over
# those decisions and the model on the same interleavings.
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

# The decisions the Rust takes
# ----------------------------
# The Rust refresh runs each caller on its own thread: a leg reads, fetches
# or writes with no lock held, and the flights of one auth document are one
# book under a mutex. The credentials and failures stay in the Rust; what
# follows each step is decided here:
# - `next`: the leg after a read, fetch or write (the call of the entry)
# - `book.step`: the book's answer to a board, a land, a wait (its stepper)
# The laws tie `next` to the model's steps (`adv.*`).

# what a leg's read, fetch or write found, and the flight the leg is on:
# the load found a fresh credential, an expired one, or no refresh can
# start; the check found a fresh credential or not; the fetch a credential
# or a failure; the store wrote (or kept a peer's credential, or failed)
type Io is Data:
  LoadFresh{}
  LoadExpired{}
  LoadFailed{}
  CheckFresh{f: Nat}
  CheckExpired{f: Nat}
  FetchOk{f: Nat}
  FetchFailed{f: Nat}
  Stored{f: Nat}

# the leg that follows: board, fetch, store the fetched credential, land
# the flight with what was found, or done with what was found
type Next is Data:
  NBoard{}
  NFetch{f: Nat}
  NStore{f: Nat}
  NLand{f: Nat}
  NDone{}

# the leg after a step that found io
def next(io: Io) -> Next:
  match io:
    case LoadFresh{}:
      NDone{}
    case LoadExpired{}:
      NBoard{}
    case LoadFailed{}:
      NDone{}
    case CheckFresh{f}:
      NLand{f}
    case CheckExpired{f}:
      NFetch{f}
    case FetchOk{f}:
      NStore{f}
    case FetchFailed{f}:
      NLand{f}
    case Stored{f}:
      NLand{f}

# a model leg as the Rust holds it, its credential or failure aside (none
# for the legs no read, fetch or write gives)
def shape(l: Leg) -> Maybe<&2, Next>:
  match l:
    case Load{}:
      None{}
    case Board{}:
      Some{NBoard{}}
    case Check{f}:
      None{}
    case Fetch{f}:
      Some{NFetch{f}}
    case Store{f, c}:
      Some{NStore{f}}
    case Land{f, o}:
      Some{NLand{f}}
    case Waiting{f}:
      None{}
    case Served{v, o}:
      Some{NDone{}}

# The book
# --------
# The flights of one document, of every provider: the providers in flight
# (each with its flight and how many callers joined it), the landed
# flights whose joiners did not all take the outcome yet (with how many
# still wait), and how many flights started (the next flight's number).
# The outcomes stay in the Rust, under the flight's number.

type Fly is Data:
  Fly{p: String, f: Nat, j: Nat}

type Lnd is Data:
  Lnd{f: Nat, w: Nat}

type Book is Data:
  Book{fly: List<&2, Fly>, lnd: List<&2, Lnd>, n: Nat}

# a caller of provider p boards; the leader of p's flight f lands it; a
# caller that joined flight f asks for its outcome; how many joined p's
# flight (the tests wait on it)
type BEv is Data:
  EvBoard{p: String}
  EvLand{p: String, f: Nat}
  EvWait{f: Nat}
  EvJoiners{p: String}

# lead the new flight f; join p's flight f; the outcome is kept for the
# joiners; no joiner, nothing kept; flight f did not land yet; take its
# outcome (more joiners wait); take it, the last joiner; the joiners of
# p's flight, none when p is not in flight
type BOut is Data:
  OLead{f: Nat}
  OJoin{f: Nat}
  OKept{}
  ODropped{}
  ONotYet{}
  OTake{}
  OTakeLast{}
  OJoiners{j: Maybe<&2, Nat>}

type BRes is Data:
  BRes{b: Book, o: BOut}

def Book.new() -> Book:
  Book{Nil{}, Nil{}, 0n}

def Fly.p(x: Fly) -> String:
  match x:
    case Fly{p, f, j}:
      p

def Fly.f(x: Fly) -> Nat:
  match x:
    case Fly{p, f, j}:
      f

def Fly.j(x: Fly) -> Nat:
  match x:
    case Fly{p, f, j}:
      j

def Lnd.f(x: Lnd) -> Nat:
  match x:
    case Lnd{f, w}:
      f

def Lnd.w(x: Lnd) -> Nat:
  match x:
    case Lnd{f, w}:
      w

def fly.find.at(hit: Bool, x: Fly, r: Maybe<&2, Fly>) -> Maybe<&2, Fly>:
  match hit:
    case True{}:
      Some{x}
    case False{}:
      r

# p's flight in flight
def fly.find(+p: String, fs: List<&2, Fly>) -> Maybe<&2, Fly>:
  match fs:
    case Nil{}:
      None{}
    case +x <> t:
      fly.find.at(String.eq(Fly.p(x), p), x, fly.find(p, t))

def fly.join.at(hit: Bool, x: Fly, t: List<&2, Fly>, r: List<&2, Fly>) -> List<&2, Fly>:
  match hit:
    case True{}:
      match x:
        case Fly{p, f, j}:
          Fly{p, f, 1n+j} <> t
    case False{}:
      x <> r

# one more joiner on p's flight
def fly.join(+p: String, fs: List<&2, Fly>) -> List<&2, Fly>:
  match fs:
    case Nil{}:
      Nil{}
    case +x <> +t:
      fly.join.at(String.eq(Fly.p(x), p), x, t, fly.join(p, t))

def fly.drop.at(hit: Bool, x: Fly, t: List<&2, Fly>, r: List<&2, Fly>) -> List<&2, Fly>:
  match hit:
    case True{}:
      t
    case False{}:
      x <> r

# p's flight is no longer in flight
def fly.drop(+p: String, fs: List<&2, Fly>) -> List<&2, Fly>:
  match fs:
    case Nil{}:
      Nil{}
    case +x <> +t:
      fly.drop.at(String.eq(Fly.p(x), p), x, t, fly.drop(p, t))

def lnd.find.at(hit: Bool, x: Lnd, r: Maybe<&2, Lnd>) -> Maybe<&2, Lnd>:
  match hit:
    case True{}:
      Some{x}
    case False{}:
      r

# landed flight f
def lnd.find(+f: Nat, ls: List<&2, Lnd>) -> Maybe<&2, Lnd>:
  match ls:
    case Nil{}:
      None{}
    case +x <> t:
      lnd.find.at(Nat.is_eq(Lnd.f(x), f), x, lnd.find(f, t))

def lnd.less.at(hit: Bool, x: Lnd, t: List<&2, Lnd>, r: List<&2, Lnd>) -> List<&2, Lnd>:
  match hit:
    case True{}:
      match x:
        case Lnd{f, w}:
          Lnd{f, Nat.sub(w, 1n)} <> t
    case False{}:
      x <> r

# one joiner of flight f fewer waits
def lnd.less(+f: Nat, ls: List<&2, Lnd>) -> List<&2, Lnd>:
  match ls:
    case Nil{}:
      Nil{}
    case +x <> +t:
      lnd.less.at(Nat.is_eq(Lnd.f(x), f), x, t, lnd.less(f, t))

def lnd.drop.at(hit: Bool, x: Lnd, t: List<&2, Lnd>, r: List<&2, Lnd>) -> List<&2, Lnd>:
  match hit:
    case True{}:
      t
    case False{}:
      x <> r

# flight f is forgotten
def lnd.drop(+f: Nat, ls: List<&2, Lnd>) -> List<&2, Lnd>:
  match ls:
    case Nil{}:
      Nil{}
    case +x <> +t:
      lnd.drop.at(Nat.is_eq(Lnd.f(x), f), x, t, lnd.drop(f, t))

# board: join p's flight in flight, or start flight n and lead it
def book.board(m: Maybe<&2, Fly>, +p: String, +fs: List<&2, Fly>, ls: List<&2, Lnd>, +n: Nat) -> BRes:
  match m:
    case Some{x}:
      BRes{Book{fly.join(p, fs), ls, n}, OJoin{Fly.f(x)}}
    case None{}:
      BRes{Book{Fly{p, n, 0n} <> fs, ls, 1n+n}, OLead{n}}

def book.keep(k: Bool, +j: Nat, +f: Nat, fs: List<&2, Fly>, ls: List<&2, Lnd>, n: Nat) -> BRes:
  match k:
    case True{}:
      BRes{Book{fs, Lnd{f, j} <> lnd.drop(f, ls), n}, OKept{}}
    case False{}:
      BRes{Book{fs, ls, n}, ODropped{}}

# land: p's flight is no longer in flight; its outcome is kept for its
# joiners, under f (in place of any outcome kept under f), when it has any
def book.land(m: Maybe<&2, Fly>, +p: String, +f: Nat, +fs: List<&2, Fly>, ls: List<&2, Lnd>, n: Nat) -> BRes:
  match m:
    case Some{+x}:
      book.keep(Nat.is_lt(0n, Fly.j(x)), Fly.j(x), f, fly.drop(p, fs), ls, n)
    case None{}:
      BRes{Book{fs, ls, n}, ODropped{}}

def book.take(more: Bool, +f: Nat, fs: List<&2, Fly>, ls: List<&2, Lnd>, n: Nat) -> BRes:
  match more:
    case True{}:
      BRes{Book{fs, lnd.less(f, ls), n}, OTake{}}
    case False{}:
      BRes{Book{fs, lnd.drop(f, ls), n}, OTakeLast{}}

# wait: flight f's outcome once it landed; the last joiner to take it
# forgets it
def book.wait(m: Maybe<&2, Lnd>, +f: Nat, fs: List<&2, Fly>, +ls: List<&2, Lnd>, n: Nat) -> BRes:
  match m:
    case Some{x}:
      book.take(Nat.is_lt(1n, Lnd.w(x)), f, fs, ls, n)
    case None{}:
      BRes{Book{fs, ls, n}, ONotYet{}}

def book.joiners(m: Maybe<&2, Fly>) -> BOut:
  match m:
    case Some{x}:
      OJoiners{Some{Fly.j(x)}}
    case None{}:
      OJoiners{None{}}

# the book after the event e, and its answer
def book.step(b: Book, e: BEv) -> BRes:
  match b:
    case Book{+fs, +ls, +n}:
      match e:
        case EvBoard{+p}:
          book.board(fly.find(p, fs), p, fs, ls, n)
        case EvLand{+p, f}:
          book.land(fly.find(p, fs), p, f, fs, ls, n)
        case EvWait{+f}:
          book.wait(lnd.find(f, ls), f, fs, ls, n)
        case EvJoiners{+p}:
          BRes{Book{fs, ls, n}, book.joiners(fly.find(p, fs))}
