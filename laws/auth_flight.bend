# eukhe: the laws of area auth_flight

import Base
import ../bend/auth_flight.bend as F
import ../bend/ffi_auth_flight.bend as FA
import ../bend/wire.bend as Wr
import ./base.bend as LawsBase

# ---- auth_flight ----

# LAWS (A1): the OAuth refresh flight. Each law is an open claim about the
# model in bend/auth_flight.bend; PROOF.bend proves them (as
# AuthFlight.<law>) with the lemmas of proof/auth_flight/.

# (A1) One refresh flight per provider
# ------------------------------------
# The OAuth refresh of an expired stored credential
# (crates/eukhe-core/src/auth/flight.rs): the callers of one provider share
# one token fetch. The bridge test crates/eukhe-core/src/auth/flight/bridge.rs
# runs the Rust dispatch over the compiled decisions (section A1, The
# decisions of the Rust refresh) and the model on the same interleavings.
# Every input is free: any callers, their steps in any order, any fetch
# results, peer writes and expiries at any time.

# LAW flight_one_fetch: at most one fetch is in flight
law flight_one_fetch:
  for +evs: List<&2, F.Ev>
  {F.le(F.fetching(F.St.cs(F.run(evs))), 1n) == True{} : Bool}

# LAW flight_board_joins: a caller that boards while flight f is in flight (caller j leads
# it) joins flight f
law flight_board_joins:
  for +evs: List<&2, F.Ev>
  for +j: Nat
  for +lj: F.Leg
  for +f: Nat
  for leads: {List.get(&2, F.Leg, F.St.cs(F.run(evs)), j) == Some{lj} : Maybe<&2, F.Leg>}
  for flight: {F.led(lj) == Some{f} : Maybe<&2, Nat>}
  for +k: Nat
  for +ok: Bool
  for boards: {List.get(&2, F.Leg, F.St.cs(F.run(evs)), k) == Some{F.Board{}} : Maybe<&2, F.Leg>}
  {List.get(&2, F.Leg, F.St.cs(F.step(F.run(evs), F.Step{k, ok})), k) == Some{F.Waiting{f}} : Maybe<&2, F.Leg>}

# LAW flight_callers_get_its_outcome: every caller of flight f (its leader, and each caller that joined
# it) gets the outcome flight f landed with
law flight_callers_get_its_outcome:
  for +evs: List<&2, F.Ev>
  for +k: Nat
  for +f: Nat
  for +o: F.Out
  for served: {List.get(&2, F.Leg, F.St.cs(F.run(evs)), k) == Some{F.Served{Some{f}, o}} : Maybe<&2, F.Leg>}
  {List.get(&2, F.Out, F.W.landed(F.St.w(F.run(evs))), f) == Some{o} : Maybe<&2, F.Out>}

# LAW flight_landed_serves: a caller that joined flight f takes its outcome at its next step
# once flight f landed
law flight_landed_serves:
  for +s: F.St
  for +k: Nat
  for +f: Nat
  for +o: F.Out
  for +ok: Bool
  for waits: {List.get(&2, F.Leg, F.St.cs(s), k) == Some{F.Waiting{f}} : Maybe<&2, F.Leg>}
  for landed: {List.get(&2, F.Out, F.W.landed(F.St.w(s)), f) == Some{o} : Maybe<&2, F.Out>}
  {List.get(&2, F.Leg, F.St.cs(F.step(s, F.Step{k, ok})), k) == Some{F.Served{Some{f}, o}} : Maybe<&2, F.Leg>}

# LAW flight_after_end_stored: a flight ends after its credential is stored: once caller k lands
# flight f with credential c, the store holds c or a newer credential, so a
# caller after the end sees the stored credential
law flight_after_end_stored:
  for +evs: List<&2, F.Ev>
  for +k: Nat
  for +f: Nat
  for +c: Nat
  for lands: {List.get(&2, F.Leg, F.St.cs(F.run(evs)), k) == Some{F.Land{f, F.Ok{c}}} : Maybe<&2, F.Leg>}
  for +ok: Bool
  {F.le(c, F.Sto.c(F.W.sto(F.St.w(F.step(F.run(evs), F.Step{k, ok}))))) == True{} : Bool}

# LAW flight_after_end_served: a caller after the end sees the stored credential: once caller k
# lands flight f with credential c, a caller that arrives while the store
# is fresh is served the stored credential, c or a newer one
law flight_after_end_served:
  for +evs: List<&2, F.Ev>
  for +k: Nat
  for +f: Nat
  for +c: Nat
  for lands: {List.get(&2, F.Leg, F.St.cs(F.run(evs)), k) == Some{F.Land{f, F.Ok{c}}} : Maybe<&2, F.Leg>}
  for +ok: Bool
  for +ok2: Bool
  for fresh: {F.Sto.fresh(F.W.sto(F.St.w(F.step(F.run(evs), F.Step{k, ok})))) == True{} : Bool}
  F.After(c, F.step(F.run(evs), F.Step{k, ok}), ok2)

# LAW flight_board_leads: a caller that boards while no flight is in flight starts the next
# flight (numbered by the flights landed so far) and leads it: its next leg
# is the leader's check, and a flight is now in flight
# EXCLUDES: a board that waits on a flight nobody leads (every expired
#   caller would then wait forever and nothing is fetched), a lead of a
#   flight number already used, a flight that starts without being in flight
law flight_board_leads:
  for +s: F.St
  for +k: Nat
  for +ok: Bool
  for boards: {List.get(&2, F.Leg, F.St.cs(s), k) == Some{F.Board{}} : Maybe<&2, F.Leg>}
  for free: {F.W.fl(F.St.w(s)) == False{} : Bool}
  {List.get(&2, F.Leg, F.St.cs(F.step(s, F.Step{k, ok})), k) == Some{F.Check{List.length(&2, F.Out, F.W.landed(F.St.w(s)))}} : Maybe<&2, F.Leg>} & {F.W.fl(F.St.w(F.step(s, F.Step{k, ok}))) == True{} : Bool}

# LAW flight_land_ends: a leader that lands flight f with outcome o is served o, the flight is
# no longer in flight, and o is landed after the outcomes landed before
# EXCLUDES: a land that leaves the flight in flight (every later expired
#   caller would join a flight nobody leads and wait forever), a land that
#   records no outcome, records it at another index or serves another one
law flight_land_ends:
  for +s: F.St
  for +k: Nat
  for +f: Nat
  for +o: F.Out
  for +ok: Bool
  for lands: {List.get(&2, F.Leg, F.St.cs(s), k) == Some{F.Land{f, o}} : Maybe<&2, F.Leg>}
  {List.get(&2, F.Leg, F.St.cs(F.step(s, F.Step{k, ok})), k) == Some{F.Served{Some{f}, o}} : Maybe<&2, F.Leg>} & {F.W.fl(F.St.w(F.step(s, F.Step{k, ok}))) == False{} : Bool} & {F.W.landed(F.St.w(F.step(s, F.Step{k, ok}))) == List.append(&2, F.Out, F.W.landed(F.St.w(s)), [o]) : List<&2, F.Out>}

# a leg that fetches counts 1, any other 0
def af_is_fetch(l: F.Leg) -> Nat:
  match l:
    case F.Load{}:
      0n
    case F.Board{}:
      0n
    case F.Check{f}:
      0n
    case F.Fetch{f}:
      1n
    case F.Store{f, c}:
      0n
    case F.Land{f, o}:
      0n
    case F.Waiting{f}:
      0n
    case F.Served{v, o}:
      0n

# the callers whose leg is a fetch
def af_fetching(cs: List<&2, F.Leg>) -> Nat:
  match cs:
    case Nil{}:
      0n
    case l <> t:
      Nat.add(af_is_fetch(l), af_fetching(t))

# the flight a leg leads: the leader's check, fetch, store and land
def af_led(l: F.Leg) -> Maybe<&2, Nat>:
  match l:
    case F.Load{}:
      None{}
    case F.Board{}:
      None{}
    case F.Check{f}:
      Some{f}
    case F.Fetch{f}:
      Some{f}
    case F.Store{f, c}:
      Some{f}
    case F.Land{f, o}:
      Some{f}
    case F.Waiting{f}:
      None{}
    case F.Served{v, o}:
      None{}

# LAW flight_terms_exact: the model's terms the A1 laws speak in are their meaning: `fetching`
# counts the callers whose leg is a fetch, `led` is the flight a leader's
# leg is on (none for a caller that does not lead)
# EXCLUDES: flight_one_fetch or flight_board_joins made vacuous by a
#   `fetching` that counts nothing or a `led` that names no flight
law flight_terms_exact:
  for +cs: List<&2, F.Leg>
  for +l: F.Leg
  {F.fetching(cs) == af_fetching(cs) : Nat} & {F.led(l) == af_led(l) : Maybe<&2, Nat>}

# The model's step, stated on its own

def am_load(fresh: Bool, +c: Nat, w: F.W) -> F.Adv:
  match fresh:
    case True{}:
      F.Adv{F.Served{None{}, F.Ok{c}}, w}
    case False{}:
      F.Adv{F.Board{}, w}

def am_board(fl: Bool, sto: F.Sto, +ld: List<&2, F.Out>, n: Nat) -> F.Adv:
  match fl:
    case True{}:
      F.Adv{F.Waiting{List.length(&2, F.Out, ld)}, F.W{sto, True{}, ld, n}}
    case False{}:
      F.Adv{F.Check{List.length(&2, F.Out, ld)}, F.W{sto, True{}, ld, n}}

def am_check(fresh: Bool, +f: Nat, +c: Nat, w: F.W) -> F.Adv:
  match fresh:
    case True{}:
      F.Adv{F.Land{f, F.Ok{c}}, w}
    case False{}:
      F.Adv{F.Fetch{f}, w}

def am_fetch(ok: Bool, +f: Nat, sto: F.Sto, fl: Bool, ld: List<&2, F.Out>, +n: Nat) -> F.Adv:
  match ok:
    case True{}:
      F.Adv{F.Store{f, 1n+n}, F.W{sto, fl, ld, 1n+n}}
    case False{}:
      F.Adv{F.Land{f, F.Err{1n+n}}, F.W{sto, fl, ld, 1n+n}}

def am_store(fresh: Bool, +f: Nat, +c: Nat, +p: Nat, fl: Bool, ld: List<&2, F.Out>, n: Nat) -> F.Adv:
  match fresh:
    case True{}:
      F.Adv{F.Land{f, F.Ok{p}}, F.W{F.Sto{p, True{}}, fl, ld, n}}
    case False{}:
      F.Adv{F.Land{f, F.Ok{c}}, F.W{F.Sto{c, True{}}, fl, ld, n}}

def am_wait(m: Maybe<&2, F.Out>, +f: Nat, w: F.W) -> F.Adv:
  match m:
    case None{}:
      F.Adv{F.Waiting{f}, w}
    case Some{o}:
      F.Adv{F.Served{Some{f}, o}, w}

# a caller's step from leg l in the world W{Sto{c, fresh}, fl, ld, n} (a
# fetch at it succeeds when ok): a load serves a fresh credential and
# boards on an expired one; a board joins the flight in flight or leads
# flight |ld|, and a flight is in flight; the leader's check lands on a
# fresh credential and fetches otherwise; a fetch is the next credential
# or failure; a store keeps a peer's fresh credential, else stores the
# fetched one, and lands; a land serves its outcome, ends the flight and
# appends the outcome; a wait takes its flight's landed outcome; a served
# caller stays served
def am_adv(l: F.Leg, ok: Bool, +c: Nat, +fresh: Bool, +fl: Bool, +ld: List<&2, F.Out>, +n: Nat) -> F.Adv:
  match l:
    case F.Load{}:
      am_load(fresh, c, F.W{F.Sto{c, fresh}, fl, ld, n})
    case F.Board{}:
      am_board(fl, F.Sto{c, fresh}, ld, n)
    case F.Check{f}:
      am_check(fresh, f, c, F.W{F.Sto{c, fresh}, fl, ld, n})
    case F.Fetch{f}:
      am_fetch(ok, f, F.Sto{c, fresh}, fl, ld, n)
    case F.Store{f, p}:
      am_store(fresh, f, p, c, fl, ld, n)
    case F.Land{f, +o}:
      F.Adv{F.Served{Some{f}, o}, F.W{F.Sto{c, fresh}, False{}, List.append(&2, F.Out, ld, [o]), n}}
    case F.Waiting{+f}:
      am_wait(List.get(&2, F.Out, ld, f), f, F.W{F.Sto{c, fresh}, fl, ld, n})
    case F.Served{v, o}:
      F.Adv{F.Served{v, o}, F.W{F.Sto{c, fresh}, fl, ld, n}}

# caller k takes the leg of its step, the others keep theirs
def am_put(+k: Nat, a: F.Adv, +cs: List<&2, F.Leg>) -> F.St:
  match a:
    case F.Adv{l, w}:
      F.St{w, List.append(&2, F.Leg, List.take(&2, F.Leg, cs, k), l <> List.drop(&2, F.Leg, cs, 1n+k))}

def am_at(m: Maybe<&2, F.Leg>, +k: Nat, ok: Bool, +c: Nat, +fresh: Bool, +fl: Bool, +ld: List<&2, F.Out>, +n: Nat, +cs: List<&2, F.Leg>) -> F.St:
  match m:
    case None{}:
      F.St{F.W{F.Sto{c, fresh}, fl, ld, n}, cs}
    case Some{l}:
      am_put(k, am_adv(l, ok, c, fresh, fl, ld, n), cs)

# the model's state after event e: a caller arrives at its load; caller k
# (when there is one) takes its step; a peer stores a fresh credential
# one newer than the stored one; the stored credential expires
def am_step(s: F.St, e: F.Ev) -> F.St:
  match s:
    case F.St{w, +cs}:
      match w:
        case F.W{sto, +fl, +ld, +n}:
          match sto:
            case F.Sto{+c, +fresh}:
              match e:
                case F.Arrive{}:
                  F.St{F.W{F.Sto{c, fresh}, fl, ld, n}, List.append(&2, F.Leg, cs, [F.Load{}])}
                case F.Step{+k, ok}:
                  am_at(List.get(&2, F.Leg, cs, k), k, ok, c, fresh, fl, ld, n, cs)
                case F.Peer{}:
                  F.St{F.W{F.Sto{1n+c, True{}}, fl, ld, n}, cs}
                case F.Expire{}:
                  F.St{F.W{F.Sto{c, False{}}, fl, ld, n}, cs}

# LAW flight_step_exact: every event moves the model exactly as stated on its own (am_step):
# every caller's step, every arrival, peer write and expiry, from any state
# EXCLUDES: a step the A1 laws do not reach (a board, land, check, fetch,
#   store or wait that strands callers, an arrival that skips the load, a
#   peer write or expiry that does nothing), so a wrong model cannot pass
#   the A1 laws by never reaching the states they speak of
law flight_step_exact:
  for +s: F.St
  for +e: F.Ev
  {F.step(s, e) == am_step(s, e) : F.St}

# LAW flight_new_example: anchor: a world starts with no caller, no flight in flight, none
# landed, no fetch made, and the store holding credential 0, expired (the
# bridge's new world)
# EXCLUDES: a model whose runs start from a fresh store or a flight in flight
law flight_new_example:
  {F.St.new() == F.St{F.W{F.Sto{0n, False{}}, False{}, Nil{}, 0n}, Nil{}} : F.St}

# LAW flight_store_terms_exact: the store's accessors the A1 laws read (flight_after_end_served's
# premise) are its fields: the stored credential and whether it is fresh
# EXCLUDES: flight_after_end_served made vacuous by a `Sto.fresh` that is
#   never True
law flight_store_terms_exact:
  for +c: Nat
  for +f: Bool
  {F.Sto.fresh(F.Sto{c, f}) == f : Bool} & {F.Sto.c(F.Sto{c, f}) == c : Nat}

# (A1) The decisions of the Rust refresh, run as compiled Bend
# ------------------------------------------------------------
# The Rust refresh (crates/eukhe-core/src/auth/flight.rs) runs each caller
# on its own thread and moves the bytes: the document, the token
# endpoint, the credentials. After each read, fetch or write it asks the
# entry (bend/ffi_auth_flight.bend, a call) which leg follows; each step
# on the flights of a document it asks the document's book (the entry's
# stepper). No Rust copy of either decision. The thread interleaving stays
# in the Rust (the mutex, the condvar, the unwind that lands a flight): the
# bridge test runs it over these decisions against the model.
#
# The spec below spells requests, events and replies with the wire
# primitives (bend/wire.bend), never with the entry's own codec, and
# states each decision on its own.

# The call: the leg after a step

# the request Rust writes for what a step found
def af_spell_io(io: F.Io) -> String:
  match io:
    case F.LoadFresh{}:
      Wr.put_nat(0n, "")
    case F.LoadExpired{}:
      Wr.put_nat(1n, "")
    case F.LoadFailed{}:
      Wr.put_nat(2n, "")
    case F.CheckFresh{f}:
      Wr.put_nat(3n, Wr.put_nat(f, ""))
    case F.CheckExpired{f}:
      Wr.put_nat(4n, Wr.put_nat(f, ""))
    case F.FetchOk{f}:
      Wr.put_nat(5n, Wr.put_nat(f, ""))
    case F.FetchFailed{f}:
      Wr.put_nat(6n, Wr.put_nat(f, ""))
    case F.Stored{f}:
      Wr.put_nat(7n, Wr.put_nat(f, ""))

# its flight fits the wire
def af_io_fits(io: F.Io) -> Bool:
  match io:
    case F.LoadFresh{}:
      True{}
    case F.LoadExpired{}:
      True{}
    case F.LoadFailed{}:
      True{}
    case F.CheckFresh{f}:
      LawsBase.wire_fits(f)
    case F.CheckExpired{f}:
      LawsBase.wire_fits(f)
    case F.FetchOk{f}:
      LawsBase.wire_fits(f)
    case F.FetchFailed{f}:
      LawsBase.wire_fits(f)
    case F.Stored{f}:
      LawsBase.wire_fits(f)

# the reply: a fresh credential at the load, or no refresh at all, ends the
# refresh (0 is board, 4 done); an expired one boards; the leader's check
# lands its flight on a fresh credential and fetches otherwise (3 land, 1
# fetch); a fetched credential is stored (2), a failed fetch lands; the
# store lands the flight; each on the flight it is on
def af_reply_io(io: F.Io) -> String:
  match io:
    case F.LoadFresh{}:
      Wr.put_nat(4n, "")
    case F.LoadExpired{}:
      Wr.put_nat(0n, "")
    case F.LoadFailed{}:
      Wr.put_nat(4n, "")
    case F.CheckFresh{f}:
      Wr.put_nat(3n, Wr.put_nat(f, ""))
    case F.CheckExpired{f}:
      Wr.put_nat(1n, Wr.put_nat(f, ""))
    case F.FetchOk{f}:
      Wr.put_nat(2n, Wr.put_nat(f, ""))
    case F.FetchFailed{f}:
      Wr.put_nat(3n, Wr.put_nat(f, ""))
    case F.Stored{f}:
      Wr.put_nat(3n, Wr.put_nat(f, ""))

def af_io_of(t: Nat, f: Nat, s: String) -> Wr.Dec<F.Io>:
  match t:
    case 0n:
      Wr.Bad{}
    case 1n:
      Wr.Bad{}
    case 2n:
      Wr.Bad{}
    case 3n:
      Wr.Got{F.CheckFresh{f}, s}
    case 4n:
      Wr.Got{F.CheckExpired{f}, s}
    case 5n:
      Wr.Got{F.FetchOk{f}, s}
    case 6n:
      Wr.Got{F.FetchFailed{f}, s}
    case 7n:
      Wr.Got{F.Stored{f}, s}
    case 8n+q:
      Wr.Bad{}

def af_read_io.flight(t: Nat, r: Wr.Dec<Nat>) -> Wr.Dec<F.Io>:
  match r:
    case Wr.Got{f, s}:
      af_io_of(t, f, s)
    case Wr.Bad{}:
      Wr.Bad{}

def af_read_io.tag(t: Nat, s: String) -> Wr.Dec<F.Io>:
  match t:
    case 0n:
      Wr.Got{F.LoadFresh{}, s}
    case 1n:
      Wr.Got{F.LoadExpired{}, s}
    case 2n:
      Wr.Got{F.LoadFailed{}, s}
    case 3n+p:
      af_read_io.flight(3n+p, Wr.get_nat(s))

def af_read_io.go(r: Wr.Dec<Nat>) -> Wr.Dec<F.Io>:
  match r:
    case Wr.Got{t, s}:
      af_read_io.tag(t, s)
    case Wr.Bad{}:
      Wr.Bad{}

def af_whole(-A: Data, whole: Bool, x: A) -> Maybe<&2, A>:
  match whole:
    case True{}:
      Some{x}
    case False{}:
      None{}

def af_read_io.whole(r: Wr.Dec<F.Io>) -> Maybe<&2, F.Io>:
  match r:
    case Wr.Got{io, s}:
      af_whole(F.Io, Wr.end(s), io)
    case Wr.Bad{}:
      None{}

# what a step found, when s is exactly one request
def af_read_io(s: String) -> Maybe<&2, F.Io>:
  af_read_io.whole(af_read_io.go(Wr.get_nat(s)))

# LAW flight_ffi_answers: on every request Rust writes (its flight within the wire), the call
# answers the leg that follows: an expired credential at the load boards; a
# fresh one, or no refresh at all, is done; the check lands the flight on a
# fresh credential and fetches otherwise; a fetched credential is stored, a
# failed fetch lands; the store lands; each on the flight the step was on
# EXCLUDES: a misread step or flight, a leg out of order (a fetch on a
#   fresh credential, a store of a failure, a store that does not land), a
#   leg on another flight
law flight_ffi_answers:
  for +io: F.Io
  for fits: {af_io_fits(io) == True{} : Bool}
  {FA.ffi(af_spell_io(io)) == af_reply_io(io) : String}

# LAW flight_ffi_reads: every input that is exactly one request (as the wire primitives read
# it) gets the leg after its step
# EXCLUDES: a reply on another reading of the input
law flight_ffi_reads:
  for +s: String
  for +io: F.Io
  for got: {af_read_io(s) == Some{io} : Maybe<&2, F.Io>}
  {FA.ffi(s) == af_reply_io(io) : String}

# LAW flight_ffi_malformed_exact: every input that is not exactly one request gets exactly the
# error form 'E ', then "auth_flight: malformed request"
# EXCLUDES: a guessed leg for garbage, a request with input after it
#   answered
law flight_ffi_malformed_exact:
  for +s: String
  for no: {af_read_io(s) == None{} : Maybe<&2, F.Io>}
  {FA.ffi(s) == SCon{'E', SCon{' ', "auth_flight: malformed request"}} : String}

# LAW flight_next_load_is_model: the leg the call answers after a load is the model's (adv.load) on
# a fresh and on an expired stored credential
# EXCLUDES: a call whose load step is not the one the A1 laws are proved of
law flight_next_load_is_model:
  for +c: Nat
  for +w: F.W
  {F.shape(F.Adv.l(F.adv.load(F.Sto{c, True{}}, w))) == Some{F.next(F.LoadFresh{})} : Maybe<&2, F.Next>} & {F.shape(F.Adv.l(F.adv.load(F.Sto{c, False{}}, w))) == Some{F.next(F.LoadExpired{})} : Maybe<&2, F.Next>}

# LAW flight_next_check_is_model: the leg the call answers after the leader's check is the
# model's (adv.check)
# EXCLUDES: a call whose check step is not the one the A1 laws are proved of
law flight_next_check_is_model:
  for +f: Nat
  for +c: Nat
  for +w: F.W
  {F.shape(F.Adv.l(F.adv.check(f, F.Sto{c, True{}}, w))) == Some{F.next(F.CheckFresh{f})} : Maybe<&2, F.Next>} & {F.shape(F.Adv.l(F.adv.check(f, F.Sto{c, False{}}, w))) == Some{F.next(F.CheckExpired{f})} : Maybe<&2, F.Next>}

# LAW flight_next_fetch_is_model: the leg the call answers after a fetch is the model's
# (adv.fetch), on a fetched credential and on a failure
# EXCLUDES: a call whose fetch step is not the one the A1 laws are proved of
law flight_next_fetch_is_model:
  for +f: Nat
  for +w: F.W
  {F.shape(F.Adv.l(F.adv.fetch(f, w, True{}))) == Some{F.next(F.FetchOk{f})} : Maybe<&2, F.Next>} & {F.shape(F.Adv.l(F.adv.fetch(f, w, False{}))) == Some{F.next(F.FetchFailed{f})} : Maybe<&2, F.Next>}

# LAW flight_next_store_is_model: the leg the call answers after the store is the model's
# (adv.store): the flight lands, whether the fetched credential or a
# peer's stands
# EXCLUDES: a call whose store step is not the one the A1 laws are proved of
law flight_next_store_is_model:
  for +f: Nat
  for +c: Nat
  for +w: F.W
  {F.shape(F.Adv.l(F.adv.store(f, c, w))) == Some{F.next(F.Stored{f})} : Maybe<&2, F.Next>}

# LAW flight_ffi_example: anchor: the strings Rust writes and the replies it reads for each
# step; an unknown step and input left over are refused
# EXCLUDES: a tag numbering other than Rust's
law flight_ffi_example:
  {[FA.ffi("0,"), FA.ffi("1,"), FA.ffi("2,"), FA.ffi("3,7,"), FA.ffi("4,7,"), FA.ffi("5,7,"), FA.ffi("6,7,"), FA.ffi("7,7,")] == ["4,", "0,", "4,", "3,7,", "1,7,", "2,7,", "3,7,", "3,7,"] : List<&2, String>} &
  {[FA.ffi("8,7,"), FA.ffi("3,7,x")] == [Wr.err("auth_flight: malformed request"), Wr.err("auth_flight: malformed request")] : List<&2, String>}

# The stepper: the book of a document's flights

# the event Rust writes
def af_spell_ev(e: F.BEv) -> String:
  match e:
    case F.EvBoard{p}:
      Wr.put_nat(0n, Wr.put_str(p, ""))
    case F.EvLand{p, f}:
      Wr.put_nat(1n, Wr.put_str(p, Wr.put_nat(f, "")))
    case F.EvWait{f}:
      Wr.put_nat(2n, Wr.put_nat(f, ""))
    case F.EvJoiners{p}:
      Wr.put_nat(3n, Wr.put_str(p, ""))

# its provider's length and its flight fit the wire
def af_ev_fits(e: F.BEv) -> Bool:
  match e:
    case F.EvBoard{p}:
      LawsBase.wire_fits(String.length(p))
    case F.EvLand{p, f}:
      Bool.and(LawsBase.wire_fits(String.length(p)), LawsBase.wire_fits(f))
    case F.EvWait{f}:
      LawsBase.wire_fits(f)
    case F.EvJoiners{p}:
      LawsBase.wire_fits(String.length(p))

# the book's answer, spelled: 0 lead, 1 join (then the flight), 2 kept, 3
# dropped, 4 not yet, 5 take, 6 take last, 7 joiners (then 0, for none or
# 1, and the count)
def af_spell_out(o: F.BOut) -> String:
  match o:
    case F.OLead{f}:
      Wr.put_nat(0n, Wr.put_nat(f, ""))
    case F.OJoin{f}:
      Wr.put_nat(1n, Wr.put_nat(f, ""))
    case F.OKept{}:
      Wr.put_nat(2n, "")
    case F.ODropped{}:
      Wr.put_nat(3n, "")
    case F.ONotYet{}:
      Wr.put_nat(4n, "")
    case F.OTake{}:
      Wr.put_nat(5n, "")
    case F.OTakeLast{}:
      Wr.put_nat(6n, "")
    case F.OJoiners{m}:
      match m:
        case None{}:
          Wr.put_nat(7n, Wr.put_nat(0n, ""))
        case Some{j}:
          Wr.put_nat(7n, Wr.put_nat(1n, Wr.put_nat(j, "")))

def af_read_ev.land(p: String, r: Wr.Dec<Nat>) -> Wr.Dec<F.BEv>:
  match r:
    case Wr.Got{f, s}:
      Wr.Got{F.EvLand{p, f}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def af_read_ev.board(r: Wr.Dec<String>) -> Wr.Dec<F.BEv>:
  match r:
    case Wr.Got{p, s}:
      Wr.Got{F.EvBoard{p}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def af_read_ev.landed(r: Wr.Dec<String>) -> Wr.Dec<F.BEv>:
  match r:
    case Wr.Got{p, s}:
      af_read_ev.land(p, Wr.get_nat(s))
    case Wr.Bad{}:
      Wr.Bad{}

def af_read_ev.wait(r: Wr.Dec<Nat>) -> Wr.Dec<F.BEv>:
  match r:
    case Wr.Got{f, s}:
      Wr.Got{F.EvWait{f}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def af_read_ev.joiners(r: Wr.Dec<String>) -> Wr.Dec<F.BEv>:
  match r:
    case Wr.Got{p, s}:
      Wr.Got{F.EvJoiners{p}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def af_read_ev.tag(t: Nat, s: String) -> Wr.Dec<F.BEv>:
  match t:
    case 0n:
      af_read_ev.board(Wr.get_str(s))
    case 1n:
      af_read_ev.landed(Wr.get_str(s))
    case 2n:
      af_read_ev.wait(Wr.get_nat(s))
    case 3n:
      af_read_ev.joiners(Wr.get_str(s))
    case 4n+p:
      Wr.Bad{}

def af_read_ev.go(r: Wr.Dec<Nat>) -> Wr.Dec<F.BEv>:
  match r:
    case Wr.Got{t, s}:
      af_read_ev.tag(t, s)
    case Wr.Bad{}:
      Wr.Bad{}

def af_read_ev.whole(r: Wr.Dec<F.BEv>) -> Maybe<&2, F.BEv>:
  match r:
    case Wr.Got{e, s}:
      af_whole(F.BEv, Wr.end(s), e)
    case Wr.Bad{}:
      None{}

# the event s is, when s is exactly one event
def af_read_ev(s: String) -> Maybe<&2, F.BEv>:
  af_read_ev.whole(af_read_ev.go(Wr.get_nat(s)))

# The book, stated on its own

def af_is(+p: String, x: F.Fly) -> Bool:
  match x:
    case F.Fly{q, f, j}:
      String.eq(q, p)

def af_fly.pick(hit: Bool, x: F.Fly, r: Maybe<&2, F.Fly>) -> Maybe<&2, F.Fly>:
  match hit:
    case True{}:
      Some{x}
    case False{}:
      r

# the first flight in flight of provider p
def af_fly(+p: String, fs: List<&2, F.Fly>) -> Maybe<&2, F.Fly>:
  match fs:
    case Nil{}:
      None{}
    case +x <> t:
      af_fly.pick(af_is(p, x), x, af_fly(p, t))

def af_bump.pick(hit: Bool, x: F.Fly, t: List<&2, F.Fly>, r: List<&2, F.Fly>) -> List<&2, F.Fly>:
  match hit:
    case True{}:
      match x:
        case F.Fly{q, f, j}:
          F.Fly{q, f, 1n+j} <> t
    case False{}:
      x <> r

# the flights with one more joiner on the first of provider p
def af_bump(+p: String, fs: List<&2, F.Fly>) -> List<&2, F.Fly>:
  match fs:
    case Nil{}:
      Nil{}
    case +x <> +t:
      af_bump.pick(af_is(p, x), x, t, af_bump(p, t))

def af_unfly.pick(hit: Bool, x: F.Fly, t: List<&2, F.Fly>, r: List<&2, F.Fly>) -> List<&2, F.Fly>:
  match hit:
    case True{}:
      t
    case False{}:
      x <> r

# the flights without the first of provider p
def af_unfly(+p: String, fs: List<&2, F.Fly>) -> List<&2, F.Fly>:
  match fs:
    case Nil{}:
      Nil{}
    case +x <> +t:
      af_unfly.pick(af_is(p, x), x, t, af_unfly(p, t))

def af_on(+f: Nat, x: F.Lnd) -> Bool:
  match x:
    case F.Lnd{g, w}:
      Nat.is_eq(g, f)

def af_landed.pick(hit: Bool, x: F.Lnd, r: Maybe<&2, F.Lnd>) -> Maybe<&2, F.Lnd>:
  match hit:
    case True{}:
      Some{x}
    case False{}:
      r

# the first landed flight f
def af_landed(+f: Nat, ls: List<&2, F.Lnd>) -> Maybe<&2, F.Lnd>:
  match ls:
    case Nil{}:
      None{}
    case +x <> t:
      af_landed.pick(af_on(f, x), x, af_landed(f, t))

def af_one_less.pick(hit: Bool, x: F.Lnd, t: List<&2, F.Lnd>, r: List<&2, F.Lnd>) -> List<&2, F.Lnd>:
  match hit:
    case True{}:
      match x:
        case F.Lnd{g, w}:
          F.Lnd{g, Nat.sub(w, 1n)} <> t
    case False{}:
      x <> r

# the landed flights with one waiting joiner fewer on the first f
def af_one_less(+f: Nat, ls: List<&2, F.Lnd>) -> List<&2, F.Lnd>:
  match ls:
    case Nil{}:
      Nil{}
    case +x <> +t:
      af_one_less.pick(af_on(f, x), x, t, af_one_less(f, t))

def af_unland.pick(hit: Bool, x: F.Lnd, t: List<&2, F.Lnd>, r: List<&2, F.Lnd>) -> List<&2, F.Lnd>:
  match hit:
    case True{}:
      t
    case False{}:
      x <> r

# the landed flights without the first f
def af_unland(+f: Nat, ls: List<&2, F.Lnd>) -> List<&2, F.Lnd>:
  match ls:
    case Nil{}:
      Nil{}
    case +x <> +t:
      af_unland.pick(af_on(f, x), x, t, af_unland(f, t))

def af_board(m: Maybe<&2, F.Fly>, +p: String, +fs: List<&2, F.Fly>, ls: List<&2, F.Lnd>, +n: Nat) -> F.BRes:
  match m:
    case Some{x}:
      match x:
        case F.Fly{q, f, j}:
          F.BRes{F.Book{af_bump(p, fs), ls, n}, F.OJoin{f}}
    case None{}:
      F.BRes{F.Book{F.Fly{p, n, 0n} <> fs, ls, 1n+n}, F.OLead{n}}

def af_land(m: Maybe<&2, F.Fly>, +p: String, +f: Nat, +fs: List<&2, F.Fly>, +ls: List<&2, F.Lnd>, n: Nat) -> F.BRes:
  match m:
    case Some{x}:
      match x:
        case F.Fly{q, g, j}:
          match j:
            case 0n:
              F.BRes{F.Book{af_unfly(p, fs), ls, n}, F.ODropped{}}
            case 1n+i:
              F.BRes{F.Book{af_unfly(p, fs), F.Lnd{f, 1n+i} <> af_unland(f, ls), n}, F.OKept{}}
    case None{}:
      F.BRes{F.Book{fs, ls, n}, F.ODropped{}}

def af_wait(m: Maybe<&2, F.Lnd>, +f: Nat, fs: List<&2, F.Fly>, +ls: List<&2, F.Lnd>, n: Nat) -> F.BRes:
  match m:
    case Some{x}:
      match x:
        case F.Lnd{g, w}:
          match w:
            case 0n:
              F.BRes{F.Book{fs, af_unland(f, ls), n}, F.OTakeLast{}}
            case 1n:
              F.BRes{F.Book{fs, af_unland(f, ls), n}, F.OTakeLast{}}
            case 2n+v:
              F.BRes{F.Book{fs, af_one_less(f, ls), n}, F.OTake{}}
    case None{}:
      F.BRes{F.Book{fs, ls, n}, F.ONotYet{}}

def af_joiners(m: Maybe<&2, F.Fly>) -> F.BOut:
  match m:
    case Some{x}:
      match x:
        case F.Fly{q, f, j}:
          F.OJoiners{Some{j}}
    case None{}:
      F.OJoiners{None{}}

# the book after event e, and its answer: a board joins the provider's
# flight in flight (one more joiner) or starts flight n, leads it and
# counts it; a land takes the provider's flight out of flight and keeps
# the outcome under the landed flight for its joiners (in place of any
# kept under that flight) when it had any; a wait takes a landed flight's
# outcome, the last of its joiners forgets it, and a flight not landed
# waits; joiners counts the provider's flight's joiners
def af_book(b: F.Book, e: F.BEv) -> F.BRes:
  match b:
    case F.Book{+fs, +ls, +n}:
      match e:
        case F.EvBoard{+p}:
          af_board(af_fly(p, fs), p, fs, ls, n)
        case F.EvLand{+p, +f}:
          af_land(af_fly(p, fs), p, f, fs, ls, n)
        case F.EvWait{+f}:
          af_wait(af_landed(f, ls), f, fs, ls, n)
        case F.EvJoiners{+p}:
          F.BRes{F.Book{fs, ls, n}, af_joiners(af_fly(p, fs))}

def af_step_of(r: F.BRes) -> FA.St & String:
  match r:
    case F.BRes{b, o}:
      (FA.Open{b}, af_spell_out(o))

# LAW flight_open_empty: the stepper opens on the empty input with an empty book (no flight
# in flight, none landed, none started) and the empty reply
# EXCLUDES: a book that starts with flights, or numbers from another start
law flight_open_empty:
  {FA.open("") == (FA.Open{F.Book{Nil{}, Nil{}, 0n}}, "") : FA.St & String}

# LAW flight_open_refuses: any other open is refused with exactly the error form, and the
# refused stepper answers every event with exactly the error form
# EXCLUDES: a book opened on input Rust never writes, a refused stepper
#   that decides
law flight_open_refuses:
  for +s: String
  for ne: {String.is_empty(s) == False{} : Bool}
  for +e: String
  {FA.open(s) == (FA.Shut{}, SCon{'E', SCon{' ', "auth_flight: malformed open"}}) : FA.St & String} & {FA.step(FA.Shut{}, e) == (FA.Shut{}, SCon{'E', SCon{' ', "auth_flight: the open was refused"}}) : FA.St & String}

# LAW flight_step_answers: on every event Rust writes (within the wire), from every book, the
# stepper's book and answer are the book's (af_book), spelled
# EXCLUDES: a misread event, provider or flight; a board that starts a
#   second flight for a provider in flight, or joins another provider's; a
#   flight number reused or skipped; a land that keeps the provider in
#   flight, keeps an outcome no joiner waits for or forgets one a joiner
#   waits for; a wait served before its flight landed, an outcome
#   forgotten before its last joiner took it or kept after; a wrong count
law flight_step_answers:
  for +b: F.Book
  for +e: F.BEv
  for fits: {af_ev_fits(e) == True{} : Bool}
  {FA.step(FA.Open{b}, af_spell_ev(e)) == af_step_of(af_book(b, e)) : FA.St & String}

# LAW flight_step_reads: every input that is exactly one event (as the wire primitives read
# it) gets the book's answer to it
# EXCLUDES: a decision on another reading of the input
law flight_step_reads:
  for +b: F.Book
  for +s: String
  for +e: F.BEv
  for got: {af_read_ev(s) == Some{e} : Maybe<&2, F.BEv>}
  {FA.step(FA.Open{b}, s) == af_step_of(af_book(b, e)) : FA.St & String}

# LAW flight_step_malformed_exact: every input that is not exactly one event keeps the book and
# answers exactly the error form 'E ', then "auth_flight: malformed event"
# EXCLUDES: a guessed event, a book changed by garbage, an event with input
#   after it decided
law flight_step_malformed_exact:
  for +b: F.Book
  for +s: String
  for no: {af_read_ev(s) == None{} : Maybe<&2, F.BEv>}
  {FA.step(FA.Open{b}, s) == (FA.Open{b}, SCon{'E', SCon{' ', "auth_flight: malformed event"}}) : FA.St & String}

# LAW flight_step_example: anchor: the strings Rust writes and reads: two callers of x board
# (flight 0, led, then joined), one of y starts flight 1, x's flight lands
# with its joiner (kept), the joiner takes it (the last), y's flight lands
# with none (dropped), a third x caller leads flight 2; a bad tag is
# refused
# EXCLUDES: a tag numbering or field order other than Rust's
law flight_step_example:
  {FA.step(FA.Open{F.Book{Nil{}, Nil{}, 0n}}, "0,1,x") == (FA.Open{F.Book{[F.Fly{"x", 0n, 0n}], Nil{}, 1n}}, "0,0,") : FA.St & String} &
  {FA.step(FA.Open{F.Book{[F.Fly{"x", 0n, 0n}], Nil{}, 1n}}, "0,1,x") == (FA.Open{F.Book{[F.Fly{"x", 0n, 1n}], Nil{}, 1n}}, "1,0,") : FA.St & String} &
  {FA.step(FA.Open{F.Book{[F.Fly{"x", 0n, 1n}], Nil{}, 1n}}, "3,1,x") == (FA.Open{F.Book{[F.Fly{"x", 0n, 1n}], Nil{}, 1n}}, "7,1,1,") : FA.St & String} &
  {FA.step(FA.Open{F.Book{[F.Fly{"x", 0n, 1n}], Nil{}, 1n}}, "0,1,y") == (FA.Open{F.Book{[F.Fly{"y", 1n, 0n}, F.Fly{"x", 0n, 1n}], Nil{}, 2n}}, "0,1,") : FA.St & String} &
  {FA.step(FA.Open{F.Book{[F.Fly{"y", 1n, 0n}, F.Fly{"x", 0n, 1n}], Nil{}, 2n}}, "1,1,x0,") == (FA.Open{F.Book{[F.Fly{"y", 1n, 0n}], [F.Lnd{0n, 1n}], 2n}}, "2,") : FA.St & String} &
  {FA.step(FA.Open{F.Book{[F.Fly{"y", 1n, 0n}], [F.Lnd{0n, 1n}], 2n}}, "2,0,") == (FA.Open{F.Book{[F.Fly{"y", 1n, 0n}], Nil{}, 2n}}, "6,") : FA.St & String} &
  {FA.step(FA.Open{F.Book{[F.Fly{"y", 1n, 0n}], Nil{}, 2n}}, "1,1,y1,") == (FA.Open{F.Book{Nil{}, Nil{}, 2n}}, "3,") : FA.St & String} &
  {FA.step(FA.Open{F.Book{Nil{}, Nil{}, 2n}}, "0,1,x") == (FA.Open{F.Book{[F.Fly{"x", 2n, 0n}], Nil{}, 3n}}, "0,2,") : FA.St & String} &
  {FA.step(FA.Open{F.Book{Nil{}, Nil{}, 2n}}, "9,") == (FA.Open{F.Book{Nil{}, Nil{}, 2n}}, Wr.err("auth_flight: malformed event")) : FA.St & String}
