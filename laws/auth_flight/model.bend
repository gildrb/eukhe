# eukhe: the laws of area auth_flight: the model

import Base
import ../../bend/auth_flight.bend as F

# ---- auth_flight ----

# LAWS (A1): the OAuth refresh flight. Each law is an open claim about the
# model in bend/auth_flight.bend; PROOF.bend proves them (as
# AuthFlight.<law>) with the lemmas of proof/auth_flight/.

# (A1) One refresh flight per provider
# ------------------------------------
# The OAuth refresh of an expired stored credential
# (crates/eukhe-core/src/auth/flight.rs): the callers of one provider share
# one token fetch. The desk the Rust runs (laws/auth_flight/entry.bend and
# safety.bend) answers each caller the model's next leg
# (flight_step_is_model). Every input is free: any callers, their steps
# in any order, any fetch results, peer writes and expiries at any time.

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
# landed, no fetch made, and the store holding credential 0, expired
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
