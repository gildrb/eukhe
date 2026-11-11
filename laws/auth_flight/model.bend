# eukhe: the laws of area auth_flight: the model

import Base
import ../../bend/auth_flight.bend as F

# ---- auth_flight ----

# LAWS (A1): the model of the OAuth refresh flight (bend/auth_flight.bend:
# Leg, W, St, step). Requirements A1.1, A1.2, A1.3, A1.4, A1.7 (table:
# laws/auth_flight/entry.bend). Each law is an open claim about the
# model's step F.step, from any state or folded over any events from a
# new world (am_run, stated below); PROOF.bend proves them (as
# AuthFlight.<law>) with the lemmas of proof/auth_flight/. The desk the
# Rust runs answers each caller the model's next leg (flight_step_is_model,
# laws/auth_flight/entry.bend). Every input is free: any callers, their
# steps in any order, any fetch results, peer writes and expiries at any
# time.

# Terms
# -----

# the world after the events evs from s: each event one F.step, in order
def am_go(evs: List<&2, F.Ev>, s: F.St) -> F.St:
  match evs:
    case Nil{}:
      s
    case e <> rest:
      am_go(rest, F.step(s, e))

# the world after the events evs from a new world: no caller, no flight
# in flight, none landed, no fetch made, the store holding credential 0,
# expired
def am_run(evs: List<&2, F.Ev>) -> F.St:
  am_go(evs, F.St{F.W{F.Sto{0n, False{}}, False{}, Nil{}, 0n}, Nil{}})

# 1 for True, 0 for False
def am_bit(b: Bool) -> Nat:
  match b:
    case True{}:
      1n
    case False{}:
      0n

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

# 1 for a leg that leads a flight
def af_leads_bit(m: Maybe<&2, Nat>) -> Nat:
  match m:
    case None{}:
      0n
    case Some{f}:
      1n

# how many callers lead a flight
def af_leaders(cs: List<&2, F.Leg>) -> Nat:
  match cs:
    case Nil{}:
      0n
    case l <> t:
      Nat.add(af_leads_bit(af_led(l)), af_leaders(t))

# the flight m a leg leads, if any, is f
def af_on(+f: Nat, m: Maybe<&2, Nat>) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{g}:
      Nat.is_eq(g, f)

# every caller of cs that leads a flight leads flight f
def af_all_on(+f: Nat, cs: List<&2, F.Leg>) -> Bool:
  match cs:
    case Nil{}:
      True{}
    case l <> t:
      Bool.and(af_on(f, af_led(l)), af_all_on(f, t))

# the leg a caller that arrives in s holds after its first step (a fetch
# at it succeeds when ok)
def af_late(+s: F.St, ok: Bool) -> Maybe<&2, F.Leg>:
  +k = List.length(&2, F.Leg, F.St.cs(s))
  List.get(&2, F.Leg, F.St.cs(F.step(F.step(s, F.Arrive{}), F.Step{k, ok})), k)

# how far a leg is from its end: a load 6, a board 5, the leader's check
# 4, fetch 3, store 2, land 1, a wait 1, served 0
def af_rank(l: F.Leg) -> Nat:
  match l:
    case F.Load{}:
      6n
    case F.Board{}:
      5n
    case F.Check{f}:
      4n
    case F.Fetch{f}:
      3n
    case F.Store{f, c}:
      2n
    case F.Land{f, o}:
      1n
    case F.Waiting{f}:
      1n
    case F.Served{v, o}:
      0n

# the rank of a caller's leg; past every rank for no caller
def af_mrank(m: Maybe<&2, F.Leg>) -> Nat:
  match m:
    case None{}:
      7n
    case Some{l}:
      af_rank(l)

# a step can move leg l in a world that landed ld: any leg but a served
# one, and a wait once its flight landed
def af_moves(l: F.Leg, +ld: List<&2, F.Out>) -> Bool:
  match l:
    case F.Load{}:
      True{}
    case F.Board{}:
      True{}
    case F.Check{f}:
      True{}
    case F.Fetch{f}:
      True{}
    case F.Store{f, c}:
      True{}
    case F.Land{f, o}:
      True{}
    case F.Waiting{f}:
      Maybe.is_some(&2, F.Out, List.get(&2, F.Out, ld, f))
    case F.Served{v, o}:
      False{}

# Laws
# ----

# LAW flight_one_fetch (A1.1): after any events from a new world, at most
# one caller fetches
# EXCLUDES: a second token fetch while one is in flight
law flight_one_fetch:
  for +evs: List<&2, F.Ev>
  {Nat.is_le(af_fetching(F.St.cs(am_run(evs))), 1n) == True{} : Bool}

# LAW flight_one_flight (A1.1): after any events from a new world, a
# flight is in flight exactly when one caller leads a flight (none
# otherwise), and every leader leads flight number |landed|: the one that
# lands next
# EXCLUDES: a second leader, a flight in flight that nobody leads (every
#   later expired caller joins it and waits forever), a leader kept after
#   its land, a flight started under a number already landed
law flight_one_flight:
  for +evs: List<&2, F.Ev>
  {af_leaders(F.St.cs(am_run(evs))) == am_bit(F.W.fl(F.St.w(am_run(evs)))) : Nat} & {af_all_on(List.length(&2, F.Out, F.W.landed(F.St.w(am_run(evs)))), F.St.cs(am_run(evs))) == True{} : Bool}

# LAW flight_board_joins (A1.2): after any events from a new world, a
# caller that boards while flight f is in flight (caller j leads it)
# joins flight f at its step
# EXCLUDES: a second flight started while one is in flight, a join of
#   another flight
law flight_board_joins:
  for +evs: List<&2, F.Ev>
  for +j: Nat
  for +lj: F.Leg
  for +f: Nat
  for leads: {List.get(&2, F.Leg, F.St.cs(am_run(evs)), j) == Some{lj} : Maybe<&2, F.Leg>}
  for flight: {af_led(lj) == Some{f} : Maybe<&2, Nat>}
  for +k: Nat
  for +ok: Bool
  for boards: {List.get(&2, F.Leg, F.St.cs(am_run(evs)), k) == Some{F.Board{}} : Maybe<&2, F.Leg>}
  {List.get(&2, F.Leg, F.St.cs(F.step(am_run(evs), F.Step{k, ok})), k) == Some{F.Waiting{f}} : Maybe<&2, F.Leg>}

# LAW flight_callers_get_its_outcome (A1.3): after any events from a new
# world, every caller served by flight f (its leader, and each caller that
# joined it) holds the outcome flight f landed with
# EXCLUDES: a joiner served another flight's outcome, or one the flight
#   never landed with; leader and joiners told different outcomes
law flight_callers_get_its_outcome:
  for +evs: List<&2, F.Ev>
  for +k: Nat
  for +f: Nat
  for +o: F.Out
  for served: {List.get(&2, F.Leg, F.St.cs(am_run(evs)), k) == Some{F.Served{Some{f}, o}} : Maybe<&2, F.Leg>}
  {List.get(&2, F.Out, F.W.landed(F.St.w(am_run(evs))), f) == Some{o} : Maybe<&2, F.Out>}

# LAW flight_after_end_stored (A1.7): after any events from a new world,
# once caller k lands flight f with credential c, the store holds c or a
# newer credential (a credential is numbered by its fetch; a peer's is
# newer than the one it replaces)
# EXCLUDES: a flight that ends before its credential is stored, a store
#   that keeps an older credential than the one served
law flight_after_end_stored:
  for +evs: List<&2, F.Ev>
  for +k: Nat
  for +f: Nat
  for +c: Nat
  for lands: {List.get(&2, F.Leg, F.St.cs(am_run(evs)), k) == Some{F.Land{f, F.Ok{c}}} : Maybe<&2, F.Leg>}
  for +ok: Bool
  {Nat.is_le(c, F.Sto.c(F.W.sto(F.St.w(F.step(am_run(evs), F.Step{k, ok}))))) == True{} : Bool}

# LAW flight_after_end_served (A1.7): after any events from a new world,
# once caller k lands flight f with credential c, while the store holds a
# fresh credential c2, a caller that arrives is served c2 at its first
# step (no flight), and c2 is c or newer
# EXCLUDES: a caller after the end that refreshes again, or is served an
#   older credential than the flight's
law flight_after_end_served:
  for +evs: List<&2, F.Ev>
  for +k: Nat
  for +f: Nat
  for +c: Nat
  for lands: {List.get(&2, F.Leg, F.St.cs(am_run(evs)), k) == Some{F.Land{f, F.Ok{c}}} : Maybe<&2, F.Leg>}
  for +ok: Bool
  for +ok2: Bool
  for +c2: Nat
  for fresh: {F.W.sto(F.St.w(F.step(am_run(evs), F.Step{k, ok}))) == F.Sto{c2, True{}} : F.Sto}
  {af_late(F.step(am_run(evs), F.Step{k, ok}), ok2) == Some{F.Served{None{}, F.Ok{c2}}} : Maybe<&2, F.Leg>} & {Nat.is_le(c, c2) == True{} : Bool}

# LAW flight_waiter_led (A1.4): after any events from a new world, every
# caller waiting on flight f waits on a flight that has landed (its
# outcome is recorded, so its next step serves it: flight_step_progresses)
# or on the flight in flight, the one numbered |landed| (which exactly one
# caller leads: flight_one_flight)
# EXCLUDES: a lost wake-up: a joiner of a flight that ended without
#   recording its outcome, or of a flight nobody leads, waits forever; a
#   join of a flight number never started
law flight_waiter_led:
  for +evs: List<&2, F.Ev>
  for +k: Nat
  for +f: Nat
  for waits: {List.get(&2, F.Leg, F.St.cs(am_run(evs)), k) == Some{F.Waiting{f}} : Maybe<&2, F.Leg>}
  {Bool.or(Maybe.is_some(&2, F.Out, List.get(&2, F.Out, F.W.landed(F.St.w(am_run(evs))), f)), Bool.and(F.W.fl(F.St.w(am_run(evs))), Nat.is_eq(f, List.length(&2, F.Out, F.W.landed(F.St.w(am_run(evs))))))) == True{} : Bool}

# LAW flight_step_progresses (A1.4): from any state, a caller whose leg a
# step can move (not served; a wait only once its flight landed) is
# moved strictly nearer its end by its step (af_rank falls): a load is
# served or boards, a board leads or joins, the leader's check lands or
# fetches, a fetch stores or lands, a store lands, a land and a landed
# wait are served
# EXCLUDES: a step that ignores the caller or the events (so the laws
#   over runs hold of a model that never moves), a step that goes back or
#   stays, a waiter not served once its flight landed
law flight_step_progresses:
  for +s: F.St
  for +k: Nat
  for +ok: Bool
  for +l: F.Leg
  for at: {List.get(&2, F.Leg, F.St.cs(s), k) == Some{l} : Maybe<&2, F.Leg>}
  for moves: {af_moves(l, F.W.landed(F.St.w(s))) == True{} : Bool}
  {Nat.is_lt(af_mrank(List.get(&2, F.Leg, F.St.cs(F.step(s, F.Step{k, ok})), k)), af_rank(l)) == True{} : Bool}
