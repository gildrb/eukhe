# eukhe: the laws of area auth_flight: the desk over every order of events

import Base
import ../../bend/auth_flight.bend as F
import ./entry.bend as AuthFlightEntry

# (A1) What no order of events breaks
# -----------------------------------
# These laws run the desk the entry steps (F.desk.step: every input string
# steps it as the event it reads, or keeps it, laws/auth_flight/entry.bend
# flight_step_reads and flight_step_malformed_exact) over any events, any
# callers of any providers, in any order, from any desk or from the
# open's empty desk.

# Runs

def af_after(r: F.DRes) -> F.Desk:
  match r:
    case F.DRes{d, o}:
      d

def af_out(r: F.DRes) -> F.DOut:
  match r:
    case F.DRes{d, o}:
      o

# the desk the entry steps, after the events evs from d
def af_go(evs: List<&2, F.DEv>, d: F.Desk) -> F.Desk:
  match evs:
    case Nil{}:
      d
    case e <> rest:
      af_go(rest, af_after(F.desk.step(d, e)))

# the desk after evs, from the open's empty desk
def af_run(evs: List<&2, F.DEv>) -> F.Desk:
  af_go(evs, F.Desk{Nil{}, 0n})

# how many live callers lead p's flight
def af_leaders(+p: String, cs: List<&2, F.Cl>) -> Nat:
  match cs:
    case Nil{}:
      0n
    case +x <> t:
      Nat.add(AuthFlightEntry.af_bit(AuthFlightEntry.af_lead(p, x)), af_leaders(p, t))

def af_fetches(+p: String, x: F.Cl) -> Bool:
  match x:
    case F.Cl{j, q, a}:
      match a:
        case F.Loads{}:
          False{}
        case F.Checks{}:
          False{}
        case F.Fetches{}:
          String.eq(q, p)
        case F.Stores{}:
          False{}
        case F.Waits{}:
          False{}

# how many live callers of p fetch
def af_fetchers(+p: String, cs: List<&2, F.Cl>) -> Nat:
  match cs:
    case Nil{}:
      0n
    case +x <> t:
      Nat.add(AuthFlightEntry.af_bit(af_fetches(p, x)), af_fetchers(p, t))

# x, when it waits, waits on a flight in flight in cs
def af_led(x: F.Cl, +cs: List<&2, F.Cl>) -> Bool:
  match x:
    case F.Cl{j, q, a}:
      match a:
        case F.Loads{}:
          True{}
        case F.Checks{}:
          True{}
        case F.Fetches{}:
          True{}
        case F.Stores{}:
          True{}
        case F.Waits{}:
          AuthFlightEntry.af_inflight(q, cs)

# every caller of xs that waits, waits on a flight in flight in cs
def af_led_all(xs: List<&2, F.Cl>, +cs: List<&2, F.Cl>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case x <> t:
      Bool.and(af_led(x, cs), af_led_all(t, cs))

# a caller numbered k is live
def af_live(+k: Nat, cs: List<&2, F.Cl>) -> Bool:
  match cs:
    case Nil{}:
      False{}
    case x <> t:
      match x:
        case F.Cl{j, p, a}:
          Bool.or(Nat.is_eq(j, k), af_live(k, t))

# the act a ends its caller's refresh
def af_ending(a: F.Act) -> Bool:
  match a:
    case F.DoLoad{}:
      False{}
    case F.DoCheck{}:
      False{}
    case F.DoFetch{}:
      False{}
    case F.DoStore{}:
      False{}
    case F.DoWait{}:
      False{}
    case F.DoDone{}:
      True{}
    case F.DoFail{e}:
      True{}

# how many pairs of xs end caller k's refresh; how many name k
def af_ends_in(+k: Nat, xs: List<&2, F.To>) -> Nat:
  match xs:
    case Nil{}:
      0n
    case x <> t:
      match x:
        case F.To{j, a}:
          Nat.add(AuthFlightEntry.af_bit(Bool.and(Nat.is_eq(j, k), af_ending(a))), af_ends_in(k, t))

def af_names_in(+k: Nat, xs: List<&2, F.To>) -> Nat:
  match xs:
    case Nil{}:
      0n
    case x <> t:
      match x:
        case F.To{j, a}:
          Nat.add(AuthFlightEntry.af_bit(Nat.is_eq(j, k)), af_names_in(k, t))

# the answer o ends caller k's refresh
def af_ends(+k: Nat, o: F.DOut) -> Bool:
  match o:
    case F.Acts{xs}:
      Nat.is_lt(0n, af_ends_in(k, xs))
    case F.Joined{j}:
      False{}
    case F.Off{}:
      False{}

# how many pairs of the answer o name caller k
def af_names(+k: Nat, o: F.DOut) -> Nat:
  match o:
    case F.Acts{xs}:
      af_names_in(k, xs)
    case F.Joined{j}:
      0n
    case F.Off{}:
      0n

# some answer of the events evs, from d, names caller k
def af_named(+k: Nat, evs: List<&2, F.DEv>, +d: F.Desk) -> Bool:
  match evs:
    case Nil{}:
      False{}
    case +e <> rest:
      Bool.or(Nat.is_lt(0n, af_names(k, af_out(F.desk.step(d, e)))), af_named(k, rest, af_after(F.desk.step(d, e))))

# e is caller j's unwind
def af_unwinds(e: F.DEv, +j: Nat) -> Bool:
  match e:
    case F.Comes{p}:
      False{}
    case F.Found{k, fd}:
      False{}
    case F.Unwinds{k}:
      Nat.is_eq(k, j)
    case F.Joiners{p}:
      False{}

# LAW flight_no_caller_dropped: from any desk, after any event, every live
# caller other than one that unwinds is still live or the answer ends its
# refresh (done or failed)
# EXCLUDES: a caller dropped without an outcome (a lost wake-up: a joiner
#   removed and never served), a land or an unwind that drops callers of
#   other flights
law flight_no_caller_dropped:
  for +d: F.Desk
  for +e: F.DEv
  for +j: Nat
  for live: {af_live(j, AuthFlightEntry.af_cs(d)) == True{} : Bool}
  for stays: {af_unwinds(e, j) == False{} : Bool}
  {Bool.or(af_live(j, AuthFlightEntry.af_cs(af_after(F.desk.step(d, e)))), af_ends(j, af_out(F.desk.step(d, e)))) == True{} : Bool}

# Laws: every order of events

# LAW flight_one_leader: after any events in any order (any callers of
# any providers), at most one live caller leads each provider's flight
# EXCLUDES: a second leader on board (two token fetches with one
#   single-use refresh token), a leader kept after its land
law flight_one_leader:
  for +evs: List<&2, F.DEv>
  for +p: String
  {Nat.is_le(af_leaders(p, AuthFlightEntry.af_cs(af_run(evs))), 1n) == True{} : Bool}

# LAW flight_one_fetch_each: after any events in any order, at most one
# live caller of each provider fetches
# EXCLUDES: a fetch while a fetch of the same provider is in flight
law flight_one_fetch_each:
  for +evs: List<&2, F.DEv>
  for +p: String
  {Nat.is_le(af_fetchers(p, AuthFlightEntry.af_cs(af_run(evs))), 1n) == True{} : Bool}

# LAW flight_no_lost_wakeup: after any events in any order, every waiting
# caller waits on its provider's flight while a live caller leads it
# EXCLUDES: a joiner left waiting after its flight landed or its leader
#   unwound (it would wait forever), a join of a flight nobody leads
law flight_no_lost_wakeup:
  for +evs: List<&2, F.DEv>
  {af_led_all(AuthFlightEntry.af_cs(af_run(evs)), AuthFlightEntry.af_cs(af_run(evs))) == True{} : Bool}

# LAW flight_done_once: after any events, an event whose answer ends
# caller k's refresh ends it exactly once; then k is no longer live, and
# no answer to any later events names k
# EXCLUDES: a Done twice, an act after the Done (a finished caller woken
#   again, a caller number reused), a caller kept after its end
law flight_done_once:
  for +pre: List<&2, F.DEv>
  for +e: F.DEv
  for +post: List<&2, F.DEv>
  for +k: Nat
  for ends: {af_ends(k, af_out(F.desk.step(af_run(pre), e))) == True{} : Bool}
  {af_names(k, af_out(F.desk.step(af_run(pre), e))) == 1n : Nat} & {af_named(k, post, af_after(F.desk.step(af_run(pre), e))) == False{} : Bool} & {af_live(k, AuthFlightEntry.af_cs(af_go(post, af_after(F.desk.step(af_run(pre), e))))) == False{} : Bool}

# LAW flight_safety_witness: anchor: the premises of flight_no_caller_dropped
# and flight_done_once hold on a run where their conclusions say something:
# x's caller 0 leads, caller 1 joins; caller 1 is live before the land of
# caller 0's check, the land is not its unwind, and the land ends its
# refresh (done with the landed outcome)
# EXCLUDES: flight_no_caller_dropped or flight_done_once made vacuous by
#   premises no run meets
law flight_safety_witness:
  {AuthFlightEntry.af_cs(af_run([F.Comes{"x"}, F.Found{0n, F.LoadExpired{}}, F.Comes{"x"}, F.Found{1n, F.LoadExpired{}}])) == [F.Cl{1n, "x", F.Waits{}}, F.Cl{0n, "x", F.Checks{}}] : List<&2, F.Cl>} &
  {af_live(1n, AuthFlightEntry.af_cs(af_run([F.Comes{"x"}, F.Found{0n, F.LoadExpired{}}, F.Comes{"x"}, F.Found{1n, F.LoadExpired{}}]))) == True{} : Bool} &
  {af_unwinds(F.Found{0n, F.CheckFresh{}}, 1n) == False{} : Bool} &
  {af_ends(1n, af_out(F.desk.step(af_run([F.Comes{"x"}, F.Found{0n, F.LoadExpired{}}, F.Comes{"x"}, F.Found{1n, F.LoadExpired{}}]), F.Found{0n, F.CheckFresh{}}))) == True{} : Bool}
