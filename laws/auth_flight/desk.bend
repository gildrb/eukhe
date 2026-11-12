# eukhe: the laws of area auth_flight: the desk's decision on one event

import Base
import ../../bend/auth_flight.bend as F
import ./entry.bend as AuthFlightEntry
import ./safety.bend as AuthFlightSafety

# (A1) What the desk does with one event
# --------------------------------------
# Requirements A1.3, A1.5, A1.8, A1.10 (table: laws/auth_flight/entry.bend).
# Each law is a claim about F.desk.step, the decision the entry runs on
# every event it reads (flight_step_answers, flight_step_reads_only_events),
# from every desk: any callers of any providers, in any places. A live
# caller is written where it stands in the desk's list: the callers pre
# before it, none of them numbered k (the desk acts on the first caller
# numbered k), then caller k of provider p at place a, then post. The
# number n the desk gives its next caller is any.

# Terms
# -----

# x before r when b, else r alone
def af_keep(b: Bool, x: F.Cl, r: List<&2, F.Cl>) -> List<&2, F.Cl>:
  match b:
    case True{}:
      x <> r
    case False{}:
      r

# the callers of cs that wait on p's flight, in their order
def af_waiters(+p: String, cs: List<&2, F.Cl>) -> List<&2, F.Cl>:
  match cs:
    case Nil{}:
      Nil{}
    case +x <> t:
      af_keep(AuthFlightEntry.af_waits(p, x), x, af_waiters(p, t))

# the callers of cs that do not wait on p's flight, in their order
def af_others(+p: String, cs: List<&2, F.Cl>) -> List<&2, F.Cl>:
  match cs:
    case Nil{}:
      Nil{}
    case +x <> t:
      af_keep(Bool.not(AuthFlightEntry.af_waits(p, x)), x, af_others(p, t))

# each caller of ws, in order, told a
def af_tell(+a: F.Act, ws: List<&2, F.Cl>) -> List<&2, F.To>:
  match ws:
    case Nil{}:
      Nil{}
    case x <> t:
      match x:
        case F.Cl{j, q, o}:
          F.To{j, a} <> af_tell(a, t)

# the act a live caller at a was last sent: the place's meaning
# (bend/auth_flight.bend type At: asked to load; leading its provider's
# flight at its check, its fetch or its store; waiting for the flight)
def af_place_act(a: F.At) -> F.Act:
  match a:
    case F.Loads{}:
      F.DoLoad{}
    case F.Checks{}:
      F.DoCheck{}
    case F.Fetches{}:
      F.DoFetch{}
    case F.Stores{}:
      F.DoStore{}
    case F.Waits{}:
      F.DoWait{}

# the founds Rust reports for each act (crates/eukhe-core/src/auth/flight.rs
# Order::take 339-353): a load reads the store and reports a fresh
# credential, an expired one, or that no refresh can start
# (Found::load 223-243); a check reads it again and reports fresh or
# expired (Found::check 246-257); a fetch reports a credential or a
# failure; a store reports its outcome; a wait, a done and a failure
# report nothing
def af_answers_load(fd: F.Fd) -> Bool:
  match fd:
    case F.LoadFresh{}:
      True{}
    case F.LoadExpired{}:
      True{}
    case F.LoadFailed{}:
      True{}
    case F.CheckFresh{}:
      False{}
    case F.CheckExpired{}:
      False{}
    case F.FetchOk{}:
      False{}
    case F.FetchFailed{}:
      False{}
    case F.Stored{}:
      False{}

def af_answers_check(fd: F.Fd) -> Bool:
  match fd:
    case F.LoadFresh{}:
      False{}
    case F.LoadExpired{}:
      False{}
    case F.LoadFailed{}:
      False{}
    case F.CheckFresh{}:
      True{}
    case F.CheckExpired{}:
      True{}
    case F.FetchOk{}:
      False{}
    case F.FetchFailed{}:
      False{}
    case F.Stored{}:
      False{}

def af_answers_fetch(fd: F.Fd) -> Bool:
  match fd:
    case F.LoadFresh{}:
      False{}
    case F.LoadExpired{}:
      False{}
    case F.LoadFailed{}:
      False{}
    case F.CheckFresh{}:
      False{}
    case F.CheckExpired{}:
      False{}
    case F.FetchOk{}:
      True{}
    case F.FetchFailed{}:
      True{}
    case F.Stored{}:
      False{}

def af_answers_store(fd: F.Fd) -> Bool:
  match fd:
    case F.LoadFresh{}:
      False{}
    case F.LoadExpired{}:
      False{}
    case F.LoadFailed{}:
      False{}
    case F.CheckFresh{}:
      False{}
    case F.CheckExpired{}:
      False{}
    case F.FetchOk{}:
      False{}
    case F.FetchFailed{}:
      False{}
    case F.Stored{}:
      True{}

# fd is what Rust reports after doing act
def af_answers(act: F.Act, fd: F.Fd) -> Bool:
  match act:
    case F.DoLoad{}:
      af_answers_load(fd)
    case F.DoCheck{}:
      af_answers_check(fd)
    case F.DoFetch{}:
      af_answers_fetch(fd)
    case F.DoStore{}:
      af_answers_store(fd)
    case F.DoWait{}:
      False{}
    case F.DoDone{}:
      False{}
    case F.DoFail{e}:
      False{}

# the callers after caller k of p, between pre and post, is sent act: it
# stands where act puts it (the place whose act is act), or it is gone
# when act ends its refresh
def af_moved(+k: Nat, +p: String, act: F.Act, pre: List<&2, F.Cl>, +post: List<&2, F.Cl>) -> List<&2, F.Cl>:
  match act:
    case F.DoLoad{}:
      List.append(&2, F.Cl, pre, F.Cl{k, p, F.Loads{}} <> post)
    case F.DoCheck{}:
      List.append(&2, F.Cl, pre, F.Cl{k, p, F.Checks{}} <> post)
    case F.DoFetch{}:
      List.append(&2, F.Cl, pre, F.Cl{k, p, F.Fetches{}} <> post)
    case F.DoStore{}:
      List.append(&2, F.Cl, pre, F.Cl{k, p, F.Stores{}} <> post)
    case F.DoWait{}:
      List.append(&2, F.Cl, pre, F.Cl{k, p, F.Waits{}} <> post)
    case F.DoDone{}:
      List.append(&2, F.Cl, pre, post)
    case F.DoFail{e}:
      List.append(&2, F.Cl, pre, post)

# the joiner count of p's flight: how many wait on it, none when p has no
# flight in flight
def af_count(fl: Bool, +p: String, cs: List<&2, F.Cl>) -> Maybe<&2, Nat>:
  match fl:
    case True{}:
      Some{List.length(&2, F.Cl, af_waiters(p, cs))}
    case False{}:
      None{}

# Laws
# ----

# LAW flight_land_serves_joiners (A1.3): when the leader of p's flight
# (caller k, the first numbered k, at a leading place a) reports a found
# that lands the flight there (af_lands: a fresh credential at its check,
# a failed fetch at its fetch, the store's outcome at its store), the
# reply is exactly: the leader, then every other caller waiting on p's
# flight in the desk's order, each done with this event's payload (the one
# outcome); the desk keeps every other caller, in order, and the next
# number
# EXCLUDES: a joiner never woken (a lost wake-up), a joiner served a
#   failure or another event's payload, another provider's caller woken, a
#   land that keeps its leader or a joiner, a caller of another flight
#   dropped or moved, a reply in another order
law flight_land_serves_joiners:
  for +pre: List<&2, F.Cl>
  for +post: List<&2, F.Cl>
  for +n: Nat
  for +k: Nat
  for +p: String
  for +a: F.At
  for first: {AuthFlightSafety.af_live(k, pre) == False{} : Bool}
  for +fd: F.Fd
  for lands: {AuthFlightEntry.af_lands(a, fd) == True{} : Bool}
  {F.desk.step(F.Desk{List.append(&2, F.Cl, pre, F.Cl{k, p, a} <> post), n}, F.Found{k, fd}) == F.DRes{F.Desk{af_others(p, List.append(&2, F.Cl, pre, post)), n}, F.Acts{F.To{k, F.DoDone{}} <> af_tell(F.DoDone{}, af_waiters(p, List.append(&2, F.Cl, pre, post)))}} : F.DRes}

# LAW flight_unwind_leader_fails_joiners (A1.5): when the leader of p's
# flight (caller k, the first numbered k, at a leading place: its check,
# fetch or store) unwinds, it leaves, and every caller waiting on p's
# flight, in the desk's order, fails with exactly "the token refresh of
# <p> ended without an outcome" (af_gone) and leaves; every other caller
# stays, in order, and the next number is kept
# EXCLUDES: joiners left waiting on a flight nobody leads, a failure with
#   another text or provider, another provider's caller failed, a caller
#   of another flight dropped or moved, the leader kept
law flight_unwind_leader_fails_joiners:
  for +pre: List<&2, F.Cl>
  for +post: List<&2, F.Cl>
  for +n: Nat
  for +k: Nat
  for +p: String
  for +a: F.At
  for first: {AuthFlightSafety.af_live(k, pre) == False{} : Bool}
  for leads: {AuthFlightEntry.af_leads(a) == True{} : Bool}
  {F.desk.step(F.Desk{List.append(&2, F.Cl, pre, F.Cl{k, p, a} <> post), n}, F.Unwinds{k}) == F.DRes{F.Desk{af_others(p, List.append(&2, F.Cl, pre, post)), n}, F.Acts{af_tell(F.DoFail{AuthFlightEntry.af_gone(p)}, af_waiters(p, List.append(&2, F.Cl, pre, post)))}} : F.DRes}

# LAW flight_unwind_other_leaves (A1.5): a caller that does not lead (it
# loads or waits; the first numbered k) and unwinds leaves alone: the reply
# names nobody, every other caller stays, in order, and the next number is
# kept
# EXCLUDES: a waiting caller's unwind that wakes, fails or drops the
#   others, a flight landed by a caller that does not lead it, the caller
#   kept
law flight_unwind_other_leaves:
  for +pre: List<&2, F.Cl>
  for +post: List<&2, F.Cl>
  for +n: Nat
  for +k: Nat
  for +p: String
  for +a: F.At
  for first: {AuthFlightSafety.af_live(k, pre) == False{} : Bool}
  for leads: {AuthFlightEntry.af_leads(a) == False{} : Bool}
  {F.desk.step(F.Desk{List.append(&2, F.Cl, pre, F.Cl{k, p, a} <> post), n}, F.Unwinds{k}) == F.DRes{F.Desk{List.append(&2, F.Cl, pre, post), n}, F.Acts{Nil{}}} : F.DRes}

# LAW flight_unknown_caller_out_of_turn (A1.8): a found or an unwind of a
# caller number no live caller holds (never arrived, or done) is out of
# turn and keeps the desk
# EXCLUDES: a finished caller served or failed again, an unknown caller's
#   event that changes the desk
law flight_unknown_caller_out_of_turn:
  for +cs: List<&2, F.Cl>
  for +n: Nat
  for +k: Nat
  for gone: {AuthFlightSafety.af_live(k, cs) == False{} : Bool}
  for +fd: F.Fd
  {F.desk.step(F.Desk{cs, n}, F.Found{k, fd}) == F.DRes{F.Desk{cs, n}, F.Off{}} : F.DRes} & {F.desk.step(F.Desk{cs, n}, F.Unwinds{k}) == F.DRes{F.Desk{cs, n}, F.Off{}} : F.DRes}

# LAW flight_found_out_of_turn (A1.8): a found of a live caller (the first
# numbered k, at place a) that does not answer the act its place was sent
# (af_answers of af_place_act: a fetch result while loading, a load result
# while leading, any found while waiting) is out of turn and keeps the desk
# EXCLUDES: a found from the wrong step acted on (a failure read as the
#   fetch's while the store runs, a waiting caller that reports), a desk
#   changed by it
law flight_found_out_of_turn:
  for +pre: List<&2, F.Cl>
  for +post: List<&2, F.Cl>
  for +n: Nat
  for +k: Nat
  for +p: String
  for +a: F.At
  for first: {AuthFlightSafety.af_live(k, pre) == False{} : Bool}
  for +fd: F.Fd
  for off: {af_answers(af_place_act(a), fd) == False{} : Bool}
  {F.desk.step(F.Desk{List.append(&2, F.Cl, pre, F.Cl{k, p, a} <> post), n}, F.Found{k, fd}) == F.DRes{F.Desk{List.append(&2, F.Cl, pre, F.Cl{k, p, a} <> post), n}, F.Off{}} : F.DRes}

# LAW flight_found_moves (A1.8, A1.2): a found of a live caller (the first
# numbered k, at place a) that answers the act its place was sent and does
# not land a flight is taken: the reply is one act to that caller alone,
# the caller then stands where that act puts it (af_moved: the place whose
# act it is), or leaves when the act ends its refresh, and every other
# caller stays, in order, with the next number kept. Which act it is:
# flight_step_is_model
# EXCLUDES: a found in turn refused, an act sent to another caller or two
#   acts, a caller left at a place other than the act it was sent (its
#   next found then out of turn, or a found from the wrong step taken), a
#   caller of another flight moved or dropped
law flight_found_moves:
  for +pre: List<&2, F.Cl>
  for +post: List<&2, F.Cl>
  for +n: Nat
  for +k: Nat
  for +p: String
  for +a: F.At
  for first: {AuthFlightSafety.af_live(k, pre) == False{} : Bool}
  for +fd: F.Fd
  for answers: {af_answers(af_place_act(a), fd) == True{} : Bool}
  for stays: {AuthFlightEntry.af_lands(a, fd) == False{} : Bool}
  exs act: F.Act
  {F.desk.step(F.Desk{List.append(&2, F.Cl, pre, F.Cl{k, p, a} <> post), n}, F.Found{k, fd}) == F.DRes{F.Desk{af_moved(k, p, act, pre, post), n}, F.Acts{[F.To{k, act}]}} : F.DRes}

# LAW flight_joiners_counts (A1.10): the joiner count of provider p is how
# many live callers wait on p's flight while a live caller leads it, none
# when nobody leads it; the desk is kept
# EXCLUDES: a count of another provider's callers, of the leader, or of
#   loading callers; a count for a provider with no flight; a desk changed
#   by the probe
law flight_joiners_counts:
  for +cs: List<&2, F.Cl>
  for +n: Nat
  for +p: String
  {F.desk.step(F.Desk{cs, n}, F.Joiners{p}) == F.DRes{F.Desk{cs, n}, F.Joined{af_count(AuthFlightEntry.af_inflight(p, cs), p, cs)}} : F.DRes}
