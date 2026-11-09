# eukhe: the laws of area admission

import Base
import ../bend/admission.bend as Ad
import ../bend/ffi_admission.bend as FAd
import ../bend/wire.bend as Wr
import ./base.bend as LawsBase

# (H3) A user's request never waits behind background work
# ---------------------------------------------------------
# One provider's admission: crates/eukhe-core/src/admission.rs (module
# doc, `AdmissionLimits`, `ProviderPermit`, `QueuedPermit`) and its tests
# (admission/tests.rs). omp (packages/ai/src/stream.ts
# `withProviderInFlightLimit`, `providers.maxInFlightRequests` in
# docs/settings.md) caps each provider's requests in flight and makes the
# rest wait, an omitted provider unlimited; eukhe adds the two classes,
# the preemption and the queue limit. The model is bend/admission.bend:
# `Ad.step`, one op on every ticket ever admitted (ticket k is the k-th
# admitted, oldest 0). eukhe runs `Ad.Live.step`, which
# admission_live_step ties to the model, through the stepper
# bend/ffi_admission.bend (R1-R3: laws/admission/wire.bend). Every op is
# free: admits of either class, polls, drops of permits and of waiters,
# new limits, in any order, on any state.
#
# H3.1 An interactive admit on a provider with an in-flight limit takes
#      back every background slot at once: a granted background waiter
#      waits again, a collected background permit is preempted, its
#      holder told (tests.rs
#      an_interactive_request_preempts_every_background_permit,
#      an_uncollected_background_grant_goes_back_to_the_queue,
#      a_preempted_model_permit_says_so). On an unlimited provider it
#      changes no ticket (only_a_limited_provider_preempts_a_running_background_request).
#      After any history no background slot is held while an
#      interactive request waits.
# H3.2 Within a class, slots go oldest first
#      (a_released_slot_goes_to_the_oldest_waiter).
# H3.3 No lost wake-up: no slot stays free while a waiter may take it:
#      an interactive waiter, or a background one while no interactive
#      request holds a slot.
# H3.4 An interactive waiter is granted once the interactive slots held
#      and the interactive waiters ahead of it are freed, whatever
#      background requests do.
# H3.5 At most providerMaxInFlight slots are held at once (omp's cap); a
#      lowered limit only drains.
# H3.6 An interactive request that does not get a slot at once is
#      rejected once providerMaxQueued interactive requests wait
#      (local_admission_rejects_past_the_queue_limit); a background one
#      is never rejected.
# H3.7 A background request takes a slot only while no interactive
#      request holds a slot or waits for one (module doc).
# H3.8 The holders' ops: a poll collects a granted permit; dropping a
#      collected permit ends it and its slot goes to the waiters;
#      dropping a preempted one ends it and frees nothing more (its slot
#      went at the preemption); dropping a waiter, granted or not, ends
#      it and a slot it was granted passes on
#      (a_granted_but_uncollected_permit_passes_on_when_dropped); new
#      limits take effect at once and serve the waiters. The free slots
#      go to the interactive waiters, oldest first, then, while no
#      interactive request holds a slot or waits, to the background
#      waiters, oldest first (H3.2, H3.3, H3.5, H3.7).
# A1   An ended ticket stays ended.
# A2   Every ticket ends when its holder drops it (a waiter leaves, a
#      permit is released): no slot leaks.
# A3   An op on a ticket it does not apply to (a poll of a ticket not
#      granted, a release of a ticket holding no collected permit, a
#      leave of a collected permit, any op on an ended or never admitted
#      ticket) changes nothing.
# A4   The live controller is the model with the ended tickets left out,
#      numbered as the model numbers them.

# Terms
# -----
# Every term reads a state through the constructors of the model's types
# and Base, never through the model's own functions: a model whose
# counts or accessors were wrong could not make a law vacuous.

# the tickets, the limit of a model state
def adm_ts(s: Ad.St) -> List<&2, Ad.Tk>:
  match s:
    case Ad.St{l, q, ts}:
      ts

def adm_lim(s: Ad.St) -> Ad.Lim:
  match s:
    case Ad.St{l, q, ts}:
      l

# ticket k of a state (none: never admitted)
def adm_status(+s: Ad.St, k: Nat) -> Maybe<&2, Ad.Tk>:
  List.get(&2, Ad.Tk, adm_ts(s), k)

# the state after the ops os, oldest first, from s
def adm_run(os: List<&2, Ad.Op>, s: Ad.St) -> Ad.St:
  match os:
    case Nil{}:
      s
    case o <> r:
      adm_run(r, Ad.step(s, o))

def ads_same(a: Ad.Cls, b: Ad.Cls) -> Bool:
  match a b:
    case Ad.Ia{} Ad.Ia{}:
      True{}
    case Ad.Ia{} Ad.Bg{}:
      False{}
    case Ad.Bg{} Ad.Ia{}:
      False{}
    case Ad.Bg{} Ad.Bg{}:
      True{}

# a status that holds a slot: granted (not collected yet) or collected; a
# preempted permit's slot was freed by the preemption
def ads_holding(s: Ad.Sts) -> Bool:
  match s:
    case Ad.Queued{}:
      False{}
    case Ad.Granted{}:
      True{}
    case Ad.Held{}:
      True{}
    case Ad.Preempted{}:
      False{}
    case Ad.Ended{}:
      False{}

def ads_waiting(s: Ad.Sts) -> Bool:
  match s:
    case Ad.Queued{}:
      True{}
    case Ad.Granted{}:
      False{}
    case Ad.Held{}:
      False{}
    case Ad.Preempted{}:
      False{}
    case Ad.Ended{}:
      False{}

# ticket t of class c holds a slot / waits
def ads_holds(+c: Ad.Cls, t: Ad.Tk) -> Bool:
  match t:
    case Ad.Tk{tc, s}:
      Bool.and(ads_holding(s), ads_same(c, tc))

def ads_waits(+c: Ad.Cls, t: Ad.Tk) -> Bool:
  match t:
    case Ad.Tk{tc, s}:
      Bool.and(ads_waiting(s), ads_same(c, tc))

def ads_one(b: Bool, n: Nat) -> Nat:
  match b:
    case True{}:
      1n+n
    case False{}:
      n

# the slots class c holds / the waiters of class c
def ads_held(+c: Ad.Cls, ts: List<&2, Ad.Tk>) -> Nat:
  match ts:
    case Nil{}:
      0n
    case h <> r:
      ads_one(ads_holds(c, h), ads_held(c, r))

def ads_queued(+c: Ad.Cls, ts: List<&2, Ad.Tk>) -> Nat:
  match ts:
    case Nil{}:
      0n
    case h <> r:
      ads_one(ads_waits(c, h), ads_queued(c, r))

# the slots held by both classes
def ads_busy(+ts: List<&2, Ad.Tk>) -> Nat:
  Nat.add(ads_held(Ad.Ia{}, ts), ads_held(Ad.Bg{}, ts))

# a slot is free with n held: no limit, or n below 1 + p
def ads_room(l: Ad.Lim, n: Nat) -> Bool:
  match l:
    case Ad.Unl{}:
      True{}
    case Ad.Cap{p}:
      Nat.is_le(n, p)

# n slots held are within the limit: no limit, or at most 1 + p
def adm_within(l: Ad.Lim, n: Nat) -> Bool:
  match l:
    case Ad.Unl{}:
      True{}
    case Ad.Cap{p}:
      Nat.is_le(n, 1n+p)

# a less n, or 0 when n is more
def ads_left(a: Nat, n: Nat) -> Nat:
  match a n:
    case 0n _:
      0n
    case 1n+b 0n:
      1n+b
    case 1n+b 1n+m:
      ads_left(b, m)

# the free slots with n held: none for no limit (no bound), else 1 + p
# less n
def ads_free(l: Ad.Lim, n: Nat) -> Maybe<&2, Nat>:
  match l:
    case Ad.Unl{}:
      None{}
    case Ad.Cap{p}:
      Some{ads_left(1n+p, n)}

# The grant (H3.8), written as two passes over the waiters, each oldest
# first while a slot is free: the interactive waiters, then, while no
# interactive request holds a slot or waits, the background ones. The
# model grants one waiter at a time, picking the class anew each time.

# a ticket after the grant pass reaches it: a waiter of the pass's class
# c (w) is granted while a slot is free (f), else it stays
def ads_head(w: Bool, f: Maybe<&2, Nat>, c: Ad.Cls, h: Ad.Tk) -> Ad.Tk:
  match w:
    case False{}:
      h
    case True{}:
      match f:
        case None{}:
          Ad.Tk{c, Ad.Granted{}}
        case Some{n}:
          match n:
            case 0n:
              h
            case 1n+k:
              Ad.Tk{c, Ad.Granted{}}

# the free slots after the pass reaches a ticket: a grant takes one
def ads_next(w: Bool, f: Maybe<&2, Nat>) -> Maybe<&2, Nat>:
  match w:
    case False{}:
      f
    case True{}:
      match f:
        case None{}:
          None{}
        case Some{n}:
          match n:
            case 0n:
              Some{0n}
            case 1n+k:
              Some{k}

# a grant pass of class c: its waiters, oldest first, each granted while
# a slot is free
def ads_take(+c: Ad.Cls, ts: List<&2, Ad.Tk>, +f: Maybe<&2, Nat>) -> List<&2, Ad.Tk>:
  match ts:
    case Nil{}:
      Nil{}
    case +h <> r:
      +w = ads_waits(c, h)
      ads_head(w, f, c, h) <> ads_take(c, r, ads_next(w, f))

def ads_grant.then(idle: Bool, f: Maybe<&2, Nat>, t: List<&2, Ad.Tk>) -> List<&2, Ad.Tk>:
  match idle:
    case True{}:
      ads_take(Ad.Bg{}, t, f)
    case False{}:
      t

# the free slots go to the interactive waiters, oldest first; then, while
# no interactive request holds a slot or waits, to the background waiters,
# oldest first
def ads_grant(+l: Ad.Lim, +ts: List<&2, Ad.Tk>) -> List<&2, Ad.Tk>:
  +f = ads_free(l, ads_busy(ts))
  +t1 = ads_take(Ad.Ia{}, ts, f)
  ads_grant.then(Bool.and(Nat.is_eq(ads_held(Ad.Ia{}, t1), 0n), Nat.is_eq(ads_queued(Ad.Ia{}, t1), 0n)), f, t1)

# a waiter may take a free slot (H3.3): a slot is free, and an
# interactive request waits, or a background one waits while no
# interactive request holds a slot
def adm_grantable(s: Ad.St) -> Bool:
  match s:
    case Ad.St{l, q, +ts}:
      Bool.and(ads_room(l, ads_busy(ts)), Bool.or(Bool.not(Nat.is_eq(ads_queued(Ad.Ia{}, ts), 0n)), Bool.and(Bool.not(Nat.is_eq(ads_queued(Ad.Bg{}, ts), 0n)), Nat.is_eq(ads_held(Ad.Ia{}, ts), 0n))))

# no background slot is held while an interactive request waits (H3.1)
def adm_calm(+ts: List<&2, Ad.Tk>) -> Bool:
  Bool.or(Nat.is_eq(ads_held(Ad.Bg{}, ts), 0n), Nat.is_eq(ads_queued(Ad.Ia{}, ts), 0n))

# the slots an op frees itself, before any grant (H3.1, H3.8): a release
# of a collected permit, or a granted waiter that leaves, one; an
# interactive admit on a provider with an in-flight limit, every
# background slot
def adm_freed.at(m: Maybe<&2, Ad.Tk>, rel: Bool) -> Nat:
  match m rel:
    case Some{Ad.Tk{c, Ad.Held{}}} True{}:
      1n
    case Some{Ad.Tk{c, Ad.Granted{}}} False{}:
      1n
    case _ _:
      0n

def adm_freed.ia(l: Ad.Lim, n: Nat) -> Nat:
  match l:
    case Ad.Unl{}:
      0n
    case Ad.Cap{p}:
      n

def adm_freed(+s: Ad.St, o: Ad.Op) -> Nat:
  match o:
    case Ad.Admit{c}:
      match c:
        case Ad.Ia{}:
          adm_freed.ia(adm_lim(s), ads_held(Ad.Bg{}, adm_ts(s)))
        case Ad.Bg{}:
          0n
    case Ad.Collect{k}:
      0n
    case Ad.Release{k}:
      adm_freed.at(List.get(&2, Ad.Tk, adm_ts(s), k), True{})
    case Ad.Leave{k}:
      adm_freed.at(List.get(&2, Ad.Tk, adm_ts(s), k), False{})
    case Ad.Limit{l, q}:
      0n

# adm_fifo(c, ts, seen): no ticket of class c holds a slot after one of
# its class that waits (seen: one waited before ts) (H3.2)
def adm_fifo(+c: Ad.Cls, ts: List<&2, Ad.Tk>, +seen: Bool) -> Bool:
  match ts:
    case Nil{}:
      True{}
    case +h <> r:
      Bool.and(Bool.not(Bool.and(seen, ads_holds(c, h))), adm_fifo(c, r, Bool.or(seen, ads_waits(c, h))))

def adm_fifo_both(+ts: List<&2, Ad.Tk>) -> Bool:
  Bool.and(adm_fifo(Ad.Ia{}, ts, False{}), adm_fifo(Ad.Bg{}, ts, False{}))

# ticket m waits, interactive
def adm_waits_ia(m: Maybe<&2, Ad.Tk>) -> Bool:
  match m:
    case Some{Ad.Tk{Ad.Ia{}, Ad.Queued{}}}:
      True{}
    case _:
      False{}

# what interactive ticket w waits for (H3.4): the interactive tickets
# before w that hold a slot or wait, and the interactive slots held from
# w on
def adm_pot(ts: List<&2, Ad.Tk>, w: Nat) -> Nat:
  match ts:
    case Nil{}:
      0n
    case +h <> +r:
      match w:
        case 0n:
          ads_held(Ad.Ia{}, h <> r)
        case 1n+p:
          ads_one(Bool.or(ads_holds(Ad.Ia{}, h), ads_waits(Ad.Ia{}, h)), adm_pot(r, p))

def adm_ahead(+s: Ad.St, w: Nat) -> Nat:
  adm_pot(adm_ts(s), w)

# an op frees an interactive slot: a release of a collected interactive
# permit, or a granted interactive waiter that leaves
def adm_frees.at(m: Maybe<&2, Ad.Tk>, rel: Bool) -> Nat:
  match m rel:
    case Some{Ad.Tk{Ad.Ia{}, Ad.Held{}}} True{}:
      1n
    case Some{Ad.Tk{Ad.Ia{}, Ad.Granted{}}} False{}:
      1n
    case _ _:
      0n

def adm_frees(+s: Ad.St, o: Ad.Op) -> Nat:
  match o:
    case Ad.Admit{c}:
      0n
    case Ad.Collect{k}:
      0n
    case Ad.Release{k}:
      adm_frees.at(List.get(&2, Ad.Tk, adm_ts(s), k), True{})
    case Ad.Leave{k}:
      adm_frees.at(List.get(&2, Ad.Tk, adm_ts(s), k), False{})
    case Ad.Limit{l, q}:
      0n

# the interactive slots freed along a run
def adm_frees_run(os: List<&2, Ad.Op>, +s: Ad.St) -> Nat:
  match os:
    case Nil{}:
      0n
    case +o <> r:
      Nat.add(adm_frees(s, o), adm_frees_run(r, Ad.step(s, o)))

# ticket w waits, interactive, before and after every op of a run
def adm_waits_thru(os: List<&2, Ad.Op>, +s: Ad.St, +w: Nat) -> Bool:
  match os:
    case Nil{}:
      adm_waits_ia(adm_status(s, w))
    case +o <> r:
      Bool.and(adm_waits_ia(adm_status(s, w)), adm_waits_thru(r, Ad.step(s, o), w))

# ticket m has ended
def adm_ended(m: Maybe<&2, Ad.Tk>) -> Bool:
  match m:
    case Some{Ad.Tk{c, Ad.Ended{}}}:
      True{}
    case _:
      False{}

# ticket m holds a collected permit
def adm_took(m: Maybe<&2, Ad.Tk>) -> Bool:
  match m:
    case Some{Ad.Tk{c, Ad.Held{}}}:
      True{}
    case _:
      False{}

# the op by which ticket m's holder ends it (A2): a waiter (queued or
# granted, not collected) leaves (Rust `QueuedPermit` drop), a permit is
# released (`ProviderPermit` drop)
def adm_finish(m: Maybe<&2, Ad.Tk>, k: Nat) -> Ad.Op:
  match m:
    case Some{Ad.Tk{c, Ad.Queued{}}}:
      Ad.Leave{k}
    case Some{Ad.Tk{c, Ad.Granted{}}}:
      Ad.Leave{k}
    case _:
      Ad.Release{k}

# the newest ticket
def adm_last.go(r: List<&2, Ad.Tk>, t: Ad.Tk) -> Maybe<&2, Ad.Tk>:
  match r:
    case Nil{}:
      Some{t}
    case u <> v:
      adm_last.go(v, u)

def adm_last(ts: List<&2, Ad.Tk>) -> Maybe<&2, Ad.Tk>:
  match ts:
    case Nil{}:
      None{}
    case t <> r:
      adm_last.go(r, t)

# a status a new ticket may get (H3.6): a slot taken at once (held) or a
# wait (queued), and for an interactive request only, a rejection
# (ended); never a grant left to collect (an admit that gets a slot
# holds it at once: Rust `Admission::Granted`)
def adm_fresh(c: Ad.Cls, x: Ad.Sts) -> Bool:
  match c:
    case Ad.Ia{}:
      match x:
        case Ad.Queued{}:
          True{}
        case Ad.Granted{}:
          False{}
        case Ad.Held{}:
          True{}
        case Ad.Preempted{}:
          False{}
        case Ad.Ended{}:
          True{}
    case Ad.Bg{}:
      match x:
        case Ad.Queued{}:
          True{}
        case Ad.Granted{}:
          False{}
        case Ad.Held{}:
          True{}
        case Ad.Preempted{}:
          False{}
        case Ad.Ended{}:
          False{}

# an earlier ticket after an interactive admit takes back the background
# slots (H3.1), row by row: an interactive ticket is untouched; a
# granted background waiter waits again
# (an_uncollected_background_grant_goes_back_to_the_queue); a collected
# background permit is preempted (a_preempted_model_permit_says_so); a
# waiting, preempted or ended background ticket holds no slot and is
# untouched
def adm_taken_back(t: Ad.Tk) -> Ad.Tk:
  match t:
    case Ad.Tk{c, s}:
      match c:
        case Ad.Ia{}:
          Ad.Tk{Ad.Ia{}, s}
        case Ad.Bg{}:
          match s:
            case Ad.Queued{}:
              Ad.Tk{Ad.Bg{}, Ad.Queued{}}
            case Ad.Granted{}:
              Ad.Tk{Ad.Bg{}, Ad.Queued{}}
            case Ad.Held{}:
              Ad.Tk{Ad.Bg{}, Ad.Preempted{}}
            case Ad.Preempted{}:
              Ad.Tk{Ad.Bg{}, Ad.Preempted{}}
            case Ad.Ended{}:
              Ad.Tk{Ad.Bg{}, Ad.Ended{}}

def adm_taken_back.all(ts: List<&2, Ad.Tk>) -> List<&2, Ad.Tk>:
  match ts:
    case Nil{}:
      Nil{}
    case t <> r:
      adm_taken_back(t) <> adm_taken_back.all(r)

# the earlier tickets after an admit of class c: a background admit and
# an interactive admit on an unlimited provider keep them; an interactive
# admit on a provider with an in-flight limit takes back every
# background slot (H3.1)
def adm_yield(c: Ad.Cls, l: Ad.Lim, ts: List<&2, Ad.Tk>) -> List<&2, Ad.Tk>:
  match c:
    case Ad.Ia{}:
      match l:
        case Ad.Unl{}:
          ts
        case Ad.Cap{p}:
          adm_taken_back.all(ts)
    case Ad.Bg{}:
      ts

# a waiter: queued, or granted and not collected (H3.8: a leave ends it)
def adm_waiter(x: Ad.Sts) -> Bool:
  match x:
    case Ad.Queued{}:
      True{}
    case Ad.Granted{}:
      True{}
    case Ad.Held{}:
      False{}
    case Ad.Preempted{}:
      False{}
    case Ad.Ended{}:
      False{}

def adm_waiter.at(m: Maybe<&2, Ad.Tk>) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{t}:
      match t:
        case Ad.Tk{c, x}:
          adm_waiter(x)

# a granted ticket, not collected (H3.8: a poll collects it)
def adm_granted.at(m: Maybe<&2, Ad.Tk>) -> Bool:
  match m:
    case Some{Ad.Tk{c, Ad.Granted{}}}:
      True{}
    case _:
      False{}

# a collected permit, or a preempted one (H3.8: a release ends it)
def adm_permit.at(m: Maybe<&2, Ad.Tk>) -> Bool:
  match m:
    case Some{Ad.Tk{c, Ad.Held{}}}:
      True{}
    case Some{Ad.Tk{c, Ad.Preempted{}}}:
      True{}
    case _:
      False{}

# op o applies to its ticket in ts (A3): an admit and new limits always;
# a poll to a granted ticket, a release to a collected or preempted
# permit, a leave to a waiter
def adm_applies(+ts: List<&2, Ad.Tk>, o: Ad.Op) -> Bool:
  match o:
    case Ad.Admit{c}:
      True{}
    case Ad.Collect{k}:
      adm_granted.at(List.get(&2, Ad.Tk, ts, k))
    case Ad.Release{k}:
      adm_permit.at(List.get(&2, Ad.Tk, ts, k))
    case Ad.Leave{k}:
      adm_waiter.at(List.get(&2, Ad.Tk, ts, k))
    case Ad.Limit{l, q}:
      True{}

# Laws: the ops
# -------------

# LAW admission_admit_appends: on every state, an admit of class c adds one ticket, the newest, of class c, and keeps the limits; the new ticket holds a slot at once (held) or waits (queued), or, for an interactive request only, is rejected (ended): never a grant left to collect; every earlier ticket is kept, except that an interactive admit on a provider with an in-flight limit takes back every background slot (a granted background waiter waits again, a collected background permit is preempted) (H3.1, H3.6)
# EXCLUDES: a ticket lost, reordered or of another class; a background
#   request rejected; a preemption on an unlimited provider, of an
#   interactive ticket, of a background ticket holding no slot, or that
#   ends a background request; a granted background waiter kept granted
#   or a collected permit kept; limits changed by an admit
law admission_admit_appends:
  for +l: Ad.Lim
  for +q: Nat
  for +ts: List<&2, Ad.Tk>
  for +c: Ad.Cls
  exs x: Ad.Sts
  {(Ad.step(Ad.St{l, q, ts}, Ad.Admit{c}), adm_fresh(c, x)) == (Ad.St{l, q, List.append(&2, Ad.Tk, adm_yield(c, l, ts), [Ad.Tk{c, x}])}, True{}) : Ad.St & Bool}

# LAW admission_queue_limit: on every state, an interactive admit is rejected (its ticket ends at once) exactly when it does not hold a slot at once and providerMaxQueued (q) interactive requests already wait (H3.6)
# EXCLUDES: a rejection while fewer than q interactive requests wait, or
#   of a request that gets a slot; a request queued past the limit
law admission_queue_limit:
  for +l: Ad.Lim
  for +q: Nat
  for +ts: List<&2, Ad.Tk>
  {adm_ended(adm_last(adm_ts(Ad.step(Ad.St{l, q, ts}, Ad.Admit{Ad.Ia{}})))) == Bool.and(Bool.not(adm_took(adm_last(adm_ts(Ad.step(Ad.St{l, q, ts}, Ad.Admit{Ad.Ia{}}))))), Nat.is_le(q, ads_queued(Ad.Ia{}, ts))) : Bool}

# LAW admission_background_admit_idle: on every state, a background admit holds a slot at once only when no interactive request holds a slot or waits (H3.7)
# EXCLUDES: a background request admitted beside a running or waiting
#   interactive one (with a slot to spare too)
law admission_background_admit_idle:
  for +l: Ad.Lim
  for +q: Nat
  for +ts: List<&2, Ad.Tk>
  for took: {adm_took(adm_last(adm_ts(Ad.step(Ad.St{l, q, ts}, Ad.Admit{Ad.Bg{}})))) == True{} : Bool}
  {(ads_held(Ad.Ia{}, ts), ads_queued(Ad.Ia{}, ts)) == (0n, 0n) : Nat & Nat}

# LAW admission_collect_takes_grant: on every state, a poll of granted ticket k (k tickets before it) collects its permit, and nothing else changes: no ticket, no limit (H3.8)
# EXCLUDES: a grant lost or left uncollected on a poll, another ticket
#   touched, a grant run on a poll
law admission_collect_takes_grant:
  for +l: Ad.Lim
  for +q: Nat
  for +pre: List<&2, Ad.Tk>
  for +c: Ad.Cls
  for +post: List<&2, Ad.Tk>
  {Ad.step(Ad.St{l, q, List.append(&2, Ad.Tk, pre, Ad.Tk{c, Ad.Granted{}} <> post)}, Ad.Collect{List.length(&2, Ad.Tk, pre)}) == Ad.St{l, q, List.append(&2, Ad.Tk, pre, Ad.Tk{c, Ad.Held{}} <> post)} : Ad.St}

# LAW admission_release_grants: on every state, dropping collected permit k (k tickets before it) ends it, and the free slots then go to the waiters by the two passes of ads_grant (interactive oldest first, then background oldest first while no interactive request holds or waits); the limits stay (H3.8)
# EXCLUDES: a slot not passed on, passed to the wrong class or out of
#   order, more slots granted than are free, the permit kept, another
#   ticket ended or changed
law admission_release_grants:
  for +l: Ad.Lim
  for +q: Nat
  for +pre: List<&2, Ad.Tk>
  for +c: Ad.Cls
  for +post: List<&2, Ad.Tk>
  {Ad.step(Ad.St{l, q, List.append(&2, Ad.Tk, pre, Ad.Tk{c, Ad.Held{}} <> post)}, Ad.Release{List.length(&2, Ad.Tk, pre)}) == Ad.St{l, q, ads_grant(l, List.append(&2, Ad.Tk, pre, Ad.Tk{c, Ad.Ended{}} <> post))} : Ad.St}

# LAW admission_release_preempted: on every state, dropping preempted permit k ends it and changes nothing else: its slot went at the preemption, so no grant runs (H3.8)
# EXCLUDES: a slot freed twice (a grant on the drop of a preempted
#   permit), the permit kept
law admission_release_preempted:
  for +l: Ad.Lim
  for +q: Nat
  for +pre: List<&2, Ad.Tk>
  for +c: Ad.Cls
  for +post: List<&2, Ad.Tk>
  {Ad.step(Ad.St{l, q, List.append(&2, Ad.Tk, pre, Ad.Tk{c, Ad.Preempted{}} <> post)}, Ad.Release{List.length(&2, Ad.Tk, pre)}) == Ad.St{l, q, List.append(&2, Ad.Tk, pre, Ad.Tk{c, Ad.Ended{}} <> post)} : Ad.St}

# LAW admission_leave_grants: on every state, dropping waiter k (queued, or granted and not collected; k tickets before it) ends it, and the free slots, its grant among them, go to the waiters by the two passes of ads_grant; the limits stay (H3.8)
# EXCLUDES: a dropped waiter's grant kept or lost, a waiter kept in the
#   queue, a wrong grant after it
law admission_leave_grants:
  for +l: Ad.Lim
  for +q: Nat
  for +pre: List<&2, Ad.Tk>
  for +c: Ad.Cls
  for +x: Ad.Sts
  for +post: List<&2, Ad.Tk>
  for w: {adm_waiter(x) == True{} : Bool}
  {Ad.step(Ad.St{l, q, List.append(&2, Ad.Tk, pre, Ad.Tk{c, x} <> post)}, Ad.Leave{List.length(&2, Ad.Tk, pre)}) == Ad.St{l, q, ads_grant(l, List.append(&2, Ad.Tk, pre, Ad.Tk{c, Ad.Ended{}} <> post))} : Ad.St}

# LAW admission_limits_grant: on every state, new limits take effect at once, and the free slots under them go to the waiters by the two passes of ads_grant (H3.5, H3.8)
# EXCLUDES: limits ignored or kept, waiters left waiting after a raised
#   limit, a lowered limit that revokes held slots
law admission_limits_grant:
  for +l: Ad.Lim
  for +q: Nat
  for +ts: List<&2, Ad.Tk>
  for +l2: Ad.Lim
  for +q2: Nat
  {Ad.step(Ad.St{l, q, ts}, Ad.Limit{l2, q2}) == Ad.St{l2, q2, ads_grant(l2, ts)} : Ad.St}

# LAW admission_inert_ops: on every state, an op that does not apply to its ticket changes nothing: a poll of a ticket not granted, a release of a ticket holding no collected or preempted permit, a leave of a ticket that is no waiter (ended, collected, preempted, or never admitted) (A3, A1)
# EXCLUDES: a double release (a slot granted twice), a revived ended
#   ticket, a stray poll or drop that grants, ends or changes a ticket
law admission_inert_ops:
  for +s: Ad.St
  for +o: Ad.Op
  for no: {adm_applies(adm_ts(s), o) == False{} : Bool}
  {Ad.step(s, o) == s : Ad.St}

# LAW admission_step_example (anchor): at one slot, an interactive request holds it, a second waits, a background one waits; the release grants the interactive waiter; at unlimited slots with no interactive request, two background waiters are granted at once; a full queue rejects; an interactive request preempts the background slots of a capped provider and leaves those of an unlimited one
# EXCLUDES: values the laws above leave open on these states
law admission_step_example:
  {Ad.step(Ad.St{Ad.Cap{0n}, 5n, [Ad.Tk{Ad.Ia{}, Ad.Held{}}, Ad.Tk{Ad.Ia{}, Ad.Queued{}}, Ad.Tk{Ad.Bg{}, Ad.Queued{}}]}, Ad.Release{0n}) == Ad.St{Ad.Cap{0n}, 5n, [Ad.Tk{Ad.Ia{}, Ad.Ended{}}, Ad.Tk{Ad.Ia{}, Ad.Granted{}}, Ad.Tk{Ad.Bg{}, Ad.Queued{}}]} : Ad.St} &
  {Ad.step(Ad.St{Ad.Cap{0n}, 5n, [Ad.Tk{Ad.Bg{}, Ad.Queued{}}, Ad.Tk{Ad.Bg{}, Ad.Queued{}}]}, Ad.Limit{Ad.Unl{}, 5n}) == Ad.St{Ad.Unl{}, 5n, [Ad.Tk{Ad.Bg{}, Ad.Granted{}}, Ad.Tk{Ad.Bg{}, Ad.Granted{}}]} : Ad.St} &
  {Ad.step(Ad.St{Ad.Cap{0n}, 1n, [Ad.Tk{Ad.Ia{}, Ad.Held{}}, Ad.Tk{Ad.Ia{}, Ad.Queued{}}]}, Ad.Admit{Ad.Ia{}}) == Ad.St{Ad.Cap{0n}, 1n, [Ad.Tk{Ad.Ia{}, Ad.Held{}}, Ad.Tk{Ad.Ia{}, Ad.Queued{}}, Ad.Tk{Ad.Ia{}, Ad.Ended{}}]} : Ad.St} &
  {Ad.step(Ad.St{Ad.Cap{1n}, 5n, [Ad.Tk{Ad.Bg{}, Ad.Held{}}, Ad.Tk{Ad.Bg{}, Ad.Granted{}}]}, Ad.Admit{Ad.Ia{}}) == Ad.St{Ad.Cap{1n}, 5n, [Ad.Tk{Ad.Bg{}, Ad.Preempted{}}, Ad.Tk{Ad.Bg{}, Ad.Queued{}}, Ad.Tk{Ad.Ia{}, Ad.Held{}}]} : Ad.St} &
  {Ad.step(Ad.St{Ad.Unl{}, 5n, [Ad.Tk{Ad.Bg{}, Ad.Held{}}, Ad.Tk{Ad.Bg{}, Ad.Granted{}}]}, Ad.Admit{Ad.Ia{}}) == Ad.St{Ad.Unl{}, 5n, [Ad.Tk{Ad.Bg{}, Ad.Held{}}, Ad.Tk{Ad.Bg{}, Ad.Granted{}}, Ad.Tk{Ad.Ia{}, Ad.Held{}}]} : Ad.St}

# Laws: every history
# -------------------

# LAW admission_preempts: on a provider with an in-flight limit, after an interactive admit on any tickets no background slot is held (H3.1)
# EXCLUDES: an interactive request that waits behind background work on a
#   provider that serves only so many requests at once
law admission_preempts:
  for +p: Nat
  for +q: Nat
  for +ts: List<&2, Ad.Tk>
  {ads_held(Ad.Bg{}, adm_ts(Ad.step(Ad.St{Ad.Cap{p}, q, ts}, Ad.Admit{Ad.Ia{}}))) == 0n : Nat}

# LAW admission_unlimited_keeps_background: on an unlimited provider an interactive admit changes no ticket admitted before it: a background request keeps its slot, granted or collected (H3.1)
# EXCLUDES: a background request preempted (stopped and sent again) where
#   no interactive request could wait for its slot, a ticket an admit
#   changes, drops or reorders
law admission_unlimited_keeps_background:
  for q: Nat
  for +ts: List<&2, Ad.Tk>
  for +k: Nat
  for live: {Maybe.is_some(&2, Ad.Tk, List.get(&2, Ad.Tk, ts, k)) == True{} : Bool}
  {List.get(&2, Ad.Tk, adm_ts(Ad.step(Ad.St{Ad.Unl{}, q, ts}, Ad.Admit{Ad.Ia{}})), k) == List.get(&2, Ad.Tk, ts, k) : Maybe<&2, Ad.Tk>}

# LAW admission_capacity: on every state, an op grants only into free slots: after it the slots held are within the limit, or no more than before less the slots the op freed itself (adm_freed: a lowered limit drains, and nothing is granted until below it) (H3.5)
# EXCLUDES: a grant past the limit, a lowered limit that grants while over
#   it
law admission_capacity:
  for +s: Ad.St
  for +o: Ad.Op
  {Bool.or(adm_within(adm_lim(Ad.step(s, o)), ads_busy(adm_ts(Ad.step(s, o)))), Nat.is_le(Nat.add(ads_busy(adm_ts(Ad.step(s, o))), adm_freed(s, o)), ads_busy(adm_ts(s)))) == True{} : Bool}

# LAW admission_no_lost_wakeup: after any history from a new controller (limits l, q, no ticket), no waiter may take a free slot: no slot is free while an interactive request waits, or while a background one waits and no interactive request holds a slot (H3.3)
# EXCLUDES: a waiter left waiting beside a free slot it may take (a missed
#   grant on a release, a leave, new limits or an admit)
law admission_no_lost_wakeup:
  for +l: Ad.Lim
  for +q: Nat
  for +os: List<&2, Ad.Op>
  {adm_grantable(adm_run(os, Ad.St{l, q, Nil{}})) == False{} : Bool}

# LAW admission_background_yields: after any history from a new controller, a background slot is held only while no interactive request waits: a user's request never waits behind background work (H3.1)
# EXCLUDES: an interactive request queued while a background request holds
#   a slot (a capped provider preempts them; an unlimited one has a slot
#   for every interactive request)
law admission_background_yields:
  for +l: Ad.Lim
  for +q: Nat
  for +os: List<&2, Ad.Op>
  {adm_calm(adm_ts(adm_run(os, Ad.St{l, q, Nil{}}))) == True{} : Bool}

# LAW admission_fifo: after any history from a new controller, no request holds a slot while an older one of its class waits: grants within a class go oldest first (H3.2)
# EXCLUDES: a younger waiter served before an older one of its class
law admission_fifo:
  for +l: Ad.Lim
  for +q: Nat
  for +os: List<&2, Ad.Op>
  {adm_fifo_both(adm_ts(adm_run(os, Ad.St{l, q, Nil{}}))) == True{} : Bool}

# LAW admission_interactive_step: on every state, while interactive ticket w waits before and after an op, the op raises nothing w waits for (adm_ahead: the interactive slots held and the interactive waiters ahead of it), and each interactive slot the op frees lowers it (H3.4)
# EXCLUDES: a waiter overtaken (by a younger interactive request or a
#   background one), a freed interactive slot that does not bring w closer
law admission_interactive_step:
  for +s: Ad.St
  for +o: Ad.Op
  for +w: Nat
  for ws: {adm_waits_ia(adm_status(s, w)) == True{} : Bool}
  for wf: {adm_waits_ia(adm_status(Ad.step(s, o), w)) == True{} : Bool}
  {Nat.is_le(Nat.add(adm_frees(s, o), adm_ahead(Ad.step(s, o), w)), adm_ahead(s, w)) == True{} : Bool}

# LAW admission_interactive_bound: after any history from a new controller, an interactive waiter w is granted after at most adm_ahead interactive releases, whatever background requests do: while it keeps waiting through a run, the run freed fewer interactive slots than were ahead of it (H3.4)
# EXCLUDES: an interactive request that waits forever while interactive
#   slots free up (starved by background work or younger requests)
law admission_interactive_bound:
  for +l: Ad.Lim
  for +q: Nat
  for +pre: List<&2, Ad.Op>
  for +os: List<&2, Ad.Op>
  for +w: Nat
  for waits: {adm_waits_thru(os, adm_run(pre, Ad.St{l, q, Nil{}}), w) == True{} : Bool}
  {Nat.is_le(1n+adm_frees_run(os, adm_run(pre, Ad.St{l, q, Nil{}})), adm_ahead(adm_run(pre, Ad.St{l, q, Nil{}}), w)) == True{} : Bool}

# LAW admission_ended_stays_ended: on every state, an ended ticket stays ended, whatever op comes (A1)
# EXCLUDES: an ended ticket revived (granted, queued or held again)
law admission_ended_stays_ended:
  for +s: Ad.St
  for +o: Ad.Op
  for +k: Nat
  for e: {adm_ended(adm_status(s, k)) == True{} : Bool}
  {adm_ended(adm_status(Ad.step(s, o), k)) == True{} : Bool}

# LAW admission_every_ticket_ends: on every state, every ticket ends when its holder drops it (adm_finish: a waiter leaves, a permit is released): no leak (A2)
# EXCLUDES: a dropped ticket that keeps its slot or its place in the queue
law admission_every_ticket_ends:
  for +s: Ad.St
  for +k: Nat
  for live: {Maybe.is_some(&2, Ad.Tk, adm_status(s, k)) == True{} : Bool}
  {adm_ended(adm_status(Ad.step(s, adm_finish(adm_status(s, k), k)), k)) == True{} : Bool}

# Laws: the live controller
# -------------------------
# The live controller (Ad.Live, what eukhe runs) keeps only the live
# tickets, each with its ticket number: an ended ticket leaves, so an op
# costs the live tickets, not every ticket the provider ever admitted.
# Spec helpers: the live tickets of the model's state, numbered.

# ticket k of class c and status s before rest, when it is live
def adl_keep(s: Ad.Sts, k: Nat, c: Ad.Cls, rest: List<&2, Ad.Lv>) -> List<&2, Ad.Lv>:
  match s:
    case Ad.Queued{}:
      Ad.Lv{k, c, Ad.Queued{}} <> rest
    case Ad.Granted{}:
      Ad.Lv{k, c, Ad.Granted{}} <> rest
    case Ad.Held{}:
      Ad.Lv{k, c, Ad.Held{}} <> rest
    case Ad.Preempted{}:
      Ad.Lv{k, c, Ad.Preempted{}} <> rest
    case Ad.Ended{}:
      rest

# the live tickets of ts, the first numbered k
def adl_lives(ts: List<&2, Ad.Tk>, +k: Nat) -> List<&2, Ad.Lv>:
  match ts:
    case Nil{}:
      Nil{}
    case Ad.Tk{c, s} <> r:
      adl_keep(s, k, c, adl_lives(r, 1n+k))

# the model's state as the live controller holds it: the limits, the
# live tickets with their numbers, and the number of the next ticket
def adl_live(s: Ad.St) -> Ad.Live:
  match s:
    case Ad.St{l, q, +ts}:
      Ad.Live{l, q, adl_lives(ts, 0n), List.length(&2, Ad.Tk, ts)}

# the live controller after the ops os, oldest first, from x
def adl_run(os: List<&2, Ad.Op>, x: Ad.Live) -> Ad.Live:
  match os:
    case Nil{}:
      x
    case o <> r:
      adl_run(r, Ad.Live.step(x, o))

# LAW admission_live_step: on any state of the model, an op of the live controller does what the model's op does, the ended tickets left out (A4)
# EXCLUDES: every difference between the live controller and the model
#   (a grant, a preemption, a rejection, a lost or renumbered ticket, an
#   ended ticket kept or revived); with admission_live_run it carries
#   every admission law above to the controller eukhe runs
law admission_live_step:
  for +s: Ad.St
  for +o: Ad.Op
  {Ad.Live.step(adl_live(s), o) == adl_live(Ad.step(s, o)) : Ad.Live}

# LAW admission_live_run: on the live controller of any model state, after any history, the live controller holds the model's live tickets after that history, numbered as the model numbers them (A4)
# EXCLUDES: a controller that drifts from the model over a history
law admission_live_run:
  for +os: List<&2, Ad.Op>
  for +s: Ad.St
  {adl_run(os, adl_live(s)) == adl_live(adm_run(os, s)) : Ad.Live}

# LAW admission_live_example (anchor): at a limit of one, a released permit leaves and its slot goes to the waiter, which keeps its number
# EXCLUDES: an ended ticket kept, tickets renumbered when one leaves
law admission_live_example:
  {adl_run([Ad.Admit{Ad.Ia{}}, Ad.Admit{Ad.Ia{}}, Ad.Release{0n}], Ad.Live{Ad.Cap{0n}, 1n, Nil{}, 0n}) == Ad.Live{Ad.Cap{0n}, 1n, [Ad.Lv{1n, Ad.Ia{}, Ad.Granted{}}], 2n} : Ad.Live}
