# eukhe: the laws of area admission

import Base
import ../bend/admission.bend as Ad
import ../bend/ffi_admission.bend as FAd
import ../bend/wire.bend as Wr
import ./base.bend as LawsBase

# (H3) A user's request never waits behind background work
# ---------------------------------------------------------
# LAWS.bend H3, the model in bend/admission.bend: one provider's
# admission (crates/eukhe-core/src/admission.rs), ticket by ticket. Every
# op is free: admits of either class, polls, drops of permits and of
# waiters, new limits, in any order, on any state.

# LAW admission_preempts: on a capped provider an interactive admit leaves no background slot held (H3.1)
# EXCLUDES: an interactive request that waits behind background work on a
#   provider that serves only so many requests at once
law admission_preempts:
  for p: Nat
  for q: Nat
  for +ts: List<&2, Ad.Tk>
  {Ad.cnt(Ad.Holding{}, Ad.Bg{}, Ad.St.ts(Ad.step(Ad.St{Ad.Cap{p}, q, ts}, Ad.Admit{Ad.Ia{}}))) == 0n : Nat}

# LAW admission_unlimited_keeps_background: on an unlimited provider an interactive admit changes no ticket admitted before it: a background request keeps its slot, granted or collected (H3.1)
# EXCLUDES: a background request preempted (stopped and sent again) where
#   no interactive request could wait for its slot, a ticket an admit
#   changes, drops or reorders
law admission_unlimited_keeps_background:
  for q: Nat
  for +ts: List<&2, Ad.Tk>
  for +k: Nat
  for live: {Maybe.is_some(&2, Ad.Tk, Ad.get(ts, k)) == True{} : Bool}
  {Ad.get(Ad.St.ts(Ad.step(Ad.St{Ad.Unl{}, q, ts}, Ad.Admit{Ad.Ia{}})), k) == Ad.get(ts, k) : Maybe<&2, Ad.Tk>}

# LAW admission_capacity: an op grants only into free slots: after it the slots held are
# within the limit, or no more than before less the slots the op freed
# itself (a lowered limit drains, and nothing is granted until below it)
law admission_capacity:
  for +s: Ad.St
  for +o: Ad.Op
  {Bool.or(Ad.within(Ad.St.lim(Ad.step(s, o)), Ad.held(Ad.St.ts(Ad.step(s, o)))), Ad.le(Nat.add(Ad.held(Ad.St.ts(Ad.step(s, o))), Ad.freed(s, o)), Ad.held(Ad.St.ts(s)))) == True{} : Bool}

# LAW admission_no_lost_wakeup: after any history no waiter may take a free slot: no free slot
# while an interactive request waits, or a background one waits with no
# interactive request holding or waiting (H3.3)
law admission_no_lost_wakeup:
  for +l: Ad.Lim
  for +q: Nat
  for +os: List<&2, Ad.Op>
  {Ad.grantable(Ad.run(os, Ad.St.new(l, q))) == False{} : Bool}

# LAW admission_background_yields: after any history a background slot is held only while no
# interactive request waits: a user's request never waits behind background work (H3.1)
# EXCLUDES: an interactive request queued while a background request holds
#   a slot (a capped provider preempts them; an unlimited one has a slot
#   for every interactive request)
law admission_background_yields:
  for +l: Ad.Lim
  for +q: Nat
  for +os: List<&2, Ad.Op>
  {Ad.calm(Ad.St.ts(Ad.run(os, Ad.St.new(l, q)))) == True{} : Bool}

# LAW admission_fifo: after any history no request holds a slot while an older one of
# its class waits: grants within a class go oldest first (H3.2)
law admission_fifo:
  for +l: Ad.Lim
  for +q: Nat
  for +os: List<&2, Ad.Op>
  {Ad.fifo.both(Ad.St.ts(Ad.run(os, Ad.St.new(l, q)))) == True{} : Bool}

# LAW admission_interactive_step: while interactive ticket w waits, no op raises what it waits for
# (the interactive slots held and the interactive waiters ahead of it),
# and each interactive slot an op frees lowers it (H3.4)
law admission_interactive_step:
  for +s: Ad.St
  for +o: Ad.Op
  for +w: Nat
  for ws: {Ad.waits.ia(Ad.status(s, w)) == True{} : Bool}
  for wf: {Ad.waits.ia(Ad.status(Ad.step(s, o), w)) == True{} : Bool}
  {Ad.le(Nat.add(Ad.frees(s, o), Ad.ahead(Ad.step(s, o), w)), Ad.ahead(s, w)) == True{} : Bool}

# LAW admission_interactive_bound: so an interactive waiter w is granted after at most ahead(s, w)
# interactive releases, whatever background requests do: while it keeps
# waiting through a run, the run freed fewer interactive slots (H3.4)
law admission_interactive_bound:
  for +l: Ad.Lim
  for +q: Nat
  for +pre: List<&2, Ad.Op>
  for +os: List<&2, Ad.Op>
  for +w: Nat
  for waits: {Ad.waits.thru(os, Ad.run(pre, Ad.St.new(l, q)), w) == True{} : Bool}
  {Ad.le(1n+Ad.frees.run(os, Ad.run(pre, Ad.St.new(l, q))), Ad.ahead(Ad.run(pre, Ad.St.new(l, q)), w)) == True{} : Bool}

# LAW admission_ended_stays_ended: an ended ticket stays ended, whatever op comes
law admission_ended_stays_ended:
  for +s: Ad.St
  for +o: Ad.Op
  for +k: Nat
  for e: {Ad.ended(Ad.status(s, k)) == True{} : Bool}
  {Ad.ended(Ad.status(Ad.step(s, o), k)) == True{} : Bool}

# LAW admission_end_twice_changes_nothing: ending an ended ticket again changes nothing: no double release
law admission_end_twice_changes_nothing:
  for +s: Ad.St
  for +k: Nat
  for e: {Ad.ended(Ad.status(s, k)) == True{} : Bool}
  {Ad.step(s, Ad.finish(Ad.status(s, k), k)) == s : Ad.St}

# LAW admission_every_ticket_ends: every ticket ends when its holder drops it (a waiter leaves, a
# permit is released): no leak
law admission_every_ticket_ends:
  for +s: Ad.St
  for +k: Nat
  for live: {Maybe.is_some(&2, Ad.Tk, Ad.status(s, k)) == True{} : Bool}
  {Ad.ended(Ad.status(Ad.step(s, Ad.finish(Ad.status(s, k), k)), k)) == True{} : Bool}

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

# LAW admission_live_step: on any state of the model, an op of the live controller does what
# the model's op does, the ended tickets left out
# EXCLUDES: every difference between the live controller and the model
#   (a grant, a preemption, a rejection, a lost or renumbered ticket, an
#   ended ticket kept or revived); with admission_live_run it carries
#   every admission law above to the controller eukhe runs
law admission_live_step:
  for +s: Ad.St
  for +o: Ad.Op
  {Ad.Live.step(adl_live(s), o) == adl_live(Ad.step(s, o)) : Ad.Live}

# LAW admission_live_run: after any history, the live controller holds the model's live
# tickets, numbered as the model numbers them
# EXCLUDES: a controller that drifts from the model over a history
law admission_live_run:
  for l: Ad.Lim
  for q: Nat
  for os: List<&2, Ad.Op>
  {Ad.Live.run(os, Ad.Live.new(l, q)) == adl_live(Ad.run(os, Ad.St.new(l, q))) : Ad.Live}

# LAW admission_live_example (anchor): at a limit of one, a released permit leaves and its slot
# goes to the waiter, which keeps its number
# EXCLUDES: an ended ticket kept, tickets renumbered when one leaves
law admission_live_example:
  {Ad.Live.run([Ad.Admit{Ad.Ia{}}, Ad.Admit{Ad.Ia{}}, Ad.Release{0n}], Ad.Live.new(Ad.Cap{0n}, 1n)) == Ad.Live{Ad.Cap{0n}, 1n, [Ad.Lv{1n, Ad.Ia{}, Ad.Granted{}}], 2n} : Ad.Live}

# The controller, whole
# ---------------------
# Written from the requirement (H3, M2: crates/eukhe-core/src/admission.rs
# `ControllerState`), never calling the model: the laws above pin
# properties of Ad.step; admission_step_exact pins its every answer. The
# grant is stated as two passes over the waiters (interactive ones first,
# then background ones only while no interactive request holds a slot or
# waits), each oldest first while a slot is free, not as the model's
# one-waiter-at-a-time loop.

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

# an interactive request frees every background slot: a granted waiter
# waits again, a collected permit is preempted
def ads_preempt1(t: Ad.Tk) -> Ad.Tk:
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

def ads_preempt(ts: List<&2, Ad.Tk>) -> List<&2, Ad.Tk>:
  match ts:
    case Nil{}:
      Nil{}
    case h <> r:
      ads_preempt1(h) <> ads_preempt(r)

# what an interactive request does to the tickets before it: on a capped
# provider it frees every background slot; on an unlimited one, which has
# a slot for every request, it leaves them
def ads_yield(l: Ad.Lim, ts: List<&2, Ad.Tk>) -> List<&2, Ad.Tk>:
  match l:
    case Ad.Unl{}:
      ts
    case Ad.Cap{p}:
      ads_preempt(ts)

# a new interactive request: a slot when one is free for it (the
# interactive slots below the limit) and no interactive request waits;
# else rejected (ended) once q interactive requests wait; else it waits
def ads_ia_status(free: Bool, full: Bool) -> Ad.Sts:
  match free:
    case True{}:
      Ad.Held{}
    case False{}:
      match full:
        case True{}:
          Ad.Ended{}
        case False{}:
          Ad.Queued{}

def ads_admit_ia(+l: Ad.Lim, +q: Nat, +ts: List<&2, Ad.Tk>) -> List<&2, Ad.Tk>:
  +wi = ads_queued(Ad.Ia{}, ts)
  List.append(&2, Ad.Tk, ads_yield(l, ts), [Ad.Tk{Ad.Ia{}, ads_ia_status(Bool.and(Nat.is_eq(wi, 0n), ads_room(l, ads_held(Ad.Ia{}, ts))), Nat.is_le(q, wi))}])

def ads_bg_status(free: Bool) -> Ad.Sts:
  match free:
    case True{}:
      Ad.Held{}
    case False{}:
      Ad.Queued{}

# a new background request: a slot when no interactive request holds one
# or waits, no request waits and a slot is free; else it waits (never
# rejected)
def ads_admit_bg(+l: Ad.Lim, +ts: List<&2, Ad.Tk>) -> List<&2, Ad.Tk>:
  List.append(&2, Ad.Tk, ts, [Ad.Tk{Ad.Bg{}, ads_bg_status(Bool.and(Nat.is_eq(ads_held(Ad.Ia{}, ts), 0n), Bool.and(Nat.is_eq(ads_queued(Ad.Ia{}, ts), 0n), Bool.and(Nat.is_eq(ads_queued(Ad.Bg{}, ts), 0n), ads_room(l, ads_busy(ts))))))}])

# ticket k gets status x (no ticket k: nothing changes)
def ads_set(ts: List<&2, Ad.Tk>, k: Nat, x: Ad.Sts) -> List<&2, Ad.Tk>:
  match ts:
    case Nil{}:
      Nil{}
    case Ad.Tk{c, s} <> r:
      match k:
        case 0n:
          Ad.Tk{c, x} <> r
        case 1n+j:
          Ad.Tk{c, s} <> ads_set(r, j, x)

# a waiter polls: a granted permit is collected; nothing else changes
def ads_collect(m: Maybe<&2, Ad.Tk>, l: Ad.Lim, q: Nat, ts: List<&2, Ad.Tk>, k: Nat) -> Ad.St:
  match m:
    case Some{Ad.Tk{c, Ad.Granted{}}}:
      Ad.St{l, q, ads_set(ts, k, Ad.Held{})}
    case _:
      Ad.St{l, q, ts}

# a collected permit drops: it ends and its slot goes to the waiters; a
# preempted one ends (its slot was freed); nothing else changes
def ads_release(m: Maybe<&2, Ad.Tk>, +l: Ad.Lim, q: Nat, ts: List<&2, Ad.Tk>, k: Nat) -> Ad.St:
  match m:
    case Some{Ad.Tk{c, Ad.Held{}}}:
      Ad.St{l, q, ads_grant(l, ads_set(ts, k, Ad.Ended{}))}
    case Some{Ad.Tk{c, Ad.Preempted{}}}:
      Ad.St{l, q, ads_set(ts, k, Ad.Ended{})}
    case _:
      Ad.St{l, q, ts}

# a waiter drops (granted or not): it ends and a slot it was granted goes
# to the waiters; nothing else changes
def ads_leave(m: Maybe<&2, Ad.Tk>, +l: Ad.Lim, q: Nat, ts: List<&2, Ad.Tk>, k: Nat) -> Ad.St:
  match m:
    case Some{Ad.Tk{c, Ad.Queued{}}}:
      Ad.St{l, q, ads_grant(l, ads_set(ts, k, Ad.Ended{}))}
    case Some{Ad.Tk{c, Ad.Granted{}}}:
      Ad.St{l, q, ads_grant(l, ads_set(ts, k, Ad.Ended{}))}
    case _:
      Ad.St{l, q, ts}

# one op on the controller (ticket k is the k-th admitted, oldest 0)
def ads_step(s: Ad.St, o: Ad.Op) -> Ad.St:
  match s:
    case Ad.St{+l, +q, +ts}:
      match o:
        case Ad.Admit{c}:
          match c:
            case Ad.Ia{}:
              Ad.St{l, q, ads_admit_ia(l, q, ts)}
            case Ad.Bg{}:
              Ad.St{l, q, ads_admit_bg(l, ts)}
        case Ad.Collect{+k}:
          ads_collect(List.get(&2, Ad.Tk, ts, k), l, q, ts, k)
        case Ad.Release{+k}:
          ads_release(List.get(&2, Ad.Tk, ts, k), l, q, ts, k)
        case Ad.Leave{+k}:
          ads_leave(List.get(&2, Ad.Tk, ts, k), l, q, ts, k)
        case Ad.Limit{+l2, q2}:
          Ad.St{l2, q2, ads_grant(l2, ts)}

# LAW admission_step_exact: every op on every state of the model is the spec's: an interactive admit on a capped provider preempts every background slot (on an unlimited one it changes no ticket) and holds a slot when one is free for it and no interactive request waits, is rejected once q of them wait, else waits; a background admit holds a slot only when no interactive request holds or waits, none waits and a slot is free, else waits; a collect takes a granted permit; a release ends a collected or preempted permit, and a collected one's slot is granted; a leave ends a waiter and its grant is granted; new limits take effect; each grant gives the free slots to the interactive waiters oldest first, then, while no interactive request holds or waits, to the background waiters oldest first
# EXCLUDES: a wrong grant, preemption, rejection or status, a slot left
#   free while a waiter may take it, a ticket other than the op's changed
law admission_step_exact:
  for +s: Ad.St
  for +o: Ad.Op
  {Ad.step(s, o) == ads_step(s, o) : Ad.St}

# LAW admission_spec_example (anchor): at one slot, an interactive request holds it, a second waits, a background one waits; the release grants the interactive waiter; at unlimited slots with no interactive request, two background waiters are granted at once; a full queue rejects; an interactive request preempts the background slots of a capped provider and leaves those of an unlimited one
# EXCLUDES: a vacuous admission_step_exact (a spec whose grant never runs)
law admission_spec_example:
  {ads_step(Ad.St{Ad.Cap{0n}, 5n, [Ad.Tk{Ad.Ia{}, Ad.Held{}}, Ad.Tk{Ad.Ia{}, Ad.Queued{}}, Ad.Tk{Ad.Bg{}, Ad.Queued{}}]}, Ad.Release{0n}) == Ad.St{Ad.Cap{0n}, 5n, [Ad.Tk{Ad.Ia{}, Ad.Ended{}}, Ad.Tk{Ad.Ia{}, Ad.Granted{}}, Ad.Tk{Ad.Bg{}, Ad.Queued{}}]} : Ad.St} &
  {ads_step(Ad.St{Ad.Cap{0n}, 5n, [Ad.Tk{Ad.Bg{}, Ad.Queued{}}, Ad.Tk{Ad.Bg{}, Ad.Queued{}}]}, Ad.Limit{Ad.Unl{}, 5n}) == Ad.St{Ad.Unl{}, 5n, [Ad.Tk{Ad.Bg{}, Ad.Granted{}}, Ad.Tk{Ad.Bg{}, Ad.Granted{}}]} : Ad.St} &
  {ads_step(Ad.St{Ad.Cap{0n}, 1n, [Ad.Tk{Ad.Ia{}, Ad.Held{}}, Ad.Tk{Ad.Ia{}, Ad.Queued{}}]}, Ad.Admit{Ad.Ia{}}) == Ad.St{Ad.Cap{0n}, 1n, [Ad.Tk{Ad.Ia{}, Ad.Held{}}, Ad.Tk{Ad.Ia{}, Ad.Queued{}}, Ad.Tk{Ad.Ia{}, Ad.Ended{}}]} : Ad.St} &
  {ads_step(Ad.St{Ad.Cap{1n}, 5n, [Ad.Tk{Ad.Bg{}, Ad.Held{}}, Ad.Tk{Ad.Bg{}, Ad.Granted{}}]}, Ad.Admit{Ad.Ia{}}) == Ad.St{Ad.Cap{1n}, 5n, [Ad.Tk{Ad.Bg{}, Ad.Preempted{}}, Ad.Tk{Ad.Bg{}, Ad.Queued{}}, Ad.Tk{Ad.Ia{}, Ad.Held{}}]} : Ad.St} &
  {ads_step(Ad.St{Ad.Unl{}, 5n, [Ad.Tk{Ad.Bg{}, Ad.Held{}}, Ad.Tk{Ad.Bg{}, Ad.Granted{}}]}, Ad.Admit{Ad.Ia{}}) == Ad.St{Ad.Unl{}, 5n, [Ad.Tk{Ad.Bg{}, Ad.Held{}}, Ad.Tk{Ad.Bg{}, Ad.Granted{}}, Ad.Tk{Ad.Ia{}, Ad.Held{}}]} : Ad.St}

# ---- admission_wire ----

# The wire codec of bend/ffi_admission.bend (the stepper of the compiled
# Bend core; grammar: that file's header, crates/eukhe-bend/WIRE.md). R1:
# every value the stepper and Rust exchange reads back; R2: a well-formed
# open or step answers the model's new controller, encoded; R3: a
# malformed or overlong input answers the error form and changes nothing.
# Every input is free: any limits, any op, any controller, any text.

# what fits the wire: every Nat (and every list length) at most 14 digits
def adw_lim_fits(l: Ad.Lim) -> Bool:
  match l:
    case Ad.Unl{}:
      True{}
    case Ad.Cap{p}:
      LawsBase.wire_fits(p)

def adw_lv_fits(t: Ad.Lv) -> Bool:
  match t:
    case Ad.Lv{k, c, s}:
      LawsBase.wire_fits(k)

def adw_lvs_fit(ts: List<&2, Ad.Lv>) -> Bool:
  match ts:
    case Nil{}:
      True{}
    case Con{t, u}:
      Bool.and(adw_lv_fits(t), adw_lvs_fit(u))

def adw_live_fits(x: Ad.Live) -> Bool:
  match x:
    case Ad.Live{l, q, +ts, n}:
      Bool.and(adw_lim_fits(l), Bool.and(LawsBase.wire_fits(q), Bool.and(Bool.and(LawsBase.wire_fits(List.length(&2, Ad.Lv, ts)), adw_lvs_fit(ts)), LawsBase.wire_fits(n))))

def adw_op_fits(o: Ad.Op) -> Bool:
  match o:
    case Ad.Admit{c}:
      True{}
    case Ad.Collect{k}:
      LawsBase.wire_fits(k)
    case Ad.Release{k}:
      LawsBase.wire_fits(k)
    case Ad.Leave{k}:
      LawsBase.wire_fits(k)
    case Ad.Limit{l, q}:
      Bool.and(adw_lim_fits(l), LawsBase.wire_fits(q))

# LAW adw_cls_round_trip (R1): a ticket's class reads back, and the rest is untouched
# EXCLUDES: swapped class tags, a class that eats the rest
law adw_cls_round_trip:
  for c: Ad.Cls
  for rest: String
  {FAd.get_cls(FAd.put_cls(c, rest)) == Wr.Got{c, rest} : Wr.Dec<Ad.Cls>}

# LAW adw_sts_round_trip (R1): a ticket's status reads back, and the rest is untouched
# EXCLUDES: two statuses with one tag, a status read as another
law adw_sts_round_trip:
  for s: Ad.Sts
  for rest: String
  {FAd.get_sts(FAd.put_sts(s, rest)) == Wr.Got{s, rest} : Wr.Dec<Ad.Sts>}

# LAW adw_lim_round_trip (R1): a limit that fits reads back, and the rest is untouched
# EXCLUDES: a cap read as unlimited, a misread slot count
law adw_lim_round_trip:
  for +l: Ad.Lim
  for rest: String
  for h: {adw_lim_fits(l) == True{} : Bool}
  {FAd.get_lim(FAd.put_lim(l, rest)) == Wr.Got{l, rest} : Wr.Dec<Ad.Lim>}

# LAW adw_lv_round_trip (R1): a live ticket that fits reads back, and the rest is untouched
# EXCLUDES: a ticket's number, class or status lost or misread
law adw_lv_round_trip:
  for +t: Ad.Lv
  for rest: String
  for h: {adw_lv_fits(t) == True{} : Bool}
  {FAd.get_lv(FAd.put_lv(t, rest)) == Wr.Got{t, rest} : Wr.Dec<Ad.Lv>}

# LAW adw_lvs_round_trip (R1): a list of live tickets that fit, of a length that fits, reads back
# EXCLUDES: tickets lost, added, reordered or misread, a wrong count
law adw_lvs_round_trip:
  for +ts: List<&2, Ad.Lv>
  for rest: String
  for h: {Bool.and(LawsBase.wire_fits(List.length(&2, Ad.Lv, ts)), adw_lvs_fit(ts)) == True{} : Bool}
  {Wr.get_list(~Ad.Lv, ~FAd.get_lv, Wr.put_list(~Ad.Lv, ~FAd.put_lv, ts, rest)) == Wr.Got{ts, rest} : Wr.Dec<List<&2, Ad.Lv>>}

# LAW adw_live_round_trip (R1): the reply, a controller that fits, reads back
# EXCLUDES: a reply that drops or misreads the limits, a ticket or the
#   next ticket's number
law adw_live_round_trip:
  for +x: Ad.Live
  for rest: String
  for h: {adw_live_fits(x) == True{} : Bool}
  {FAd.get_live(FAd.put_live(x, rest)) == Wr.Got{x, rest} : Wr.Dec<Ad.Live>}

# LAW adw_op_round_trip (R1): the request of a step, an op that fits, reads back
# EXCLUDES: one op read as another, a misread ticket number or limit
law adw_op_round_trip:
  for +o: Ad.Op
  for rest: String
  for h: {adw_op_fits(o) == True{} : Bool}
  {FAd.get_op(FAd.put_op(o, rest)) == Wr.Got{o, rest} : Wr.Dec<Ad.Op>}

# LAW adw_open_round_trip (R1): the request of an open, limits that fit, reads back
# EXCLUDES: the limit and providerMaxQueued swapped or misread
law adw_open_round_trip:
  for +l: Ad.Lim
  for +q: Nat
  for rest: String
  for h: {Bool.and(adw_lim_fits(l), LawsBase.wire_fits(q)) == True{} : Bool}
  {FAd.get_open(FAd.put_lim(l, Wr.put_nat(q, rest))) == Wr.Got{(l, q), rest} : Wr.Dec<+Sigma<Ad.Lim, x => Nat>>}

# LAW adw_open_answers (R2): an encoded open runs the model's open: the new controller, and
# its encoding as the reply
# EXCLUDES: an open that ignores or misreads its limits, a reply that is
#   not the state kept
law adw_open_answers:
  for +l: Ad.Lim
  for +q: Nat
  for h: {Bool.and(adw_lim_fits(l), LawsBase.wire_fits(q)) == True{} : Bool}
  {FAd.open(FAd.put_lim(l, Wr.put_nat(q, ""))) == (FAd.Running{Ad.Live.new(l, q)}, FAd.put_live(Ad.Live.new(l, q), "")) : FAd.St & String}

# LAW adw_step_answers (R2): an encoded op runs the model's step on the kept controller: the
# new controller, and its encoding as the reply
# EXCLUDES: a step that drops or reorders ops, a state that drifts from
#   the model, a reply that is not the state kept
law adw_step_answers:
  for +x: Ad.Live
  for +o: Ad.Op
  for h: {adw_op_fits(o) == True{} : Bool}
  {FAd.step(FAd.Running{x}, FAd.put_op(o, "")) == (FAd.Running{Ad.Live.step(x, o)}, FAd.put_live(Ad.Live.step(x, o), "")) : FAd.St & String}

# LAW adw_open_malformed (R3): a malformed open opens the refused state, with the error form
# EXCLUDES: a default controller for malformed limits
law adw_open_malformed:
  for +s: String
  for h: {FAd.get_open(s) == Wr.Bad{} : Wr.Dec<+Sigma<Ad.Lim, x => Nat>>}
  {FAd.open(s) == (FAd.Shut{}, Wr.err("admission: malformed open")) : FAd.St & String}

# LAW adw_open_left_over (R3): an open with input left over is refused too
# EXCLUDES: an open that ignores trailing input
law adw_open_left_over:
  for +l: Ad.Lim
  for +q: Nat
  for c: Char
  for rest: String
  for h: {Bool.and(adw_lim_fits(l), LawsBase.wire_fits(q)) == True{} : Bool}
  {FAd.open(FAd.put_lim(l, Wr.put_nat(q, SCon{c, rest}))) == (FAd.Shut{}, Wr.err("admission: input left over")) : FAd.St & String}

# LAW adw_step_malformed (R3): a malformed op answers the error form and keeps the controller
# EXCLUDES: a guessed op, a controller lost or changed by a bad input
law adw_step_malformed:
  for x: Ad.Live
  for +s: String
  for h: {FAd.get_op(s) == Wr.Bad{} : Wr.Dec<Ad.Op>}
  {FAd.step(FAd.Running{x}, s) == (FAd.Running{x}, Wr.err("admission: malformed op")) : FAd.St & String}

# LAW adw_step_left_over (R3): an op with input left over answers the error form and keeps the
# controller
# EXCLUDES: a step that runs an op followed by garbage
law adw_step_left_over:
  for x: Ad.Live
  for +o: Ad.Op
  for c: Char
  for rest: String
  for h: {adw_op_fits(o) == True{} : Bool}
  {FAd.step(FAd.Running{x}, FAd.put_op(o, SCon{c, rest})) == (FAd.Running{x}, Wr.err("admission: input left over")) : FAd.St & String}

# LAW adw_shut_refuses (R3): the refused state answers every step with the error form
# EXCLUDES: a refused open that later runs ops on a made-up controller
law adw_shut_refuses:
  for s: String
  {FAd.step(FAd.Shut{}, s) == (FAd.Shut{}, Wr.err("admission: the open was refused")) : FAd.St & String}

# LAW adw_tags_example (R1): anchor: the tags of the header (Cls 0 interactive | 1 background;
# Sts 0 queued | 1 granted | 2 held | 3 preempted | 4 ended)
# EXCLUDES: tags in another order than the grammar's
law adw_tags_example:
  {FAd.put_cls(Ad.Ia{}, FAd.put_cls(Ad.Bg{}, "")) == "0,1," : String} & {FAd.put_sts(Ad.Queued{}, FAd.put_sts(Ad.Granted{}, FAd.put_sts(Ad.Held{}, FAd.put_sts(Ad.Preempted{}, FAd.put_sts(Ad.Ended{}, ""))))) == "0,1,2,3,4," : String}

# LAW adw_lim_example (R1): anchor and witness: a cap of 1 + 2 slots is 1, 2
# EXCLUDES: a vacuous adw_lim_round_trip, a cap spelled otherwise
law adw_lim_example:
  {adw_lim_fits(Ad.Cap{2n}) == True{} : Bool} & {FAd.put_lim(Ad.Cap{2n}, FAd.put_lim(Ad.Unl{}, "")) == "1,2,0," : String}

# LAW adw_lv_example (R1): anchor and witness: a live ticket is its number, class, status
# EXCLUDES: a vacuous adw_lv_round_trip, fields in another order
law adw_lv_example:
  {adw_lv_fits(Ad.Lv{3n, Ad.Bg{}, Ad.Preempted{}}) == True{} : Bool} & {FAd.put_lv(Ad.Lv{3n, Ad.Bg{}, Ad.Preempted{}}, "") == "3,1,3," : String}

# LAW adw_lvs_example (R1): anchor and witness: a list of tickets is its count, then them
# EXCLUDES: a vacuous adw_lvs_round_trip
law adw_lvs_example:
  {Bool.and(LawsBase.wire_fits(List.length(&2, Ad.Lv, [Ad.Lv{0n, Ad.Ia{}, Ad.Queued{}}, Ad.Lv{1n, Ad.Bg{}, Ad.Ended{}}])), adw_lvs_fit([Ad.Lv{0n, Ad.Ia{}, Ad.Queued{}}, Ad.Lv{1n, Ad.Bg{}, Ad.Ended{}}])) == True{} : Bool} & {Wr.put_list(~Ad.Lv, ~FAd.put_lv, [Ad.Lv{0n, Ad.Ia{}, Ad.Queued{}}, Ad.Lv{1n, Ad.Bg{}, Ad.Ended{}}], "") == "2,0,0,0,1,1,4," : String}

# LAW adw_live_example (R1): anchor and witness: a controller is its limit, providerMaxQueued,
# live tickets and next ticket's number
# EXCLUDES: a vacuous adw_live_round_trip, fields in another order
law adw_live_example:
  {adw_live_fits(Ad.Live{Ad.Cap{0n}, 1n, [Ad.Lv{1n, Ad.Ia{}, Ad.Granted{}}], 2n}) == True{} : Bool} & {FAd.put_live(Ad.Live{Ad.Cap{0n}, 1n, [Ad.Lv{1n, Ad.Ia{}, Ad.Granted{}}], 2n}, "") == "1,0,1,1,1,0,1,2," : String}

# LAW adw_op_example (R1): anchor and witness: every op's tag and fields
# EXCLUDES: a vacuous adw_op_round_trip, op tags in another order
law adw_op_example:
  {adw_op_fits(Ad.Limit{Ad.Cap{2n}, 3n}) == True{} : Bool} & {FAd.put_op(Ad.Admit{Ad.Bg{}}, FAd.put_op(Ad.Collect{5n}, FAd.put_op(Ad.Release{6n}, FAd.put_op(Ad.Leave{7n}, FAd.put_op(Ad.Limit{Ad.Cap{2n}, 3n}, ""))))) == "0,1,1,5,2,6,3,7,4,1,2,3," : String}

# LAW adw_open_example (R2): anchor and witness: open on 0, 3 (unlimited, 3 queued) answers
# the controller with no ticket
# EXCLUDES: a vacuous adw_open_answers, an open that grants or numbers
#   tickets before any op
law adw_open_example:
  {Bool.and(adw_lim_fits(Ad.Unl{}), LawsBase.wire_fits(3n)) == True{} : Bool} & {FAd.open("0,3,") == (FAd.Running{Ad.Live{Ad.Unl{}, 3n, Nil{}, 0n}}, "0,3,0,0,") : FAd.St & String}

# LAW adw_malformed_example (R3): witness: malformed inputs exist (an unknown limit tag, an
# unknown op tag)
# EXCLUDES: a vacuous adw_open_malformed or adw_step_malformed
law adw_malformed_example:
  {FAd.get_open("2,0,") == Wr.Bad{} : Wr.Dec<+Sigma<Ad.Lim, x => Nat>>} & {FAd.get_op("5,") == Wr.Bad{} : Wr.Dec<Ad.Op>}
