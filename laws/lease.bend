# eukhe: the laws of area lease

import Base
import ../bend/lease.bend as Ls
import ../bend/ffi_lease.bend as FLs
import ../bend/wire.bend as Wr
import ./base.bend as LawsBase

# (H6) Every other wait has an exit
# ---------------------------------
# docs/harness.md H6. A wait (bend/wait.bend) sees, one at a time and in
# any order, its event, ticks of time, and the cancel; dl is its deadline
# in ticks (None: none). The root-turn lease (bend/lease.bend) takes any
# sequence of asks, releases, stops and crashes.

# LAW lease_fifo: first come, first served: after any events, the holder asked
# before every waiter, and the waiters wait in the order they asked
law lease_fifo:
  for +evs: List<&2, Ls.Ev>
  Ls.Fifo(Ls.run(evs))

# LAW lease_never_idle: after any events, the lease is held or no live waiter waits: a
# release or a crash hands it to the next waiter at once
law lease_never_idle:
  for +evs: List<&2, Ls.Ev>
  Ls.Busy(Ls.run(evs))

# LAW lease_keeps_waiters: in any state, an event that does not end a live waiter (its
# release, its stop, its origin's crash) leaves it waiting or holding
law lease_keeps_waiters:
  for +s: Ls.L
  for +e: Ls.Ev
  for +k: Nat
  for +o: Nat
  for waits: Ls.In(Ls.Waiter{k, o, True{}}, Ls.L.queue(s))
  for other: {Ls.hits(e, Ls.Waiter{k, o, True{}}) == False{} : Bool}
  Ls.Kept(k, o, Ls.step(s, e))

# LAW lease_stop_never_holds: a waiter that stopped waiting never holds the lease, whatever
# comes after
law lease_stop_never_holds:
  for +evs: List<&2, Ls.Ev>
  for +k: Nat
  for +o: Nat
  for +rest: List<&2, Ls.Ev>
  for waits: Ls.In(Ls.Waiter{k, o, True{}}, Ls.L.queue(Ls.run(evs)))
  Ls.NotHeld(k, Ls.L.holder(Ls.go(rest, Ls.step(Ls.run(evs), Ls.Stop{k}))))

# LAW lease_crash_frees: in any state, a crash ends every lease of its origin, held or
# waited for
law lease_crash_frees:
  for +s: Ls.L
  for +p: Nat
  Ls.Freed(p, Ls.step(s, Ls.Crash{p}))

# (H6.2) The lease runs as the compiled Bend core
# -----------------------------------------------
# The chat memory's owner (crates/eukhe-core/src/memory/service/turn.rs
# `Turns`) keeps one state of the stepper bend/ffi_lease.bend and sends it
# each event as it comes: an ask (its origin: 0 the owner's process, c + 1
# client connection c), a release (the key its ask got), a crash (a
# connection's origin). It keeps only the replies of the waiters, by key,
# and acts on each answer: it grants the lease to the key the answer
# grants and drops the replies of the keys it ended. The owner sends no
# stop: a waiter that stopped waiting is found when its grant cannot be
# delivered, and the owner then releases that key at once
# (lease_undelivered_is_stopped: the lease ends as if the waiter had
# stopped before the grant).
#
# The laws below speak of the stepper through spellers and a reader built
# from the wire's primitives (bend/wire.bend), not through the entry's own
# codec.

# Spellers and the reader
# -----------------------

# the events the owner sends: every one but a stop, its number within the
# wire
def lw_fits(e: Ls.Ev) -> Bool:
  match e:
    case Ls.Ask{o}:
      LawsBase.wire_fits(o)
    case Ls.Release{k}:
      LawsBase.wire_fits(k)
    case Ls.Stop{k}:
      False{}
    case Ls.Crash{o}:
      LawsBase.wire_fits(o)

# an event as the owner writes it: a tag (0 ask, 1 release, 2 crash), then
# its number (a stop has no spelling: the owner sends none)
def lw_spell_ev(e: Ls.Ev) -> String:
  match e:
    case Ls.Ask{o}:
      Wr.put_nat(0n, Wr.put_nat(o, ""))
    case Ls.Release{k}:
      Wr.put_nat(1n, Wr.put_nat(k, ""))
    case Ls.Stop{k}:
      ""
    case Ls.Crash{o}:
      Wr.put_nat(2n, Wr.put_nat(o, ""))

def lw_read.ev(r: Wr.Dec<Nat>, t: Nat) -> Wr.Dec<Ls.Ev>:
  match r:
    case Wr.Got{x, s}:
      match t:
        case 0n:
          Wr.Got{Ls.Ask{x}, s}
        case 1n:
          Wr.Got{Ls.Release{x}, s}
        case 2n:
          Wr.Got{Ls.Crash{x}, s}
        case 3n+p:
          Wr.Bad{}
    case Wr.Bad{}:
      Wr.Bad{}

def lw_read.go(r: Wr.Dec<Nat>) -> Wr.Dec<Ls.Ev>:
  match r:
    case Wr.Got{t, s}:
      lw_read.ev(Wr.get_nat(s), t)
    case Wr.Bad{}:
      Wr.Bad{}

def lw_read.end(whole: Bool, e: Ls.Ev) -> Maybe<&2, Ls.Ev>:
  match whole:
    case True{}:
      Some{e}
    case False{}:
      None{}

def lw_read.whole(r: Wr.Dec<Ls.Ev>) -> Maybe<&2, Ls.Ev>:
  match r:
    case Wr.Got{e, s}:
      lw_read.end(Wr.end(s), e)
    case Wr.Bad{}:
      None{}

# the event s is, when s is exactly one event the owner can send
def lw_read(s: String) -> Maybe<&2, Ls.Ev>:
  lw_read.whole(lw_read.go(Wr.get_nat(s)))

# The answer
# ----------

# whether m is the key k
def lw_is(m: Maybe<&2, Nat>, +k: Nat) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{j}:
      Nat.is_eq(j, k)

def lw_grant.new(held: Bool, k: Nat) -> Maybe<&2, Nat>:
  match held:
    case True{}:
      None{}
    case False{}:
      Some{k}

# the grant: the key of the lease held after, when it was not held before
def lw_grant(after: Maybe<&2, Nat>, before: Maybe<&2, Nat>) -> Maybe<&2, Nat>:
  match after:
    case None{}:
      None{}
    case Some{+k}:
      lw_grant.new(lw_is(before, k), k)

def lw_keys.queue(q: List<&2, Ls.Waiter>) -> List<&2, Nat>:
  match q:
    case Nil{}:
      Nil{}
    case w <> t:
      Ls.Waiter.key(w) <> lw_keys.queue(t)

def lw_keys.of(m: Maybe<&2, Nat>, ks: List<&2, Nat>) -> List<&2, Nat>:
  match m:
    case None{}:
      ks
    case Some{k}:
      k <> ks

# every key s holds or queues: the holder's, then each waiter's, in order
def lw_keys(s: Ls.L) -> List<&2, Nat>:
  match s:
    case Ls.L{n, h, q}:
      lw_keys.of(Ls.hkey(h), lw_keys.queue(q))

# k is one of ks
def lw_in(+k: Nat, ks: List<&2, Nat>) -> Bool:
  match ks:
    case Nil{}:
      False{}
    case j <> t:
      Bool.or(Nat.is_eq(j, k), lw_in(k, t))

def lw_ended.put(kept: Bool, k: Nat, r: List<&2, Nat>) -> List<&2, Nat>:
  match kept:
    case True{}:
      r
    case False{}:
      k <> r

# the keys of ks missing from kept, in the order of ks
def lw_ended(+kept: List<&2, Nat>, ks: List<&2, Nat>) -> List<&2, Nat>:
  match ks:
    case Nil{}:
      Nil{}
    case +k <> t:
      lw_ended.put(lw_in(k, kept), k, lw_ended(kept, t))

def lw_spell_grant(m: Maybe<&2, Nat>, rest: String) -> String:
  match m:
    case None{}:
      Wr.put_nat(0n, rest)
    case Some{k}:
      Wr.put_nat(1n, Wr.put_nat(k, rest))

# what the owner acts on when the lease goes from s to s2: the grant, then
# the ended keys (a count, then each)
def lw_answer(+s: Ls.L, +s2: Ls.L) -> String:
  lw_spell_grant(lw_grant(Ls.hkey(Ls.L.holder(s2)), Ls.hkey(Ls.L.holder(s))), Wr.put_list(~Nat, ~Wr.put_nat, lw_ended(lw_keys(s2), lw_keys(s)), ""))

# the reply to e in state s: an ask's leads with the key it got (the next
# key of s)
def lw_reply(+s: Ls.L, e: Ls.Ev) -> String:
  match e:
    case Ls.Ask{o}:
      Wr.put_nat(Ls.L.next(s), lw_answer(s, Ls.step(s, Ls.Ask{o})))
    case Ls.Release{k}:
      lw_answer(s, Ls.step(s, Ls.Release{k}))
    case Ls.Stop{k}:
      lw_answer(s, Ls.step(s, Ls.Stop{k}))
    case Ls.Crash{o}:
      lw_answer(s, Ls.step(s, Ls.Crash{o}))

# the replies to evs from s, by the model
def lw_replies(evs: List<&2, Ls.Ev>, +s: Ls.L) -> List<&2, String>:
  match evs:
    case Nil{}:
      Nil{}
    case +e <> t:
      lw_reply(s, e) <> lw_replies(t, Ls.step(s, e))

# every event of evs can be sent
def lw_all_fit(evs: List<&2, Ls.Ev>) -> Bool:
  match evs:
    case Nil{}:
      True{}
    case e <> t:
      Bool.and(lw_fits(e), lw_all_fit(t))

def lw_cons(x: String, r: List<&2, String> & FLs.St) -> List<&2, String> & FLs.St:
  (xs, st) = r
  (x <> xs, st)

# the reply of r, then the shipped stepper's replies to evs spelled on the
# wire, from the state of r; and the state it ends in
def lw_run(evs: List<&2, Ls.Ev>, r: FLs.St & String) -> List<&2, String> & FLs.St:
  match evs:
    case Nil{}:
      (st, out) = r
      ([out], st)
    case e <> t:
      (st, out) = r
      lw_cons(out, lw_run(t, FLs.step(st, lw_spell_ev(e))))

# the replies of the shipped stepper to raw inputs, from the state of r
def lw_feed(ins: List<&2, String>, r: FLs.St & String) -> List<&2, String>:
  match ins:
    case Nil{}:
      (st, out) = r
      [out]
    case i <> t:
      (st, out) = r
      out <> lw_feed(t, FLs.step(st, i))

# Laws
# ----

# LAW lease_entry_open: the open with no input is a free lease with no
# waiter and the first key next, and replies nothing
# EXCLUDES: a lease that starts held, with waiters, or with keys used
law lease_entry_open:
  {FLs.open("") == (FLs.Live{Ls.L.empty()}, "") : FLs.St & String}

# LAW lease_entry_open_refused: an open with input is refused with the
# error form
# EXCLUDES: a default lease for an open the owner never sends
law lease_entry_open_refused:
  for +s: String
  for h: {String.is_empty(s) == False{} : Bool}
  {FLs.open(s) == (FLs.Shut{}, SCon{'E', SCon{' ', "lease: the open takes no input"}}) : FLs.St & String}

# LAW lease_entry_shut: a refused open answers every step with the error
# form
# EXCLUDES: a refused stepper that grants a lease
law lease_entry_shut:
  for +s: String
  {FLs.step(FLs.Shut{}, s) == (FLs.Shut{}, SCon{'E', SCon{' ', "lease: the open was refused"}}) : FLs.St & String}

# LAW lease_entry_answers: in any state, every event the owner sends
# (spelled from the wire's primitives, its number within the wire) moves
# the lease as the model's step does and answers the spelled reply: an
# ask's key, the grant, the ended keys
# EXCLUDES: a field misread (tag, origin, key), a state other than the
# model's (Ls.step), a grant other than the new holder, an ended key
# missing, invented or out of order, a reply in another spelling
law lease_entry_answers:
  for +s: Ls.L
  for +e: Ls.Ev
  for fits: {lw_fits(e) == True{} : Bool}
  {FLs.step(FLs.Live{s}, lw_spell_ev(e)) == (FLs.Live{Ls.step(s, e)}, lw_reply(s, e)) : FLs.St & String}

# LAW lease_entry_reads: in any state, an input the laws' reader reads as
# exactly one event moves the lease as the model's step does and answers
# its spelled reply
# EXCLUDES: an input read otherwise by the entry than by the wire's
# grammar (a stop or a fourth tag accepted, a number misread)
law lease_entry_reads:
  for +s: Ls.L
  for +i: String
  for +e: Ls.Ev
  for got: {lw_read(i) == Some{e} : Maybe<&2, Ls.Ev>}
  {FLs.step(FLs.Live{s}, i) == (FLs.Live{Ls.step(s, e)}, lw_reply(s, e)) : FLs.St & String}

# LAW lease_entry_malformed_exact: in any state, an input the laws' reader
# does not read as exactly one event (a stop, an unknown tag, a bad
# number, input left over) keeps the lease and answers exactly the error
# form 'E ' + "lease: malformed event"
# EXCLUDES: a guessed event, a lease changed by a malformed event, another
# error text
law lease_entry_malformed_exact:
  for +s: Ls.L
  for +i: String
  for no: {lw_read(i) == None{} : Maybe<&2, Ls.Ev>}
  {FLs.step(FLs.Live{s}, i) == (FLs.Live{s}, SCon{'E', SCon{' ', "lease: malformed event"}}) : FLs.St & String}

# LAW lease_entry_history: the shipped stepper, opened with no input and
# fed any events the owner sends, replies to each what the model decides
# after the events before it, and ends in the model's lease after them:
# every lease law above holds for the lease the owner runs
# EXCLUDES: a stepper that forgets, reorders or replays an event, or whose
# state drifts from the model's
law lease_entry_history:
  for +evs: List<&2, Ls.Ev>
  for fits: {lw_all_fit(evs) == True{} : Bool}
  {lw_run(evs, FLs.open("")) == ("" <> lw_replies(evs, Ls.L.empty()), FLs.Live{Ls.run(evs)}) : List<&2, String> & FLs.St}

# LAW lease_entry_example: anchor: the bytes the owner sends and the
# replies: an ask of the owner's process (granted at once), two asks of
# connection 1 (origin 2), the holder's release (the next waiter granted,
# the holder ended), the crash of connection 1 (both its leases end, the
# lease free), a release of a key no one holds, an unknown tag, input
# left over
# EXCLUDES: an entry that answers other bytes than the grammar's
law lease_entry_example:
  {lw_feed(["0,0,", "0,2,", "0,2,", "1,0,", "2,2,", "1,7,", "3,0,", "0,0,x"], FLs.open("")) == ["", "0,1,0,0,", "1,0,0,", "2,0,0,", "1,1,1,0,", "0,2,1,2,", "0,0,", SCon{'E', SCon{' ', "lease: malformed event"}}, SCon{'E', SCon{' ', "lease: malformed event"}}] : List<&2, String>}

# LAW lease_req_fits_example: witness: events of each kind the owner sends
# fit the wire (lease_entry_answers and lease_entry_history are not
# vacuous)
law lease_req_fits_example:
  {[lw_fits(Ls.Ask{0n}), lw_fits(Ls.Release{3n}), lw_fits(Ls.Crash{2n}), lw_all_fit([Ls.Ask{1n}, Ls.Crash{1n}])] == [True{}, True{}, True{}, True{}] : List<&2, Bool>}

# LAW lease_undelivered_is_stopped: after any events, when an event hands
# the lease to a waiter that was already waiting and the owner releases it
# at once (the grant could not be delivered: the waiter had stopped
# waiting), the lease ends exactly as if that waiter had stopped before
# the event: the owner's release of an undelivered grant is the model's
# stop
# EXCLUDES: a lease that the owner's release-on-failure hands on otherwise
# than the model's stop would (another waiter skipped or granted, the
# queue reordered, a key reused)
law lease_undelivered_is_stopped:
  for +evs: List<&2, Ls.Ev>
  for +e: Ls.Ev
  for +k: Nat
  for +o: Nat
  for waits: Ls.In(Ls.Waiter{k, o, True{}}, Ls.L.queue(Ls.run(evs)))
  for got: {Ls.L.holder(Ls.step(Ls.run(evs), e)) == Some{Ls.Lease{k, o}} : Maybe<&2, Ls.Lease>}
  {Ls.step(Ls.step(Ls.run(evs), e), Ls.Release{k}) == Ls.step(Ls.step(Ls.run(evs), Ls.Stop{k}), e) : Ls.L}

# What an event does to the leases it names
# -----------------------------------------
# The laws above leave the model's step free where the Rust bridge used to
# pin it (the bridge went with the Rust copy): these pin what an event
# does to the leases it names.

# no waiter of q has key k
def lw_NoKey(+k: Nat, q: List<&2, Ls.Waiter>) -> Type:
  match q:
    case Nil{}:
      Unit
    case w <> t:
      ({Nat.is_eq(Ls.Waiter.key(w), k) == False{} : Bool} & lw_NoKey(k, t))

# the lease k is over: k neither holds nor waits
def lw_Over(+k: Nat, s: Ls.L) -> Type:
  match s:
    case Ls.L{n, h, q}:
      (Ls.NotHeld(k, h) & lw_NoKey(k, q))

# LAW lease_keeps_holder: in any state, an event that does not end the
# holder (its release, its stop, its origin's crash) leaves it holding
# EXCLUDES: an ask, a stop, another key's release or another origin's
# crash that frees or hands on the lease while its holder still runs its
# turn (two turns at once)
law lease_keeps_holder:
  for +s: Ls.L
  for +e: Ls.Ev
  for +k: Nat
  for +o: Nat
  for holds: {Ls.L.holder(s) == Some{Ls.Lease{k, o}} : Maybe<&2, Ls.Lease>}
  for other: {Ls.hits(e, Ls.Waiter{k, o, True{}}) == False{} : Bool}
  {Ls.L.holder(Ls.step(s, e)) == Some{Ls.Lease{k, o}} : Maybe<&2, Ls.Lease>}

# LAW lease_ask_waits: in any state, an ask holds or waits after it, live,
# under the key the entry reports (the state's next key)
# EXCLUDES: an ask that is lost, queued dead, or queued under another key
# than the one the owner is told (its release would miss it)
law lease_ask_waits:
  for +s: Ls.L
  for +o: Nat
  Ls.Kept(Ls.L.next(s), o, Ls.step(s, Ls.Ask{o}))

# LAW lease_release_ends: after any events, a release of key j ends the
# lease j: j neither holds nor waits after it
# EXCLUDES: a released holder that keeps the lease, a released waiter
# that stays queued and is granted later
law lease_release_ends:
  for +evs: List<&2, Ls.Ev>
  for +j: Nat
  lw_Over(j, Ls.step(Ls.run(evs), Ls.Release{j}))

# whether e ends the lease k of origin o, read from the words of the laws:
# a release or a stop of its key, a crash of its origin; an ask ends none
def lw_hits(e: Ls.Ev, +k: Nat, +o: Nat) -> Bool:
  match e:
    case Ls.Ask{p}:
      False{}
    case Ls.Release{j}:
      Nat.is_eq(k, j)
    case Ls.Stop{j}:
      Nat.is_eq(k, j)
    case Ls.Crash{p}:
      Nat.is_eq(o, p)

# LAW lease_hits_exact: the model's `hits`, which lease_keeps_waiters and
# lease_keeps_holder read as "the event ends this lease", means exactly
# that: a release or a stop of its key, a crash of its origin, never an ask
# EXCLUDES: a `hits` that counts an ask (or any event) as ending every
# lease, which would leave those laws nothing to say about it
law lease_hits_exact:
  for +e: Ls.Ev
  for +k: Nat
  for +o: Nat
  for +l: Bool
  {Ls.hits(e, Ls.Waiter{k, o, l}) == lw_hits(e, k, o) : Bool}

# The model's code, pinned
# ------------------------
# The lease runs as the model (bend/lease.bend) itself, and the laws above
# read its terms (Fifo, Busy, Kept, Freed, NotHeld) and its accessors: so
# the model's step and accessors are pinned here against a spec written in
# the laws, whatever those terms say.

def lw_next(s: Ls.L) -> Nat:
  match s:
    case Ls.L{n, h, q}:
      n

def lw_holder(s: Ls.L) -> Maybe<&2, Ls.Lease>:
  match s:
    case Ls.L{n, h, q}:
      h

def lw_queue(s: Ls.L) -> List<&2, Ls.Waiter>:
  match s:
    case Ls.L{n, h, q}:
      q

def lw_hkey(h: Maybe<&2, Ls.Lease>) -> Maybe<&2, Nat>:
  match h:
    case None{}:
      None{}
    case Some{x}:
      match x:
        case Ls.Lease{k, o}:
          Some{k}

def lw_wkey(w: Ls.Waiter) -> Nat:
  match w:
    case Ls.Waiter{k, o, l}:
      k

def lw_wlive(w: Ls.Waiter) -> Bool:
  match w:
    case Ls.Waiter{k, o, l}:
      l

def lw_keep(gone: Bool, w: Ls.Waiter, r: List<&2, Ls.Waiter>) -> List<&2, Ls.Waiter>:
  match gone:
    case True{}:
      r
    case False{}:
      w <> r

# the waiters of q that e does not end, in order
def lw_left(+e: Ls.Ev, q: List<&2, Ls.Waiter>) -> List<&2, Ls.Waiter>:
  match q:
    case Nil{}:
      Nil{}
    case w <> t:
      match w:
        case Ls.Waiter{+k, +o, l}:
          lw_keep(lw_hits(e, k, o), Ls.Waiter{k, o, l}, lw_left(e, t))

def lw_dead.one(hit: Bool, k: Nat, o: Nat, l: Bool) -> Ls.Waiter:
  match hit:
    case True{}:
      Ls.Waiter{k, o, False{}}
    case False{}:
      Ls.Waiter{k, o, l}

# q with every waiter of key j dead (it stopped waiting)
def lw_dead(+j: Nat, q: List<&2, Ls.Waiter>) -> List<&2, Ls.Waiter>:
  match q:
    case Nil{}:
      Nil{}
    case w <> t:
      match w:
        case Ls.Waiter{+k, o, l}:
          lw_dead.one(Nat.is_eq(k, j), k, o, l) <> lw_dead(j, t)

# the lease of the first live waiter of q
def lw_first(q: List<&2, Ls.Waiter>) -> Maybe<&2, Ls.Lease>:
  match q:
    case Nil{}:
      None{}
    case w <> t:
      match w:
        case Ls.Waiter{k, o, l}:
          match l:
            case True{}:
              Some{Ls.Lease{k, o}}
            case False{}:
              lw_first(t)

# the waiters after the first live one (the dead before it are passed over)
def lw_rest(q: List<&2, Ls.Waiter>) -> List<&2, Ls.Waiter>:
  match q:
    case Nil{}:
      Nil{}
    case w <> t:
      match w:
        case Ls.Waiter{k, o, l}:
          match l:
            case True{}:
              t
            case False{}:
              lw_rest(t)

# a free lease goes to the first live waiter
def lw_settle(n: Nat, h: Maybe<&2, Ls.Lease>, +q: List<&2, Ls.Waiter>) -> Ls.L:
  match h:
    case None{}:
      Ls.L{n, lw_first(q), lw_rest(q)}
    case Some{x}:
      Ls.L{n, Some{x}, q}

def lw_release(holds: Bool, +j: Nat, +n: Nat, h: Maybe<&2, Ls.Lease>, +q: List<&2, Ls.Waiter>) -> Ls.L:
  match holds:
    case True{}:
      lw_settle(n, None{}, q)
    case False{}:
      lw_settle(n, h, lw_left(Ls.Release{j}, q))

def lw_unless.put(hit: Bool, x: Ls.Lease) -> Maybe<&2, Ls.Lease>:
  match hit:
    case True{}:
      None{}
    case False{}:
      Some{x}

# the holder, unless it is of origin p
def lw_unless(h: Maybe<&2, Ls.Lease>, +p: Nat) -> Maybe<&2, Ls.Lease>:
  match h:
    case None{}:
      None{}
    case Some{x}:
      match x:
        case Ls.Lease{k, +o}:
          lw_unless.put(Nat.is_eq(o, p), Ls.Lease{k, o})

# the lease after e: an ask queues a live waiter under the next key; a
# release of the holder's key frees the lease, any other drops the waiters
# of that key; a stop marks the waiters of its key dead; a crash ends the
# holder of its origin and drops its waiters; a free lease then goes to the
# first live waiter
def lw_step(s: Ls.L, e: Ls.Ev) -> Ls.L:
  match s:
    case Ls.L{+n, +h, +q}:
      match e:
        case Ls.Ask{o}:
          lw_settle(1n+n, h, List.append(&2, Ls.Waiter, q, [Ls.Waiter{n, o, True{}}]))
        case Ls.Release{+j}:
          lw_release(lw_is(lw_hkey(h), j), j, n, h, q)
        case Ls.Stop{j}:
          Ls.L{n, h, lw_dead(j, q)}
        case Ls.Crash{+p}:
          lw_settle(n, lw_unless(h, p), lw_left(Ls.Crash{p}, q))

# the lease after evs, from s
def lw_go(evs: List<&2, Ls.Ev>, s: Ls.L) -> Ls.L:
  match evs:
    case Nil{}:
      s
    case e <> t:
      lw_go(t, lw_step(s, e))

# LAW lease_step_exact: the model's step is exactly the lease the laws
# describe: an ask queues a live waiter under the next key, a release of
# the holder frees it and of a waiter drops it, a stop marks its waiter
# dead, a crash ends its origin's holder and waiters, and a free lease
# goes to the first live waiter at once
# EXCLUDES: any step other than this one, even one the property laws
# above miss through a model term (Fifo, Busy, Kept, Freed, NotHeld) that
# says less than its name
law lease_step_exact:
  for +s: Ls.L
  for +e: Ls.Ev
  {Ls.step(s, e) == lw_step(s, e) : Ls.L}

# LAW lease_run_exact: the model's run of events from any lease is the
# laws' fold of lease_step_exact's step, and it starts from a free lease
# with no waiter and the key 0 next
# EXCLUDES: a run that skips, repeats or reorders events, a start state
# other than the empty lease
law lease_run_exact:
  for +evs: List<&2, Ls.Ev>
  for +s: Ls.L
  {Ls.go(evs, s) == lw_go(evs, s) : Ls.L} & {Ls.L.empty() == Ls.L{0n, None{}, Nil{}} : Ls.L}

# LAW lease_terms_exact: the model's accessors the laws read are the
# fields they name
# EXCLUDES: an accessor that reports another key (the one an ask's reply
# names), holder, queue or liveness than the lease holds
law lease_terms_exact:
  for +s: Ls.L
  for +h: Maybe<&2, Ls.Lease>
  for +w: Ls.Waiter
  {Ls.L.next(s) == lw_next(s) : Nat} & {Ls.L.holder(s) == lw_holder(s) : Maybe<&2, Ls.Lease>} & {Ls.L.queue(s) == lw_queue(s) : List<&2, Ls.Waiter>} & {Ls.hkey(h) == lw_hkey(h) : Maybe<&2, Nat>} & {Ls.Waiter.key(w) == lw_wkey(w) : Nat} & {Ls.Waiter.live(w) == lw_wlive(w) : Bool}

# The model's terms, pinned
# -------------------------
# lease_fifo, lease_never_idle, lease_keeps_waiters, lease_stop_never_holds
# and lease_crash_frees state their claims and premises with the model's
# own terms (`Ls.In`, `Ls.Kept`, `Ls.Fifo`, `Ls.Busy`, `Ls.NotHeld`,
# `Ls.Freed`). A fresh adversary noted that a model with `In = Empty` and
# `Kept = Unit` passes them vacuously. Each term is pinned here, both
# ways, to a Bool written in the laws: the term holds exactly when the
# Bool is true.

def lt_beq(a: Bool, b: Bool) -> Bool:
  match a:
    case True{}:
      b
    case False{}:
      Bool.not(b)

# two waiters are the same: key, origin and liveness
def lt_weq(a: Ls.Waiter, b: Ls.Waiter) -> Bool:
  match a:
    case Ls.Waiter{k, o, l}:
      match b:
        case Ls.Waiter{j, p, m}:
          Bool.and(Nat.is_eq(k, j), Bool.and(Nat.is_eq(o, p), lt_beq(l, m)))

# x is one of the waiters of q
def lt_in(+x: Ls.Waiter, q: List<&2, Ls.Waiter>) -> Bool:
  match q:
    case Nil{}:
      False{}
    case w <> t:
      Bool.or(lt_weq(x, w), lt_in(x, t))

# the lease h is held by key k of origin o
def lt_holds(h: Maybe<&2, Ls.Lease>, +k: Nat, +o: Nat) -> Bool:
  match h:
    case None{}:
      False{}
    case Some{x}:
      match x:
        case Ls.Lease{hk, ho}:
          Bool.and(Nat.is_eq(hk, k), Nat.is_eq(ho, o))

# k of origin o holds the lease of s or waits for it, live
def lt_kept(+k: Nat, +o: Nat, s: Ls.L) -> Bool:
  match s:
    case Ls.L{n, h, q}:
      Bool.or(lt_holds(h, k, o), lt_in(Ls.Waiter{k, o, True{}}, q))

# the keys of q rise, each above lo (None: no bound)
def lt_asc(q: List<&2, Ls.Waiter>, lo: Maybe<&2, Nat>) -> Bool:
  match q:
    case Nil{}:
      True{}
    case w <> t:
      match w:
        case Ls.Waiter{+k, o, l}:
          match lo:
            case None{}:
              lt_asc(t, Some{k})
            case Some{b}:
              Bool.and(Nat.is_lt(b, k), lt_asc(t, Some{k}))

# the holder came before every waiter, and the waiters in the order they came
def lt_fifo(s: Ls.L) -> Bool:
  match s:
    case Ls.L{n, h, q}:
      match h:
        case None{}:
          lt_asc(q, None{})
        case Some{x}:
          match x:
            case Ls.Lease{hk, ho}:
              lt_asc(q, Some{hk})

# every waiter of q is dead
def lt_dead(q: List<&2, Ls.Waiter>) -> Bool:
  match q:
    case Nil{}:
      True{}
    case w <> t:
      match w:
        case Ls.Waiter{k, o, l}:
          Bool.and(Bool.not(l), lt_dead(t))

# the lease is held, or no live waiter waits for it
def lt_busy(s: Ls.L) -> Bool:
  match s:
    case Ls.L{n, h, q}:
      match h:
        case None{}:
          lt_dead(q)
        case Some{x}:
          True{}

# k does not hold h
def lt_notheld(+k: Nat, h: Maybe<&2, Ls.Lease>) -> Bool:
  match h:
    case None{}:
      True{}
    case Some{x}:
      match x:
        case Ls.Lease{hk, ho}:
          Bool.not(Nat.is_eq(hk, k))

# no waiter of q is of origin o
def lt_nonefrom(+o: Nat, q: List<&2, Ls.Waiter>) -> Bool:
  match q:
    case Nil{}:
      True{}
    case w <> t:
      match w:
        case Ls.Waiter{k, wo, l}:
          Bool.and(Bool.not(Nat.is_eq(wo, o)), lt_nonefrom(o, t))

# no lease of origin o is held or waited for
def lt_freed(+o: Nat, s: Ls.L) -> Bool:
  match s:
    case Ls.L{n, h, q}:
      match h:
        case None{}:
          lt_nonefrom(o, q)
        case Some{x}:
          match x:
            case Ls.Lease{hk, ho}:
              Bool.and(Bool.not(Nat.is_eq(ho, o)), lt_nonefrom(o, q))

# LAW lease_in_exact: `Ls.In(x, q)` holds exactly when x is one of the waiters of q (same key,
# origin and liveness)
# EXCLUDES: an `In` that never holds (lease_keeps_waiters and lease_stop_never_holds vacuous) or
#   always holds
law lease_in_exact:
  for +x: Ls.Waiter
  for +q: List<&2, Ls.Waiter>
  (Ls.In(x, q) -> {lt_in(x, q) == True{} : Bool}) & ({lt_in(x, q) == True{} : Bool} -> Ls.In(x, q))

# LAW lease_kept_exact: `Ls.Kept(k, o, s)` holds exactly when key k of origin o holds the lease of
# s or waits for it, live
# EXCLUDES: a `Kept` that always holds (lease_keeps_waiters vacuous) or never does
law lease_kept_exact:
  for +k: Nat
  for +o: Nat
  for +s: Ls.L
  (Ls.Kept(k, o, s) -> {lt_kept(k, o, s) == True{} : Bool}) & ({lt_kept(k, o, s) == True{} : Bool} -> Ls.Kept(k, o, s))

# LAW lease_fifo_term_exact: `Ls.Fifo(s)` holds exactly when the holder's key is below every
# waiter's and the waiters' keys rise
# EXCLUDES: a `Fifo` that always holds (lease_fifo vacuous)
law lease_fifo_term_exact:
  for +s: Ls.L
  (Ls.Fifo(s) -> {lt_fifo(s) == True{} : Bool}) & ({lt_fifo(s) == True{} : Bool} -> Ls.Fifo(s))

# LAW lease_busy_term_exact: `Ls.Busy(s)` holds exactly when the lease is held or every waiter is
# dead
# EXCLUDES: a `Busy` that always holds (lease_never_idle vacuous)
law lease_busy_term_exact:
  for +s: Ls.L
  (Ls.Busy(s) -> {lt_busy(s) == True{} : Bool}) & ({lt_busy(s) == True{} : Bool} -> Ls.Busy(s))

# LAW lease_notheld_term_exact: `Ls.NotHeld(k, h)` holds exactly when key k does not hold h
# EXCLUDES: a `NotHeld` that always holds (lease_stop_never_holds vacuous)
law lease_notheld_term_exact:
  for +k: Nat
  for +h: Maybe<&2, Ls.Lease>
  (Ls.NotHeld(k, h) -> {lt_notheld(k, h) == True{} : Bool}) & ({lt_notheld(k, h) == True{} : Bool} -> Ls.NotHeld(k, h))

# LAW lease_freed_term_exact: `Ls.Freed(o, s)` holds exactly when no lease of origin o is held or
# waited for in s
# EXCLUDES: a `Freed` that always holds (lease_crash_frees vacuous)
law lease_freed_term_exact:
  for +o: Nat
  for +s: Ls.L
  (Ls.Freed(o, s) -> {lt_freed(o, s) == True{} : Bool}) & ({lt_freed(o, s) == True{} : Bool} -> Ls.Freed(o, s))

# LAW lease_run_is_go: the model's run of events is its walk from the empty lease, so
# lease_run_exact pins it (a third fresh adversary's run that restarted at a stop passed every
# law)
# EXCLUDES: a run that drifts from the steps (resets, skips or reorders events), which would
#   make the history laws speak of another lease than the one the owner runs
law lease_run_is_go:
  for +evs: List<&2, Ls.Ev>
  {Ls.run(evs) == Ls.go(evs, Ls.L.empty()) : Ls.L}
