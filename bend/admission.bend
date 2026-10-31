# admission: the pure model of one provider's admission controller
# (crates/eukhe-core/src/admission.rs, `ControllerState`), rule H3 of
# LAWS.bend.
#
# - The state is the limit, the queue limit, and one entry per ticket, in
#   ticket order: its class and its status. Ticket k is entry k.
# - A status is `Queued` (waits), `Granted` (holds a slot, its waiter has
#   not collected it), `Held` (a collected permit), `Preempted` (a
#   collected background permit an interactive request took the slot
#   from), or `Ended` (released, left, or rejected).
# - The Rust queues are the queued entries of a class, in ticket order;
#   its counters are the counts below.
#
# LAWS.bend states what must hold; PROOF.bend proves it (with
# proof/admission/). bridge/bridge_admission.bend runs this model
# on the scenarios of the Rust bridge test (admission/bridge.rs).

import Base

# The state
# ---------

# a request's class: interactive (a session's) or background (the
# compactor's)
type Cls is Data:
  Ia{}
  Bg{}

type Sts is Data:
  Queued{}
  Granted{}
  Held{}
  Preempted{}
  Ended{}

# one ticket: its class and its status
type Tk is Data:
  Tk{c: Cls, s: Sts}

# providerMaxInFlight: unlimited, or 1 + p slots
type Lim is Data:
  Unl{}
  Cap{p: Nat}

# the limit, providerMaxQueued, and the tickets, oldest first
type St is Data:
  St{lim: Lim, q: Nat, ts: List<&2, Tk>}

# what the holders of tickets do: admit a request of a class, collect a
# granted permit (a queued waiter polls), release a collected permit,
# leave (drop a waiter, granted or not), set the limits
type Op is Data:
  Admit{c: Cls}
  Collect{k: Nat}
  Release{k: Nat}
  Leave{k: Nat}
  Limit{lim: Lim, q: Nat}

def St.lim(s: St) -> Lim:
  match s:
    case St{l, q, ts}:
      l

def St.ts(s: St) -> List<&2, Tk>:
  match s:
    case St{l, q, ts}:
      ts

# Counting
# --------

# what a count counts: slots held (granted or collected, not preempted),
# or waiters
type Mode is Data:
  Holding{}
  Waiting{}

def Cls.eq(a: Cls, b: Cls) -> Bool:
  match a b:
    case Ia{} Ia{}:
      True{}
    case Ia{} Bg{}:
      False{}
    case Bg{} Ia{}:
      False{}
    case Bg{} Bg{}:
      True{}

def Mode.of(m: Mode, s: Sts) -> Bool:
  match m s:
    case Holding{} Queued{}:
      False{}
    case Holding{} Granted{}:
      True{}
    case Holding{} Held{}:
      True{}
    case Holding{} Preempted{}:
      False{}
    case Holding{} Ended{}:
      False{}
    case Waiting{} Queued{}:
      True{}
    case Waiting{} Granted{}:
      False{}
    case Waiting{} Held{}:
      False{}
    case Waiting{} Preempted{}:
      False{}
    case Waiting{} Ended{}:
      False{}

# ticket t counts in mode m of class c
def hit(+m: Mode, +c: Cls, t: Tk) -> Bool:
  match t:
    case Tk{tc, s}:
      Bool.and(Mode.of(m, s), Cls.eq(c, tc))

def bit(b: Bool, x: Nat) -> Nat:
  match b:
    case False{}:
      x
    case True{}:
      1n+x

def cnt(+m: Mode, +c: Cls, ts: List<&2, Tk>) -> Nat:
  match ts:
    case Nil{}:
      0n
    case h <> r:
      bit(hit(m, c, h), cnt(m, c, r))

def isz(n: Nat) -> Bool:
  match n:
    case 0n:
      True{}
    case 1n+p:
      False{}

def le(a: Nat, b: Nat) -> Bool:
  match a b:
    case 0n _:
      True{}
    case 1n+x 0n:
      False{}
    case 1n+x 1n+y:
      le(x, y)

# a slot is free with n held
def room(l: Lim, n: Nat) -> Bool:
  match l:
    case Unl{}:
      True{}
    case Cap{p}:
      le(n, p)

# n slots held are within the limit
def within(l: Lim, n: Nat) -> Bool:
  match l:
    case Unl{}:
      True{}
    case Cap{p}:
      le(n, 1n+p)

# slots held, both classes
def held(+ts: List<&2, Tk>) -> Nat:
  Nat.add(cnt(Holding{}, Ia{}, ts), cnt(Holding{}, Bg{}, ts))

# waiters, both classes
def waits(+ts: List<&2, Tk>) -> Nat:
  Nat.add(cnt(Waiting{}, Ia{}, ts), cnt(Waiting{}, Bg{}, ts))

# Granting
# --------

# who may take a free slot (r): an interactive waiter, else a background
# one while no interactive request holds a slot (wi, hi, wb: interactive
# waiters, interactive slots, background waiters)
def pick.go(r: Bool, wi: Nat, hi: Nat, wb: Nat) -> Maybe<&2, Cls>:
  match r wi hi wb:
    case False{} _ _ _:
      None{}
    case True{} 1n+a _ _:
      Some{Ia{}}
    case True{} 0n 1n+b _:
      None{}
    case True{} 0n 0n 0n:
      None{}
    case True{} 0n 0n 1n+d:
      Some{Bg{}}

def pick(+l: Lim, +ts: List<&2, Tk>) -> Maybe<&2, Cls>:
  pick.go(room(l, held(ts)), cnt(Waiting{}, Ia{}, ts), cnt(Holding{}, Ia{}, ts), cnt(Waiting{}, Bg{}, ts))

def mark.at(b: Bool, c: Cls, h: Tk, r: List<&2, Tk>, m: List<&2, Tk>) -> List<&2, Tk>:
  match b:
    case True{}:
      Tk{c, Granted{}} <> r
    case False{}:
      h <> m

# grant the oldest waiter of class c
def mark(+c: Cls, ts: List<&2, Tk>) -> List<&2, Tk>:
  match ts:
    case Nil{}:
      Nil{}
    case +h <> +r:
      mark.at(hit(Waiting{}, c, h), c, h, r, mark(c, r))

# grant waiters until no slot is free or no waiter may take one (Rust
# `grant_waiters`); d is the next grant. Each grant takes one waiter, so
# the waiters bound the grants.
def grant.go(n: Nat, d: Maybe<&2, Cls>, +l: Lim, +ts: List<&2, Tk>) -> List<&2, Tk>:
  match n d:
    case 0n _:
      ts
    case 1n+f None{}:
      ts
    case 1n+f Some{c}:
      +t2 = mark(c, ts)
      grant.go(f, pick(l, t2), l, t2)

def grant(+l: Lim, +ts: List<&2, Tk>) -> List<&2, Tk>:
  grant.go(waits(ts), pick(l, ts), l, ts)

# Admitting
# ---------

# an interactive request frees every background slot: a granted waiter
# waits again, a collected permit is preempted (Rust
# `preempt_background`)
def Tk.preempt(t: Tk) -> Tk:
  match t:
    case Tk{Ia{}, s}:
      Tk{Ia{}, s}
    case Tk{Bg{}, Queued{}}:
      Tk{Bg{}, Queued{}}
    case Tk{Bg{}, Granted{}}:
      Tk{Bg{}, Queued{}}
    case Tk{Bg{}, Held{}}:
      Tk{Bg{}, Preempted{}}
    case Tk{Bg{}, Preempted{}}:
      Tk{Bg{}, Preempted{}}
    case Tk{Bg{}, Ended{}}:
      Tk{Bg{}, Ended{}}

def preempt(ts: List<&2, Tk>) -> List<&2, Tk>:
  match ts:
    case Nil{}:
      Nil{}
    case h <> r:
      Tk.preempt(h) <> preempt(r)

# a new interactive ticket: a slot if one is free and no interactive
# request waits, else rejected once q of them wait, else it waits
def admit.ia.st(free: Bool, full: Bool) -> Sts:
  match free full:
    case True{} _:
      Held{}
    case False{} True{}:
      Ended{}
    case False{} False{}:
      Queued{}

# after the preemption only interactive slots are held, so the counts of
# ts decide
def admit.ia(+l: Lim, +q: Nat, +ts: List<&2, Tk>) -> List<&2, Tk>:
  List.append(&2, Tk, preempt(ts), [Tk{Ia{}, admit.ia.st(Bool.and(isz(cnt(Waiting{}, Ia{}, ts)), room(l, cnt(Holding{}, Ia{}, ts))), le(q, cnt(Waiting{}, Ia{}, ts)))}])

def admit.bg.st(free: Bool) -> Sts:
  match free:
    case True{}:
      Held{}
    case False{}:
      Queued{}

# a new background ticket: a slot if one is free and no request holds
# one interactively or waits, else it waits (never rejected)
def admit.bg(+l: Lim, +ts: List<&2, Tk>) -> List<&2, Tk>:
  List.append(&2, Tk, ts, [Tk{Bg{}, admit.bg.st(Bool.and(isz(cnt(Holding{}, Ia{}, ts)), Bool.and(isz(cnt(Waiting{}, Ia{}, ts)), Bool.and(isz(cnt(Waiting{}, Bg{}, ts)), room(l, held(ts))))))}])

# Tickets
# -------

def put(ts: List<&2, Tk>, k: Nat, x: Sts) -> List<&2, Tk>:
  match ts:
    case Nil{}:
      Nil{}
    case Tk{c, s} <> r:
      match k:
        case 0n:
          Tk{c, x} <> r
        case 1n+p:
          Tk{c, s} <> put(r, p, x)

def get(+ts: List<&2, Tk>, k: Nat) -> Maybe<&2, Tk>:
  List.get(&2, Tk, ts, k)

# a waiter polls: a granted permit is collected
def collect.at(m: Maybe<&2, Tk>, +l: Lim, +q: Nat, +ts: List<&2, Tk>, k: Nat) -> St:
  match m:
    case None{}:
      St{l, q, ts}
    case Some{Tk{c, Queued{}}}:
      St{l, q, ts}
    case Some{Tk{c, Granted{}}}:
      St{l, q, put(ts, k, Held{})}
    case Some{Tk{c, Held{}}}:
      St{l, q, ts}
    case Some{Tk{c, Preempted{}}}:
      St{l, q, ts}
    case Some{Tk{c, Ended{}}}:
      St{l, q, ts}

# a collected permit drops: its slot goes to the waiters; a preempted
# one's slot was freed by the preemption
def release.at(m: Maybe<&2, Tk>, +l: Lim, +q: Nat, +ts: List<&2, Tk>, k: Nat) -> St:
  match m:
    case None{}:
      St{l, q, ts}
    case Some{Tk{c, Queued{}}}:
      St{l, q, ts}
    case Some{Tk{c, Granted{}}}:
      St{l, q, ts}
    case Some{Tk{c, Held{}}}:
      St{l, q, grant(l, put(ts, k, Ended{}))}
    case Some{Tk{c, Preempted{}}}:
      St{l, q, put(ts, k, Ended{})}
    case Some{Tk{c, Ended{}}}:
      St{l, q, ts}

# a waiter drops: it leaves the queue, or its uncollected grant goes to
# the next waiter
def leave.at(m: Maybe<&2, Tk>, +l: Lim, +q: Nat, +ts: List<&2, Tk>, k: Nat) -> St:
  match m:
    case None{}:
      St{l, q, ts}
    case Some{Tk{c, Queued{}}}:
      St{l, q, grant(l, put(ts, k, Ended{}))}
    case Some{Tk{c, Granted{}}}:
      St{l, q, grant(l, put(ts, k, Ended{}))}
    case Some{Tk{c, Held{}}}:
      St{l, q, ts}
    case Some{Tk{c, Preempted{}}}:
      St{l, q, ts}
    case Some{Tk{c, Ended{}}}:
      St{l, q, ts}

# The controller
# --------------

def step(s: St, o: Op) -> St:
  match s:
    case St{+l, +q, +ts}:
      match o:
        case Admit{Ia{}}:
          St{l, q, admit.ia(l, q, ts)}
        case Admit{Bg{}}:
          St{l, q, admit.bg(l, ts)}
        case Collect{+k}:
          collect.at(get(ts, k), l, q, ts, k)
        case Release{+k}:
          release.at(get(ts, k), l, q, ts, k)
        case Leave{+k}:
          leave.at(get(ts, k), l, q, ts, k)
        case Limit{+l2, q2}:
          St{l2, q2, grant(l2, ts)}

def run(os: List<&2, Op>, s: St) -> St:
  match os:
    case Nil{}:
      s
    case o <> r:
      run(r, step(s, o))

def St.new(l: Lim, q: Nat) -> St:
  St{l, q, Nil{}}

# The live controller
# -------------------
# What eukhe runs (the Rust `ControllerState` keeps this state and asks
# `Live.step` for each op). The model above keeps every ticket ever
# admitted, so its ticket k is its k-th entry; this one keeps only the
# live tickets (an ended ticket leaves), each with its ticket number, and
# the number the next ticket gets. LAWS.bend (`admission_live_step`)
# states that it is the model above with the ended tickets left out.

# a live ticket: its number, class and status
type Lv is Data:
  Lv{k: Nat, c: Cls, s: Sts}

# the limit, providerMaxQueued, the live tickets (oldest first) and the
# next ticket's number
type Live is Data:
  Live{lim: Lim, q: Nat, ts: List<&2, Lv>, next: Nat}

def lv.hit(+m: Mode, +c: Cls, t: Lv) -> Bool:
  match t:
    case Lv{k, tc, s}:
      hit(m, c, Tk{tc, s})

def lv.cnt(+m: Mode, +c: Cls, ts: List<&2, Lv>) -> Nat:
  match ts:
    case Nil{}:
      0n
    case h <> r:
      bit(lv.hit(m, c, h), lv.cnt(m, c, r))

def lv.held(+ts: List<&2, Lv>) -> Nat:
  Nat.add(lv.cnt(Holding{}, Ia{}, ts), lv.cnt(Holding{}, Bg{}, ts))

def lv.waits(+ts: List<&2, Lv>) -> Nat:
  Nat.add(lv.cnt(Waiting{}, Ia{}, ts), lv.cnt(Waiting{}, Bg{}, ts))

def lv.pick(+l: Lim, +ts: List<&2, Lv>) -> Maybe<&2, Cls>:
  pick.go(room(l, lv.held(ts)), lv.cnt(Waiting{}, Ia{}, ts), lv.cnt(Holding{}, Ia{}, ts), lv.cnt(Waiting{}, Bg{}, ts))

def lv.mark.at(b: Bool, c: Cls, h: Lv, r: List<&2, Lv>, m: List<&2, Lv>) -> List<&2, Lv>:
  match b:
    case True{}:
      match h:
        case Lv{k, hc, s}:
          Lv{k, c, Granted{}} <> r
    case False{}:
      h <> m

# grant the oldest waiter of class c
def lv.mark(+c: Cls, ts: List<&2, Lv>) -> List<&2, Lv>:
  match ts:
    case Nil{}:
      Nil{}
    case +h <> +r:
      lv.mark.at(lv.hit(Waiting{}, c, h), c, h, r, lv.mark(c, r))

def lv.grant.go(n: Nat, d: Maybe<&2, Cls>, +l: Lim, +ts: List<&2, Lv>) -> List<&2, Lv>:
  match n d:
    case 0n _:
      ts
    case 1n+f None{}:
      ts
    case 1n+f Some{c}:
      +t2 = lv.mark(c, ts)
      lv.grant.go(f, lv.pick(l, t2), l, t2)

def lv.grant(+l: Lim, +ts: List<&2, Lv>) -> List<&2, Lv>:
  lv.grant.go(lv.waits(ts), lv.pick(l, ts), l, ts)

def lv.of(k: Nat, t: Tk) -> Lv:
  match t:
    case Tk{c, s}:
      Lv{k, c, s}

def lv.preempt.one(t: Lv) -> Lv:
  match t:
    case Lv{k, c, s}:
      lv.of(k, Tk.preempt(Tk{c, s}))

def lv.preempt(ts: List<&2, Lv>) -> List<&2, Lv>:
  match ts:
    case Nil{}:
      Nil{}
    case h <> r:
      lv.preempt.one(h) <> lv.preempt(r)

# the new ticket k of class c with status s: it stays only when live
def lv.fresh(s: Sts, k: Nat, c: Cls) -> List<&2, Lv>:
  match s:
    case Queued{}:
      [Lv{k, c, Queued{}}]
    case Granted{}:
      [Lv{k, c, Granted{}}]
    case Held{}:
      [Lv{k, c, Held{}}]
    case Preempted{}:
      [Lv{k, c, Preempted{}}]
    case Ended{}:
      Nil{}

def lv.admit.ia(+l: Lim, +q: Nat, +ts: List<&2, Lv>, k: Nat) -> List<&2, Lv>:
  List.append(&2, Lv, lv.preempt(ts), lv.fresh(admit.ia.st(Bool.and(isz(lv.cnt(Waiting{}, Ia{}, ts)), room(l, lv.cnt(Holding{}, Ia{}, ts))), le(q, lv.cnt(Waiting{}, Ia{}, ts))), k, Ia{}))

def lv.admit.bg(+l: Lim, +ts: List<&2, Lv>, k: Nat) -> List<&2, Lv>:
  List.append(&2, Lv, ts, lv.fresh(admit.bg.st(Bool.and(isz(lv.cnt(Holding{}, Ia{}, ts)), Bool.and(isz(lv.cnt(Waiting{}, Ia{}, ts)), Bool.and(isz(lv.cnt(Waiting{}, Bg{}, ts)), room(l, lv.held(ts)))))), k, Bg{}))

def lv.find.at(b: Bool, s: Sts, r: Maybe<&2, Sts>) -> Maybe<&2, Sts>:
  match b:
    case True{}:
      Some{s}
    case False{}:
      r

# the status of live ticket k (none: ended, or never admitted)
def lv.find(ts: List<&2, Lv>, +k: Nat) -> Maybe<&2, Sts>:
  match ts:
    case Nil{}:
      None{}
    case Lv{+j, c, s} <> r:
      lv.find.at(Nat.is_eq(j, k), s, lv.find(r, k))

def lv.set.at(b: Bool, t: Lv, x: Sts) -> Lv:
  match b:
    case True{}:
      match t:
        case Lv{k, c, s}:
          Lv{k, c, x}
    case False{}:
      t

# ticket k gets status x
def lv.set(ts: List<&2, Lv>, +k: Nat, +x: Sts) -> List<&2, Lv>:
  match ts:
    case Nil{}:
      Nil{}
    case Lv{+j, c, s} <> r:
      lv.set.at(Nat.is_eq(j, k), Lv{j, c, s}, x) <> lv.set(r, k, x)

def lv.drop.at(b: Bool, t: Lv, r: List<&2, Lv>) -> List<&2, Lv>:
  match b:
    case True{}:
      r
    case False{}:
      t <> r

# ticket k ends: it leaves
def lv.drop(ts: List<&2, Lv>, +k: Nat) -> List<&2, Lv>:
  match ts:
    case Nil{}:
      Nil{}
    case Lv{+j, c, s} <> r:
      lv.drop.at(Nat.is_eq(j, k), Lv{j, c, s}, lv.drop(r, k))

def lv.collect(m: Maybe<&2, Sts>, +ts: List<&2, Lv>, k: Nat) -> List<&2, Lv>:
  match m:
    case Some{Granted{}}:
      lv.set(ts, k, Held{})
    case Some{Queued{}}:
      ts
    case Some{Held{}}:
      ts
    case Some{Preempted{}}:
      ts
    case Some{Ended{}}:
      ts
    case None{}:
      ts

def lv.release(m: Maybe<&2, Sts>, +l: Lim, +ts: List<&2, Lv>, k: Nat) -> List<&2, Lv>:
  match m:
    case Some{Held{}}:
      lv.grant(l, lv.drop(ts, k))
    case Some{Preempted{}}:
      lv.drop(ts, k)
    case Some{Queued{}}:
      ts
    case Some{Granted{}}:
      ts
    case Some{Ended{}}:
      ts
    case None{}:
      ts

def lv.leave(m: Maybe<&2, Sts>, +l: Lim, +ts: List<&2, Lv>, k: Nat) -> List<&2, Lv>:
  match m:
    case Some{Queued{}}:
      lv.grant(l, lv.drop(ts, k))
    case Some{Granted{}}:
      lv.grant(l, lv.drop(ts, k))
    case Some{Held{}}:
      ts
    case Some{Preempted{}}:
      ts
    case Some{Ended{}}:
      ts
    case None{}:
      ts

# one op on the live controller
def Live.step(x: Live, o: Op) -> Live:
  match x:
    case Live{+l, +q, +ts, +n}:
      match o:
        case Admit{Ia{}}:
          Live{l, q, lv.admit.ia(l, q, ts, n), 1n+n}
        case Admit{Bg{}}:
          Live{l, q, lv.admit.bg(l, ts, n), 1n+n}
        case Collect{+k}:
          Live{l, q, lv.collect(lv.find(ts, k), ts, k), n}
        case Release{+k}:
          Live{l, q, lv.release(lv.find(ts, k), l, ts, k), n}
        case Leave{+k}:
          Live{l, q, lv.leave(lv.find(ts, k), l, ts, k), n}
        case Limit{+l2, q2}:
          Live{l2, q2, lv.grant(l2, ts), n}

def Live.run(os: List<&2, Op>, x: Live) -> Live:
  match os:
    case Nil{}:
      x
    case o <> r:
      Live.run(r, Live.step(x, o))

def Live.new(l: Lim, q: Nat) -> Live:
  Live{l, q, Nil{}, 0n}

# What the laws speak of
# ----------------------

# no lost wake-up: some waiter may take a free slot
def grantable(+s: St) -> Bool:
  match s:
    case St{+l, q, +ts}:
      Maybe.is_some(&2, Cls, pick(l, ts))

# a background slot is held only while no interactive request holds a
# slot or waits
def calm.n(hi: Nat, wi: Nat, hb: Nat) -> Bool:
  Bool.or(isz(hb), Bool.and(isz(hi), isz(wi)))

def calm(+ts: List<&2, Tk>) -> Bool:
  calm.n(cnt(Holding{}, Ia{}, ts), cnt(Waiting{}, Ia{}, ts), cnt(Holding{}, Bg{}, ts))

# the slots an op frees itself, before any grant: a release or a granted
# waiter that leaves, one; an interactive admit, every background slot
def freed.at(m: Maybe<&2, Tk>, rel: Bool) -> Nat:
  match m rel:
    case Some{Tk{c, Held{}}} True{}:
      1n
    case Some{Tk{c, Granted{}}} False{}:
      1n
    case _ _:
      0n

def freed(+s: St, o: Op) -> Nat:
  match o:
    case Admit{Ia{}}:
      cnt(Holding{}, Bg{}, St.ts(s))
    case Admit{Bg{}}:
      0n
    case Collect{k}:
      0n
    case Release{k}:
      freed.at(get(St.ts(s), k), True{})
    case Leave{k}:
      freed.at(get(St.ts(s), k), False{})
    case Limit{l, q}:
      0n

# fifo(c, ts, seen): no ticket of class c holds a slot after one of its
# class that waits (seen: one waited before ts)
def fifo(+c: Cls, ts: List<&2, Tk>, +seen: Bool) -> Bool:
  match ts:
    case Nil{}:
      True{}
    case +h <> r:
      Bool.and(Bool.not(Bool.and(seen, hit(Holding{}, c, h))), fifo(c, r, Bool.or(seen, hit(Waiting{}, c, h))))

def fifo.both(+ts: List<&2, Tk>) -> Bool:
  Bool.and(fifo(Ia{}, ts, False{}), fifo(Bg{}, ts, False{}))

# ticket m waits, interactive
def waits.ia(m: Maybe<&2, Tk>) -> Bool:
  match m:
    case Some{Tk{Ia{}, Queued{}}}:
      True{}
    case _:
      False{}

# what interactive ticket w waits for: the interactive slots held and the
# interactive waiters ahead of it (interactive tickets before w that hold
# or wait, and interactive slots from w on)
def pot(ts: List<&2, Tk>, w: Nat) -> Nat:
  match ts:
    case Nil{}:
      0n
    case +h <> +r:
      match w:
        case 0n:
          cnt(Holding{}, Ia{}, h <> r)
        case 1n+p:
          bit(Bool.or(hit(Holding{}, Ia{}, h), hit(Waiting{}, Ia{}, h)), pot(r, p))

def ahead(+s: St, w: Nat) -> Nat:
  pot(St.ts(s), w)

# an op frees an interactive slot
def frees.at(m: Maybe<&2, Tk>, rel: Bool) -> Nat:
  match m rel:
    case Some{Tk{Ia{}, Held{}}} True{}:
      1n
    case Some{Tk{Ia{}, Granted{}}} False{}:
      1n
    case _ _:
      0n

def frees(+s: St, o: Op) -> Nat:
  match o:
    case Admit{c}:
      0n
    case Collect{k}:
      0n
    case Release{k}:
      frees.at(get(St.ts(s), k), True{})
    case Leave{k}:
      frees.at(get(St.ts(s), k), False{})
    case Limit{l, q}:
      0n

# the interactive slots freed along a run
def frees.run(os: List<&2, Op>, +s: St) -> Nat:
  match os:
    case Nil{}:
      0n
    case +o <> r:
      Nat.add(frees(s, o), frees.run(r, step(s, o)))

def status(+s: St, k: Nat) -> Maybe<&2, Tk>:
  get(St.ts(s), k)

# ticket w waits, interactive, before and after every op of a run
def waits.thru(os: List<&2, Op>, +s: St, +w: Nat) -> Bool:
  match os:
    case Nil{}:
      waits.ia(status(s, w))
    case +o <> r:
      Bool.and(waits.ia(status(s, w)), waits.thru(r, step(s, o), w))

def ended(m: Maybe<&2, Tk>) -> Bool:
  match m:
    case Some{Tk{c, Ended{}}}:
      True{}
    case _:
      False{}

# the op by which ticket m's holder ends it: a waiter leaves, a permit
# is released
def finish(m: Maybe<&2, Tk>, k: Nat) -> Op:
  match m:
    case Some{Tk{c, Queued{}}}:
      Leave{k}
    case Some{Tk{c, Granted{}}}:
      Leave{k}
    case _:
      Release{k}
