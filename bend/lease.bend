# lease: the model of the chat's root-turn lease (docs/harness.md, H6):
# one holder, then the waiters in the order they asked. The Rust code is
# `Turns` in crates/eukhe-core/src/memory/service/turn.rs; the bridge
# (bridge/bridge_wait.bend, crates/eukhe-core/src/memory/service/turn/bridge.rs)
# runs both on the same events.
#
# A waiter asks (it gets the next key, so keys are the order of arrival);
# the holder or a waiter releases; a waiter stops waiting (its reply is
# dropped: it stays in the queue, dead, until a grant passes it over); a
# connection crashes (every lease of its origin ends). Whenever the lease
# is free, it goes to the first live waiter.

import Base

type Ev is Data:
  Ask{origin: Nat}
  Release{key: Nat}
  Stop{key: Nat}
  Crash{origin: Nat}

type Lease is Data:
  Lease{key: Nat, origin: Nat}

type Waiter is Data:
  Waiter{key: Nat, origin: Nat, live: Bool}

# the next key, the holder, the waiters in arrival order
type L is Data:
  L{next: Nat, holder: Maybe<&2, Lease>, queue: List<&2, Waiter>}

def L.empty() -> L:
  L{0n, None{}, Nil{}}

def L.holder(s: L) -> Maybe<&2, Lease>:
  match s:
    case L{n, h, q}:
      h

def L.queue(s: L) -> List<&2, Waiter>:
  match s:
    case L{n, h, q}:
      q

def L.next(s: L) -> Nat:
  match s:
    case L{n, h, q}:
      n

# The grant
# ---------

# the first live waiter
def pick(q: List<&2, Waiter>) -> Maybe<&2, Lease>:
  match q:
    case Nil{}:
      None{}
    case w <> t:
      match w:
        case Waiter{k, o, l}:
          match l:
            case True{}:
              Some{Lease{k, o}}
            case False{}:
              pick(t)

# the waiters after it: the dead ones before it are passed over
def after(q: List<&2, Waiter>) -> List<&2, Waiter>:
  match q:
    case Nil{}:
      Nil{}
    case w <> t:
      match w:
        case Waiter{k, o, l}:
          match l:
            case True{}:
              t
            case False{}:
              after(t)

# a free lease goes to the first live waiter
def settle(n: Nat, h: Maybe<&2, Lease>, +q: List<&2, Waiter>) -> L:
  match h:
    case None{}:
      L{n, pick(q), after(q)}
    case Some{x}:
      L{n, Some{x}, q}

# The events
# ----------

# whether e ends waiter w: a release or a stop of its key, a crash of its
# origin
def hits(e: Ev, w: Waiter) -> Bool:
  match e:
    case Ask{p}:
      False{}
    case Release{j}:
      match w:
        case Waiter{k, o, l}:
          Nat.is_eq(k, j)
    case Stop{j}:
      match w:
        case Waiter{k, o, l}:
          Nat.is_eq(k, j)
    case Crash{p}:
      match w:
        case Waiter{k, o, l}:
          Nat.is_eq(o, p)

def drop.put(hit: Bool, w: Waiter, r: List<&2, Waiter>) -> List<&2, Waiter>:
  match hit:
    case True{}:
      r
    case False{}:
      w <> r

# the waiters e does not end
def drop(+e: Ev, q: List<&2, Waiter>) -> List<&2, Waiter>:
  match q:
    case Nil{}:
      Nil{}
    case +w <> t:
      drop.put(hits(e, w), w, drop(e, t))

# the waiters, those e ends dead
def mark(+e: Ev, q: List<&2, Waiter>) -> List<&2, Waiter>:
  match q:
    case Nil{}:
      Nil{}
    case w <> t:
      match w:
        case Waiter{+k, +o, +l}:
          Waiter{k, o, Bool.and(l, Bool.not(hits(e, Waiter{k, o, l})))} <> mark(e, t)

# a release: the holder's frees the lease; a waiter's leaves the queue
def release.holder(hit: Bool, x: Lease, +j: Nat, +n: Nat, +q: List<&2, Waiter>) -> L:
  match hit:
    case True{}:
      settle(n, None{}, q)
    case False{}:
      settle(n, Some{x}, drop(Release{j}, q))

def release(+j: Nat, +n: Nat, h: Maybe<&2, Lease>, +q: List<&2, Waiter>) -> L:
  match h:
    case None{}:
      settle(n, None{}, drop(Release{j}, q))
    case Some{x}:
      match x:
        case Lease{+hk, ho}:
          release.holder(Nat.is_eq(hk, j), Lease{hk, ho}, j, n, q)

def crash.put(hit: Bool, x: Lease) -> Maybe<&2, Lease>:
  match hit:
    case True{}:
      None{}
    case False{}:
      Some{x}

# a crash ends the holder's lease when it is of the origin
def crash.holder(+p: Nat, h: Maybe<&2, Lease>) -> Maybe<&2, Lease>:
  match h:
    case None{}:
      None{}
    case Some{x}:
      match x:
        case Lease{hk, +ho}:
          crash.put(Nat.is_eq(ho, p), Lease{hk, ho})

def step(s: L, e: Ev) -> L:
  match s:
    case L{+n, h, +q}:
      match e:
        case Ask{o}:
          settle(1n+n, h, List.append(&2, Waiter, q, [Waiter{n, o, True{}}]))
        case Release{j}:
          release(j, n, h, q)
        case Stop{j}:
          L{n, h, mark(Stop{j}, q)}
        case Crash{+p}:
          settle(n, crash.holder(p, h), drop(Crash{p}, q))

# the state after evs, from s
def go(evs: List<&2, Ev>, s: L) -> L:
  match evs:
    case Nil{}:
      s
    case e <> rest:
      go(rest, step(s, e))

def run(evs: List<&2, Ev>) -> L:
  go(evs, L.empty())

# What the laws speak of
# ----------------------

def Waiter.key(w: Waiter) -> Nat:
  match w:
    case Waiter{k, o, l}:
      k

def Waiter.live(w: Waiter) -> Bool:
  match w:
    case Waiter{k, o, l}:
      l

# x is in q
def In(+x: Waiter, q: List<&2, Waiter>) -> Type:
  match q:
    case Nil{}:
      Empty
    case +w <> t:
      Or({x == w : Waiter}, In(x, t))

# k is above the bound lo (None: no bound)
def above(+k: Nat, lo: Maybe<&2, Nat>) -> Bool:
  match lo:
    case None{}:
      True{}
    case Some{l}:
      Nat.is_lt(l, k)

# the keys of q rise, all above lo
def Asc(lo: Maybe<&2, Nat>, q: List<&2, Waiter>) -> Type:
  match q:
    case Nil{}:
      Unit
    case +w <> t:
      ({above(Waiter.key(w), lo) == True{} : Bool} & Asc(Some{Waiter.key(w)}, t))

def hkey(h: Maybe<&2, Lease>) -> Maybe<&2, Nat>:
  match h:
    case None{}:
      None{}
    case Some{x}:
      match x:
        case Lease{k, o}:
          Some{k}

# first come, first served: the holder came before every waiter, and the
# waiters wait in the order they came
def Fifo(+s: L) -> Type:
  Asc(hkey(L.holder(s)), L.queue(s))

# every waiter of q is dead
def Dead(q: List<&2, Waiter>) -> Type:
  match q:
    case Nil{}:
      Unit
    case +w <> t:
      ({Waiter.live(w) == False{} : Bool} & Dead(t))

# the lease is held, or no live waiter waits for it
def Busy(s: L) -> Type:
  match s:
    case L{n, h, +q}:
      match h:
        case None{}:
          Dead(q)
        case Some{x}:
          Unit

# k is the holder or a live waiter of origin o
def Kept(+k: Nat, +o: Nat, +s: L) -> Type:
  Or({L.holder(s) == Some{Lease{k, o}} : Maybe<&2, Lease>}, In(Waiter{k, o, True{}}, L.queue(s)))

# k does not hold the lease
def NotHeld(+k: Nat, h: Maybe<&2, Lease>) -> Type:
  match h:
    case None{}:
      Unit
    case Some{x}:
      match x:
        case Lease{hk, ho}:
          {hk == k : Nat} -> Empty

# no lease of origin o is held or waited for
def Freed(+o: Nat, s: L) -> Type:
  match s:
    case L{n, h, +q}:
      (NotFrom(o, h) & NoneFrom(o, q))

def NotFrom(+o: Nat, h: Maybe<&2, Lease>) -> Type:
  match h:
    case None{}:
      Unit
    case Some{x}:
      match x:
        case Lease{hk, ho}:
          {Nat.is_eq(ho, o) == False{} : Bool}

def NoneFrom(+o: Nat, q: List<&2, Waiter>) -> Type:
  match q:
    case Nil{}:
      Unit
    case w <> t:
      match w:
        case Waiter{k, wo, l}:
          ({Nat.is_eq(wo, o) == False{} : Bool} & NoneFrom(o, t))
