# progress: what counts as progress when the harness checks a loop. The
# Rust code is the host of the work ledger (crates/eukhe-core/src/durable/
# children/work.rs, `WorkLedger`, which feeds the stepper of
# bend/ffi_work.bend), the goal's progress check (`stall_check` in
# crates/eukhe-core/src/durable/goals/state.rs, `goal_check` in
# goals/hooks.rs: bend/ffi_work.bend `ffi`, then bend/ffi_progress.bend),
# and the subagent watch that reads the ledger's count as the child's
# progress token (crates/eukhe-daemon/src/worker/run_outcome.rs, with
# `look` in bend/child.bend).
#
# - An act is a number (a Nat): a tool call with its result (`act`), or
#   an accepted progress note (`note`). Two acts with the same number are
#   the same act.
# - The ledger keeps the distinct acts it read (`ledger`); the work is
#   their number (`work`). The host's ledger (`Led`, `next`) reads the
#   blocks of the transcript's entries: a call waits for its result, a
#   result is the act of the call with it; nothing else is an act. It
#   keeps each act whole (`Act`), as its fingerprints, not as its number.
# - The goal's progress check runs at each goal continuation: the work
#   grew since the last check, or not. New work clears the count of
#   continuations in a row with no new work; else the count grows by one,
#   and at the cap (directors.stallSteps) the goal stops (`check`). It
#   compares with the last check only when that one was of the same run
#   and goal (`compared`).
#
# laws/progress.bend states what must hold; PROOF.bend proves it with
# proof/progress/.

import Base
import ./child.bend as Ch

# The ledger
# ----------

# x is one of the acts of s
def mem(+x: Nat, s: List<&2, Nat>) -> Bool:
  match s:
    case Nil{}:
      False{}
    case h <> t:
      Bool.or(Nat.is_eq(h, x), mem(x, t))

def add.put(seen: Bool, x: Nat, s: List<&2, Nat>) -> List<&2, Nat>:
  match seen:
    case True{}:
      s
    case False{}:
      x <> s

# the acts of s, and x when it is new
def add(+s: List<&2, Nat>, +x: Nat) -> List<&2, Nat>:
  add.put(mem(x, s), x, s)

# the distinct acts after reading xs, oldest first, on top of s
def ledger(xs: List<&2, Nat>, +s: List<&2, Nat>) -> List<&2, Nat>:
  match xs:
    case Nil{}:
      s
    case +h <> t:
      ledger(t, add(s, h))

# the work of a session whose acts are xs: its distinct acts
def work(xs: List<&2, Nat>) -> Nat:
  List.length(&2, Nat, ledger(xs, Nil{}))

# x is an act of xs
def In(+x: Nat, xs: List<&2, Nat>) -> Type:
  match xs:
    case Nil{}:
      Empty
    case +h <> t:
      Or({x == h : Nat}, In(x, t))

# every act of xs is an act of s
def Within(xs: List<&2, Nat>, +s: List<&2, Nat>) -> Type:
  match xs:
    case Nil{}:
      Unit
    case +h <> t:
      In(h, s) & Within(t, s)

# The goal's progress check
# -------------------------

# the check's verdict: continue with stalls continuations in a row that did
# no new work, or stop (the goal pauses) at that count
type Goal is Data:
  Go{stalls: Nat}
  Stop{stalls: Nat}

def strike.put(stop: Bool, n: Nat) -> Goal:
  match stop:
    case True{}:
      Stop{n}
    case False{}:
      Go{n}

# one more continuation with no new work after s of them
def strike(+cap: Nat, +s: Nat) -> Goal:
  strike.put(Nat.is_le(cap, 1n+s), 1n+s)

# the check at one continuation: the work grew since the last one, or not
def check(+cap: Nat, +s: Nat, grew: Bool) -> Goal:
  match grew:
    case True{}:
      Go{0n}
    case False{}:
      strike(cap, s)

# whether the work of hist ++ seg is more than the work of hist
def grew(+hist: List<&2, Nat>, seg: List<&2, Nat>) -> Bool:
  Nat.is_le(1n+work(hist), work(List.append(&2, Nat, hist, seg)))

# the goal loop: a check at each continuation, each one after the acts
# seg of the run since the last check, on the session's acts hist; a
# stopped goal stays stopped
def goal(segs: List<&2, List<&2, Nat>>, +cap: Nat, +hist: List<&2, Nat>, g: Goal) -> Goal:
  match segs:
    case Nil{}:
      g
    case +seg <> rest:
      match g:
        case Go{s}:
          goal(rest, cap, List.append(&2, Nat, hist, seg), check(cap, s, grew(hist, seg)))
        case Stop{s}:
          Stop{s}

def Goal.stopped(g: Goal) -> Bool:
  match g:
    case Go{s}:
      False{}
    case Stop{s}:
      True{}

# every segment of segs holds only acts of hist
def Repeats(segs: List<&2, List<&2, Nat>>, +hist: List<&2, Nat>) -> Type:
  match segs:
    case Nil{}:
      Unit
    case +seg <> rest:
      Within(seg, hist) & Repeats(rest, hist)

# The check the Rust goal loop runs
# ---------------------------------
# The Rust loop keeps, per run and goal, the count of stalls and the work
# (the ledger's count) at the last check, and compares counts: the work
# grew when its count did. The compiled core's wire carries a Nat up to
# 10^14 - 1, so the count is held below t = 10^14 - 1 and one more stall
# stays within t.

# the last check of the same run and goal: its count of stalls and the
# work then
type Prior is Data:
  Prior{stalls: Nat, work: Nat}

def Goal.stalls(g: Goal) -> Nat:
  match g:
    case Go{s}:
      s
    case Stop{s}:
      s

# the check at a continuation whose work is now `work`, after prior p
# (None: the first check of the run or the goal starts the count)
def judge(+t: Nat, +cap: Nat, p: Maybe<&2, Prior>, +work: Nat) -> Goal:
  match p:
    case None{}:
      Go{0n}
    case Some{x}:
      match x:
        case Prior{s, w}:
          check(cap, Nat.min(s, Nat.sub(t, 1n)), Nat.is_lt(w, work))

# the last check the goal loop stored: whether it was of the same run (the
# run's first input) and of the same goal as the check now, its count of
# stalls and the work then
type Last is Data:
  Last{run: Bool, goal: Bool, stalls: Nat, work: Nat}

def compared.of(same: Bool, +s: Nat, +w: Nat) -> Maybe<&2, Prior>:
  match same:
    case True{}:
      Some{Prior{s, w}}
    case False{}:
      None{}

# the prior check the check now compares with: the last one, when it was
# of the same run and the same goal (else the check starts the count)
def compared(m: Maybe<&2, Last>) -> Maybe<&2, Prior>:
  match m:
    case None{}:
      None{}
    case Some{x}:
      match x:
        case Last{r, g, s, w}:
          compared.of(Bool.and(r, g), s, w)

# The ledger the Rust host keeps
# ------------------------------
# The host (crates/eukhe-core/src/durable/children/work.rs) moves bytes:
# it fingerprints each message block of a transcript entry and each
# accepted progress note (a Nat below 2^46) and feeds them to the stepper
# of bend/ffi_work.bend, which keeps this ledger. The ledger decides what
# a block adds, which acts are new, which entries it reads, and the work.

# a message block, as the host fingerprints it: a tool call (the key of
# its id, the fingerprint of its name and arguments), a tool result (the
# key of its call's id, the fingerprint of its tool name, content and
# error flag), text, thinking, a user message, a system message
type Blk is Data:
  Call{key: Nat, fp: Nat}
  Res{key: Nat, fp: Nat}
  Txt{}
  Think{}
  User{}
  Sys{}

# a transcript entry: its id and its blocks, in order
type Ent is Data:
  Ent{id: Nat, bs: List<&2, Blk>}

# a call whose result did not come yet
type Pend is Data:
  Pend{key: Nat, fp: Nat}

# an act the ledger reads: a tool result with the fingerprint of the call
# that waited for it (None: no call of its id waited), or an accepted
# progress note. The ledger keeps acts whole (two fingerprints of up to 46
# bits each), so no two different acts merge; `act` and `note` number them
# for the laws, which count acts as Nats (`work`).
type Act is Data:
  ARes{call: Maybe<&2, Nat>, res: Nat}
  ANote{fp: Nat}

# the ledger: the distinct acts (each once, newest first), the calls
# waiting for their result, how many entries of the shown view it read,
# and the id of the last entry it read
type Led is Data:
  Led{seen: List<&2, Act>, calls: List<&2, Pend>, read: Nat, last: Maybe<&2, Nat>}

# a ledger that read nothing
def Led.empty() -> Led:
  Led{Nil{}, Nil{}, 0n, None{}}

def pend.hit(hit: Bool, f: Nat, rest: Maybe<&2, Nat>) -> Maybe<&2, Nat>:
  match hit:
    case True{}:
      Some{f}
    case False{}:
      rest

# the fingerprint of the waiting call of key k
def pend.get(cs: List<&2, Pend>, +k: Nat) -> Maybe<&2, Nat>:
  match cs:
    case Nil{}:
      None{}
    case c <> t:
      match c:
        case Pend{j, f}:
          pend.hit(Nat.is_eq(j, k), f, pend.get(t, k))

def pend.del.at(hit: Bool, j: Nat, f: Nat, rest: List<&2, Pend>) -> List<&2, Pend>:
  match hit:
    case True{}:
      rest
    case False{}:
      Pend{j, f} <> rest

# the waiting calls but those of key k
def pend.del(cs: List<&2, Pend>, +k: Nat) -> List<&2, Pend>:
  match cs:
    case Nil{}:
      Nil{}
    case c <> t:
      match c:
        case Pend{+j, f}:
          pend.del.at(Nat.is_eq(j, k), j, f, pend.del(t, k))

def meq(a: Maybe<&2, Nat>, b: Maybe<&2, Nat>) -> Bool:
  match a b:
    case None{} None{}:
      True{}
    case None{} Some{y}:
      False{}
    case Some{x} None{}:
      False{}
    case Some{x} Some{y}:
      Nat.is_eq(x, y)

# a and b are the same act: both results with the same call (or both with
# none) and the same result, or both notes with the same fingerprint
def Act.same(a: Act, b: Act) -> Bool:
  match a b:
    case ARes{m, r} ARes{n, x}:
      Bool.and(meq(m, n), Nat.is_eq(r, x))
    case ARes{m, r} ANote{y}:
      False{}
    case ANote{x} ARes{n, y}:
      False{}
    case ANote{x} ANote{y}:
      Nat.is_eq(x, y)

# x is one of the acts of s
def has(+x: Act, s: List<&2, Act>) -> Bool:
  match s:
    case Nil{}:
      False{}
    case h <> t:
      Bool.or(Act.same(h, x), has(x, t))

def put.at(seen: Bool, x: Act, s: List<&2, Act>) -> List<&2, Act>:
  match seen:
    case True{}:
      s
    case False{}:
      x <> s

# the acts of s, and x when it is new
def put(+s: List<&2, Act>, +x: Act) -> List<&2, Act>:
  put.at(has(x, s), x, s)

# The numbers of the acts (for the laws; the ledger never computes them):
# n with k odd steps on top, 2n at the bottom, so k and n are read back
def tower(k: Nat, n: Nat) -> Nat:
  match k:
    case 0n:
      Nat.double(n)
    case 1n+j:
      1n+Nat.double(tower(j, n))

# the number of a result of fingerprint r whose call waited with
# fingerprint m (None: no call of its id waited)
def act(m: Maybe<&2, Nat>, r: Nat) -> Nat:
  match m:
    case None{}:
      tower(1n, r)
    case Some{c}:
      tower(2n+c, r)

# the number of an accepted progress note of fingerprint x
def note(x: Nat) -> Nat:
  tower(0n, x)

# the ledger after one block: a call waits (it replaces a call of the same
# id), a result is the act of its call (which stops waiting); text,
# thinking, user and system messages are no act
def Led.blk(l: Led, b: Blk) -> Led:
  match l:
    case Led{s, +cs, r, z}:
      match b:
        case Call{+k, f}:
          Led{s, Pend{k, f} <> pend.del(cs, k), r, z}
        case Res{+k, x}:
          Led{put(s, ARes{pend.get(cs, k), x}), pend.del(cs, k), r, z}
        case Txt{}:
          Led{s, cs, r, z}
        case Think{}:
          Led{s, cs, r, z}
        case User{}:
          Led{s, cs, r, z}
        case Sys{}:
          Led{s, cs, r, z}

def Led.blks(bs: List<&2, Blk>, l: Led) -> Led:
  match bs:
    case Nil{}:
      l
    case b <> t:
      Led.blks(t, Led.blk(l, b))

# the ledger after reading entry e: e is the last entry read
def Led.ent(l: Led, e: Ent) -> Led:
  match l:
    case Led{s, cs, r, z}:
      match e:
        case Ent{i, bs}:
          Led.blks(bs, Led{s, cs, r, Some{i}})

def Led.ents(es: List<&2, Ent>, l: Led) -> Led:
  match es:
    case Nil{}:
      l
    case e <> t:
      Led.ents(t, Led.ent(l, e))

# an entry of id i is newer than the last entry read
def newer(m: Maybe<&2, Nat>, +i: Nat) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{x}:
      Nat.is_lt(x, i)

def Led.page.at(new: Bool, l: Led, e: Ent) -> Led:
  match new:
    case True{}:
      Led.ent(l, e)
    case False{}:
      l

def Led.last(l: Led) -> Maybe<&2, Nat>:
  match l:
    case Led{s, c, r, z}:
      z

def Ent.id(e: Ent) -> Nat:
  match e:
    case Ent{i, bs}:
      i

# a page of entries in id order: the ledger reads those newer than the
# last entry it read
def Led.page(es: List<&2, Ent>, l: Led) -> Led:
  match es:
    case Nil{}:
      l
    case +e <> t:
      +m = l
      Led.page(t, Led.page.at(newer(Led.last(m), Ent.id(e)), m, e))

# the view still holds the entries the ledger read: it read none, or the
# view's entry at the place of the last one read (at) is that entry
def kept(r: Nat, at: Maybe<&2, Nat>, z: Maybe<&2, Nat>) -> Bool:
  match r:
    case 0n:
      True{}
    case 1n+p:
      meq(at, z)

# what the host feeds the ledger: the shown view (the id of its entry at
# the place of the last entry read, None when there is none, and its
# entries from that place on), a page of entries in id order, or an
# accepted progress note
type Ev is Data:
  View{at: Maybe<&2, Nat>, es: List<&2, Ent>}
  Page{es: List<&2, Ent>}
  Note{fp: Nat}

# the ledger's answer: its work, how many entries of the view it read and
# the id of the last entry read; or, for a view that no longer holds what
# it read, Again: the ledger starts over, and the host sends the view from
# its start
type Out is Data:
  Read{work: Nat, read: Nat, last: Maybe<&2, Nat>}
  Again{}

def Led.out(l: Led) -> Out:
  match l:
    case Led{s, c, r, z}:
      Read{List.length(&2, Act, s), r, z}

def Led.done(l: Led) -> Led & Out:
  +m = l
  (m, Led.out(m))

# the ledger after it read n more entries of the view
def Led.seen(l: Led, n: Nat) -> Led:
  match l:
    case Led{s, c, r, z}:
      Led{s, c, Nat.add(r, n), z}

def Led.view.at(k: Bool, +es: List<&2, Ent>, l: Led) -> Led & Out:
  match k:
    case True{}:
      Led.done(Led.seen(Led.ents(es, l), List.length(&2, Ent, es)))
    case False{}:
      (Led.empty(), Again{})

# the ledger after one event, and its answer
def next(l: Led, e: Ev) -> Led & Out:
  match l:
    case Led{s, c, +r, +z}:
      match e:
        case View{at, es}:
          Led.view.at(kept(r, at, z), es, Led{s, c, r, z})
        case Page{es}:
          Led.done(Led.page(es, Led{s, c, r, z}))
        case Note{x}:
          Led.done(Led{put(s, ANote{x}), c, r, z})

# The subagent watch
# ------------------
# The parent's watch polls the child; each poll reads the child unsettled
# with its progress token, the work of its acts so far, 1 + dt ms after the
# last poll.

type Peek is Data:
  Peek{seg: List<&2, Nat>, dt: Nat}

def watch.step(+cfg: Ch.Cfg, t: Nat, +dt: Nat, x: Ch.Next) -> Ch.Next:
  match x:
    case Ch.Watch{w}:
      Ch.look(cfg, w, 1n+dt, Ch.Busy{Some{t}})
    case Ch.Owe{k}:
      Ch.Owe{k}
    case Ch.Quiet{}:
      Ch.Quiet{}

# the watch's verdict after the polls ps, each after the acts seg the child
# did since the last poll, on the child's acts hist, from verdict x
def watch(ps: List<&2, Peek>, +cfg: Ch.Cfg, +hist: List<&2, Nat>, x: Ch.Next) -> Ch.Next:
  match ps:
    case Nil{}:
      x
    case p <> rest:
      match p:
        case Peek{+seg, +dt}:
          +now = List.append(&2, Nat, hist, seg)
          watch(rest, cfg, now, watch.step(cfg, work(now), dt, x))

# every poll of ps shows only acts of hist
def Loops(ps: List<&2, Peek>, +hist: List<&2, Nat>) -> Type:
  match ps:
    case Nil{}:
      Unit
    case p <> rest:
      match p:
        case Peek{seg, dt}:
          Within(seg, hist) & Loops(rest, hist)
