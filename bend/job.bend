# job: the model of one job, one blocking call on it, and the job table
# at a rewind. A tool call's journal is
# bend/tool_call.bend.
#
# A job is anything that runs long: a shell, a cell, a subagent, a call
# that ran too long. It has an output, an exit status and a kill. It sees
# its events one at a time, in any order the adversary picks.
#
# The output limit is a cap in bytes: Some{c} keeps at most c bytes and
# counts the rest as dropped; None (the explicit opt-out) keeps all.
# Truncation is on by default: the Rust default is Some.
#
# The Rust jobs (crates/eukhe-core/src/durable/jobs/) run `feed`, `kills`
# and `poll` as the compiled Bend core (ffi_job, ffi_job_rewind,
# ffi_job_wait); no Rust copy of a rule remains. The laws
# job_wait_polls_* tie `wait` to `poll`.

import Base

# A job
# -----

# An exit status: the i64 the process reported, as its two 32-bit words,
# high first (two's complement), so every i64 is exactly one Code
type Code is Data:
  Code{hi: U32, lo: U32}

# What a job sees
type JEv is Data:
  Out{n: Nat}      # n bytes of output
  Quit{code: Code} # the process exits with code
  Kill{}           # the kill signal
  Tick{}           # one tick of time

# How a job ends
type End is Data:
  Exited{code: Code}
  Killed{}

# A job: live with the bytes kept and dropped, or ended
type J is Data:
  Live{kept: Nat, dropped: Nat}
  Ended{kept: Nat, dropped: Nat, end: End}

def J.kept(j: J) -> Nat:
  match j:
    case Live{k, d}:
      k
    case Ended{k, d, e}:
      k

def J.dropped(j: J) -> Nat:
  match j:
    case Live{k, d}:
      d
    case Ended{k, d, e}:
      d

def J.done(j: J) -> Bool:
  match j:
    case Live{k, d}:
      False{}
    case Ended{k, d, e}:
      True{}

# the bytes of n that fit after kept under the cap
def take(cap: Maybe<&2, Nat>, +kept: Nat, +n: Nat) -> Nat:
  match cap:
    case None{}:
      n
    case Some{c}:
      Nat.min(n, Nat.sub(c, kept))

# a running job's output of n more bytes
def out(+cap: Maybe<&2, Nat>, +k: Nat, d: Nat, +n: Nat) -> J:
  +t = take(cap, k, n)
  Live{Nat.add(k, t), Nat.add(d, Nat.sub(n, t))}

# one event
def step(+cap: Maybe<&2, Nat>, j: J, e: JEv) -> J:
  match j:
    case Ended{k, d, x}:
      Ended{k, d, x}
    case Live{k, d}:
      match e:
        case Out{n}:
          out(cap, k, d, n)
        case Quit{c}:
          Ended{k, d, Exited{c}}
        case Kill{}:
          Ended{k, d, Killed{}}
        case Tick{}:
          Live{k, d}

# what one event ends: the end, when it ends the job
def ends.of(j: J, e: JEv) -> List<&2, End>:
  match j:
    case Ended{k, d, x}:
      Nil{}
    case Live{k, d}:
      match e:
        case Out{n}:
          Nil{}
        case Quit{c}:
          [Exited{c}]
        case Kill{}:
          [Killed{}]
        case Tick{}:
          Nil{}

# The step the Rust jobs run
# --------------------------
# The compiled core's wire carries a Nat up to 10^14 - 1 (below the
# runtime's 2^48 - 1), so the Rust jobs hold a job's bytes kept plus
# dropped to t = 10^14 - 1 (about 90 TiB): an output counts only the
# bytes up to t. Below t, `feed` is `step`.

# the bytes kept plus dropped
def J.total(j: J) -> Nat:
  match j:
    case Live{k, d}:
      Nat.add(k, d)
    case Ended{k, d, e}:
      Nat.add(k, d)

# the event a live job with counts k and d sees under t: an output cut to
# the bytes left below t
def feed.ev(+t: Nat, +k: Nat, +d: Nat, e: JEv) -> JEv:
  match e:
    case Out{n}:
      Out{Nat.min(n, Nat.sub(Nat.sub(t, k), d))}
    case Quit{c}:
      Quit{c}
    case Kill{}:
      Kill{}
    case Tick{}:
      Tick{}

# one event, with the counts held to t
def feed(+t: Nat, +cap: Maybe<&2, Nat>, j: J, e: JEv) -> J:
  match j:
    case Live{+k, +d}:
      step(cap, Live{k, d}, feed.ev(t, k, d, e))
    case Ended{k, d, x}:
      Ended{k, d, x}

# the job after events es, from j
def go(es: List<&2, JEv>, +cap: Maybe<&2, Nat>, j: J) -> J:
  match es:
    case Nil{}:
      j
    case e <> rest:
      go(rest, cap, step(cap, j, e))

# every end the job reports, in order
def ends.go(es: List<&2, JEv>, +cap: Maybe<&2, Nat>, +j: J) -> List<&2, End>:
  match es:
    case Nil{}:
      Nil{}
    case +e <> rest:
      List.append(&2, End, ends.of(j, e), ends.go(rest, cap, step(cap, j, e)))

# a new job that sees es
def run(+cap: Maybe<&2, Nat>, es: List<&2, JEv>) -> J:
  go(es, cap, Live{0n, 0n})

def ends(+cap: Maybe<&2, Nat>, es: List<&2, JEv>) -> List<&2, End>:
  ends.go(es, cap, Live{0n, 0n})

# the bytes the job wrote before it ended
def produced(es: List<&2, JEv>) -> Nat:
  match es:
    case Nil{}:
      0n
    case e <> rest:
      match e:
        case Out{n}:
          Nat.add(n, produced(rest))
        case Quit{c}:
          0n
        case Kill{}:
          0n
        case Tick{}:
          produced(rest)

# es holds an exit or a kill
def has_end(es: List<&2, JEv>) -> Bool:
  match es:
    case Nil{}:
      False{}
    case e <> rest:
      match e:
        case Out{n}:
          has_end(rest)
        case Quit{c}:
          True{}
        case Kill{}:
          True{}
        case Tick{}:
          has_end(rest)

def once(b: Bool) -> Nat:
  match b:
    case True{}:
      1n
    case False{}:
      0n

# A blocking call
# ---------------
# A tool call that waits on its job waits at most `budget` ticks. Then
# the call returns, and the job goes on as a background job.

type Wait is Data:
  Settled{end: End}  # the job ended in time
  Detached{}         # the budget passed: the job runs on in the background

# the call's answer after events es, with `left` ticks of budget left:
# None while it still waits
def wait(es: List<&2, JEv>, left: Nat) -> Maybe<&2, Wait>:
  match es:
    case Nil{}:
      match left:
        case 0n:
          Some{Detached{}}
        case 1n+l:
          None{}
    case e <> rest:
      match e:
        case Out{n}:
          match left:
            case 0n:
              Some{Detached{}}
            case 1n+l:
              wait(rest, 1n+l)
        case Quit{c}:
          match left:
            case 0n:
              Some{Detached{}}
            case 1n+l:
              Some{Settled{Exited{c}}}
        case Kill{}:
          match left:
            case 0n:
              Some{Detached{}}
            case 1n+l:
              Some{Settled{Killed{}}}
        case Tick{}:
          match left:
            case 0n:
              Some{Detached{}}
            case 1n+l:
              wait(rest, l)

def ticks(es: List<&2, JEv>) -> Nat:
  match es:
    case Nil{}:
      0n
    case e <> rest:
      match e:
        case Out{n}:
          ticks(rest)
        case Quit{c}:
          ticks(rest)
        case Kill{}:
          ticks(rest)
        case Tick{}:
          1n+ticks(rest)

# The job table at a rewind
# -------------------------
# A job is a node of the session tree (bend/tree.bend). A rewind stops
# every running job that the target tree does not hold.

type Slot is Data:
  Slot{id: Nat, running: Bool}

def Slot.id(s: Slot) -> Nat:
  match s:
    case Slot{i, r}:
      i

def Slot.running(s: Slot) -> Bool:
  match s:
    case Slot{i, r}:
      r

def elem(xs: List<&2, Nat>, +x: Nat) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case y <> rest:
      Bool.or(Nat.is_eq(y, x), elem(rest, x))

# a slot after a rewind to a tree that holds the jobs `keep`
def stop.at(held: Bool, s: Slot) -> Slot:
  match held:
    case True{}:
      s
    case False{}:
      match s:
        case Slot{i, r}:
          Slot{i, False{}}

# every slot after a rewind to a tree that holds the jobs `keep`
def rewind(js: List<&2, Slot>, +keep: List<&2, Nat>) -> List<&2, Slot>:
  match js:
    case Nil{}:
      Nil{}
    case +s <> rest:
      stop.at(elem(keep, Slot.id(s)), s) <> rewind(rest, keep)

# every running slot of js is one of keep
def running_in(js: List<&2, Slot>, +keep: List<&2, Nat>) -> Bool:
  match js:
    case Nil{}:
      True{}
    case +s <> rest:
      Bool.and(Bool.or(Bool.not(Slot.running(s)), elem(keep, Slot.id(s))), running_in(rest, keep))

def b.eq(a: Bool, b: Bool) -> Bool:
  match a b:
    case True{} True{}:
      True{}
    case True{} False{}:
      False{}
    case False{} True{}:
      False{}
    case False{} False{}:
      True{}

# every slot of js that keep holds is as it was in ks
def kept(js: List<&2, Slot>, ks: List<&2, Slot>, +keep: List<&2, Nat>) -> Bool:
  match js ks:
    case Nil{} Nil{}:
      True{}
    case Nil{} k <> kr:
      False{}
    case j <> jr Nil{}:
      False{}
    case +j <> jr +k <> kr:
      Bool.and(Bool.or(Bool.not(elem(keep, Slot.id(j))), Bool.and(Nat.is_eq(Slot.id(j), Slot.id(k)), b.eq(Slot.running(j), Slot.running(k)))), kept(jr, kr, keep))

# The rewind the Rust table runs
# ------------------------------
# The Rust table (JobTable::rewind_to) knows of each job whether it runs
# and `after`: the commit of the last entry the table saw when the job
# started (None: no entry since the session opened). A rewind to the
# session just after its target entry knows that entry's commit (None: no
# target, or an entry the table did not see, committed before the session
# opened, so before every job). The target tree holds a job exactly when
# the job started before the target entry was committed; the rewind sends
# the kill to every other running job (ffi_job_rewind).

type Seen is Data:
  Seen{running: Bool, after: Maybe<&2, Nat>}

# the tree just after the entry committed at target holds the job that
# started after the commit `after`
def held(target: Maybe<&2, Nat>, after: Maybe<&2, Nat>) -> Bool:
  match target:
    case None{}:
      False{}
    case Some{t}:
      match after:
        case None{}:
          True{}
        case Some{a}:
          Nat.is_lt(a, t)

# a rewind to target sends the kill to a job that runs and that the
# target tree does not hold
def kill.of(target: Maybe<&2, Nat>, s: Seen) -> Bool:
  match s:
    case Seen{r, a}:
      Bool.and(r, Bool.not(held(target, a)))

# the kill a rewind to target sends each job of js, in order
def kills(js: List<&2, Seen>, +target: Maybe<&2, Nat>) -> List<&2, Bool>:
  match js:
    case Nil{}:
      Nil{}
    case s <> rest:
      kill.of(target, s) <> kills(rest, target)

# A blocking call, poll by poll
# -----------------------------
# The Rust wait (wait_until) is polled. At each poll it knows whether its
# deadline passed (`due`) and whether the job's end is ready, and decides
# (ffi_job_wait): a passed deadline detaches, even when the end is ready;
# else a ready end settles; else the call waits for the next poll.

type Turn is Data:
  Waits{}
  Settles{}
  Detaches{}

def poll(due: Bool, ready: Bool) -> Turn:
  match due:
    case True{}:
      Detaches{}
    case False{}:
      match ready:
        case True{}:
          Settles{}
        case False{}:
          Waits{}
