# once (spec): exactly-once effects (area once), restated without the
# rules of bend/once.bend: the life a journal tells, what a restart does
# with an effect, and the world of one effect (its journal, its launches,
# what it does to the world, crashes, restarts) the laws run the shipped
# rules in. The laws of area once (laws/once.bend) state that the shipped
# model refines it and what the world keeps. A spec: the shipped code
# never calls it.
#
# An effect is anything the harness does to the world for a run: a tool
# call, a subagent spawn, a background job, a cron fire, a heartbeat, the
# delivery of a queued or steering message, a provider request, a file
# write. A restart is whatever makes a new process read the journal: a
# crash, a kill, a reattach, a daemon replacement or upgrade.
#
# O1: every effect has a durable journal: `intended` before anything of
#     it happens, `started` before each launch, then one end: `finished`
#     (its result is recorded), `unknown` (a restart could not tell
#     whether it ran) or `unstarted` (a restart knows it never ran). An
#     effect with no record is no effect: nothing is done, nothing is
#     reported.
# O2: an effect that may change state and whose repeat nothing drops
#     (`never`) is launched at most once when the world cannot be asked,
#     and takes hold in the world at most once however the world answers.
# O3: an effect is reported done only when it ran: its end returned, or
#     the world shows its effect. It is reported not started only when it
#     certainly never ran.
# O4: a started effect with no end on record, about which the world says
#     nothing, is reported interrupted (`unknown`) at the restart: it is
#     not launched again and not reported done. The same when its run was
#     stopped, whatever its policy.
# O5: an effect that certainly never ran (intended and never started; or
#     started, and the world shows it clean) is launched when its run
#     resumes, and reported not started when its run was stopped.
# O6: an effect ends once. An ended effect never changes and is never
#     launched, whatever records, restarts and answers of the world
#     follow.
# O7: an effect that changes nothing (`safe`) runs again after a restart.
#     An effect whose receiver drops a repeat of its idempotency key
#     (`keyed`) is sent again under the same key, at most `cap` more
#     times, then reported interrupted. Two effects never share a key.
# O8: O1-O7 hold at every crash point: after any prefix of the records of
#     a journal, and after any list of records at all (also one no run
#     writes), the restart's answer is the one above for the records read.

import Base
import ../../bend/once.bend as O

# The life a journal tells (O1, O6, O8)
# -------------------------------------

# How a journal says an effect ended
type End is Data:
  Returned{}
  Untold{}
  Unrun{}

# the end a record is, when it is one
def end_of(r: O.Rec) -> Maybe<&2, End>:
  match r:
    case O.Intended{}:
      None{}
    case O.Started{}:
      None{}
    case O.Finished{}:
      Some{Returned{}}
    case O.Unknown{}:
      Some{Untold{}}
    case O.Unstarted{}:
      Some{Unrun{}}

# e when it is an end, else the first end after it
def first_end.or(e: Maybe<&2, End>, later: Maybe<&2, End>) -> Maybe<&2, End>:
  match e:
    case None{}:
      later
    case Some{x}:
      Some{x}

# the first end on record
def first_end(j: List<&2, O.Rec>) -> Maybe<&2, End>:
  match j:
    case Nil{}:
      None{}
    case Con{r, t}:
      first_end.or(end_of(r), first_end(t))

def is_start(r: O.Rec) -> Nat:
  match r:
    case O.Intended{}:
      0n
    case O.Started{}:
      1n
    case O.Finished{}:
      0n
    case O.Unknown{}:
      0n
    case O.Unstarted{}:
      0n

# how many launches are on record
def starts(j: List<&2, O.Rec>) -> Nat:
  match j:
    case Nil{}:
      0n
    case Con{r, t}:
      Nat.add(is_start(r), starts(t))

# a journal with a record
def any(j: List<&2, O.Rec>) -> Bool:
  match j:
    case Nil{}:
      False{}
    case Con{r, t}:
      True{}

def life_spec.unlaunched(some: Bool) -> O.Life:
  match some:
    case True{}:
      O.Pending{}
    case False{}:
      O.Absent{}

# an effect with no end on record: by its launches
def life_spec.open(n: Nat, some: Bool) -> O.Life:
  match n:
    case 0n:
      life_spec.unlaunched(some)
    case 1n+k:
      O.Running{k}

def life_spec.ended(e: End) -> O.Life:
  match e:
    case Returned{}:
      O.Ran{}
    case Untold{}:
      O.Lost{}
    case Unrun{}:
      O.Void{}

def life_spec.of(e: Maybe<&2, End>, n: Nat, some: Bool) -> O.Life:
  match e:
    case None{}:
      life_spec.open(n, some)
    case Some{x}:
      life_spec.ended(x)

# the life of a journal (O1, O6): the first end on record decides it for
# good; with no end, an effect launched 1 + k times is running; with no
# launch, one with a record is pending; with no record there is no effect
def life_spec(+j: List<&2, O.Rec>) -> O.Life:
  life_spec.of(first_end(j), starts(j), any(j))

# The restart (O1-O7)
# -------------------

def more_spec(within: Bool) -> O.Verdict:
  match within:
    case True{}:
      O.Launch{}
    case False{}:
      O.Interrupt{}

# the answer O1-O7 ask of a restart, as one table
def verdict_spec(l: O.Life, s: O.Seen, m: O.Mode, p: O.Policy) -> O.Verdict:
  match l:
    case O.Absent{}:
      O.Skip{}
    case O.Pending{}:
      match m:
        case O.Resume{}:
          O.Launch{}
        case O.Stop{}:
          O.Abandon{}
    case O.Running{again}:
      match s m p:
        case O.Landed{} x y:
          O.Adopt{}
        case O.Clean{} O.Resume{} y:
          O.Launch{}
        case O.Clean{} O.Stop{} y:
          O.Abandon{}
        case O.Dark{} O.Stop{} y:
          O.Interrupt{}
        case O.Dark{} O.Resume{} O.Never{}:
          O.Interrupt{}
        case O.Dark{} O.Resume{} O.Safe{}:
          O.Launch{}
        case O.Dark{} O.Resume{} O.Keyed{cap}:
          more_spec(Nat.is_lt(again, cap))
    case O.Ran{}:
      O.Settled{}
    case O.Lost{}:
      O.Settled{}
    case O.Void{}:
      O.Settled{}

# The world of one effect (O2-O7)
# -------------------------------
# The run journals the effect intended; the runtime comes to it (a first
# run, or a restart: a resume or a stop of its run) and does what the
# restart's verdict says, never while a launch of it is in flight; a
# launch in flight takes hold in the world at some point, or never; its
# end journals finished; a crash ends what ran in memory and keeps the
# journal and the world. At a restart the world can be asked (look) or
# not; asked, it tells the truth: landed when the effect ever took hold,
# clean when it never did (the launcher is dead: it never will).

# What happens to one effect
type Ev is Data:
  Mean{}                       # the run journals it intended
  Tick{m: O.Mode, look: Bool}  # the runtime comes to it: a run of mode m; look: the world can be asked
  Land{}                       # the launch in flight takes hold in the world
  End{}                        # the launch in flight returns: finished is journaled
  Crash{}                      # the process dies

# The effect and the world: its life as journaled; live: a launch is in
# flight; hit: that launch took hold; launches made; lands: times it took
# hold; ends journaled; late: launches of an ended effect
type World is Data:
  Wd{l: O.Life, live: Bool, hit: Bool, launches: Nat, lands: Nat, ends: Nat, late: Nat}

def w0() -> World:
  Wd{O.Absent{}, False{}, False{}, 0n, 0n, 0n, 0n}

def seen.truth(lands: Nat) -> O.Seen:
  match lands:
    case 0n:
      O.Clean{}
    case 1n+k:
      O.Landed{}

# what the world shows at a restart: nothing when it cannot be asked,
# else the truth
def seen(look: Bool, lands: Nat) -> O.Seen:
  match look:
    case True{}:
      seen.truth(lands)
    case False{}:
      O.Dark{}

# an ended effect
def settled(l: O.Life) -> Bool:
  match l:
    case O.Absent{}:
      False{}
    case O.Pending{}:
      False{}
    case O.Running{again}:
      False{}
    case O.Ran{}:
      True{}
    case O.Lost{}:
      True{}
    case O.Void{}:
      True{}

# one more late launch when the launched effect had ended
def late_add(ended: Bool, late: Nat) -> Nat:
  match ended:
    case True{}:
      1n+late
    case False{}:
      late

def dim.ev(e: Ev) -> Ev:
  match e:
    case Mean{}:
      Mean{}
    case Tick{m, look}:
      Tick{m, False{}}
    case Land{}:
      Land{}
    case End{}:
      End{}
    case Crash{}:
      Crash{}

# the history es in a world that can never be asked
def dim(es: List<&2, Ev>) -> List<&2, Ev>:
  match es:
    case Nil{}:
      Nil{}
    case Con{e, t}:
      dim.ev(e) <> dim(t)

def life(w: World) -> O.Life:
  match w:
    case Wd{l, live, hit, n, k, e, x}:
      l

def launches(w: World) -> Nat:
  match w:
    case Wd{l, live, hit, n, k, e, x}:
      n

def lands(w: World) -> Nat:
  match w:
    case Wd{l, live, hit, n, k, e, x}:
      k

def ends(w: World) -> Nat:
  match w:
    case Wd{l, live, hit, n, k, e, x}:
      e

def late(w: World) -> Nat:
  match w:
    case Wd{l, live, hit, n, k, e, x}:
      x

# the effect is reported done
def is_ran(l: O.Life) -> Bool:
  match l:
    case O.Absent{}:
      False{}
    case O.Pending{}:
      False{}
    case O.Running{again}:
      False{}
    case O.Ran{}:
      True{}
    case O.Lost{}:
      False{}
    case O.Void{}:
      False{}

# the effect is reported not started
def is_void(l: O.Life) -> Bool:
  match l:
    case O.Absent{}:
      False{}
    case O.Pending{}:
      False{}
    case O.Running{again}:
      False{}
    case O.Ran{}:
      False{}
    case O.Lost{}:
      False{}
    case O.Void{}:
      True{}
