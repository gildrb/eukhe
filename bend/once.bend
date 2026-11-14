# once: the life of one effect across restarts, and what a restart does
# with it (exactly-once effects). An effect is anything the harness does
# to the world for a run: a tool call, a subagent spawn, a background job,
# a cron fire, a heartbeat, the delivery of a queued or steering message,
# a provider request, a file write. Rust journals each effect durably (a
# record is acknowledged only once it survives a crash):
#
#   intended   before anything of the effect happens
#   started    before each launch of the effect
#   finished   after the effect ended, with its result
#   unknown    a restart could not tell whether it ran: it is reported
#              interrupted
#   unstarted  a restart knows it never ran: it is reported not started
#
# and asks this model at every restart of a run (a resume, or a stop of
# the run) what to do with each effect whose journal it reads. Rust keeps
# the journal (the session's commit log, the cron jobs file), the launch,
# and the look at the world (`Seen`); the model decides. It runs as the
# compiled core by bend/ffi_once.bend (eukhe-bend rules/once.rs).
# spec/once/life.bend restates the rule; laws/once.bend pins it. Pure: no
# IO, no @unsafe.

import Base
import ./wire.bend as W

# How the run of an effect comes back after a restart
type Mode is Data:
  Resume{}  # the run goes on
  Stop{}    # the run was ended: nothing of it starts any more

# What the target of a keyed effect declares of a repeat of its
# idempotency key: a declaration the principal or the target's operator
# made, never one a model or a generic tool wrote
type Dedup is Data:
  Undeclared{}  # no such declaration, or one that drops a repeat only within a window (only the harness's own clock could tell that a relaunch falls inside it): a repeat may take hold again
  Lasting{}     # every repeat of the key is dropped, whenever it comes

# What a second launch of an effect would do
type Policy is Data:
  Never{}                    # it may change state and nothing drops a repeat: never launched twice
  Safe{}                     # it changes nothing: it may run again
  Keyed{d: Dedup, cap: Nat}  # every launch carries its idempotency key: sent again under it only when its target declares d lasting, at most cap more times

# What the world shows of a started effect at a restart
type Seen is Data:
  Dark{}    # nothing can be asked, or the answer is unclear
  Landed{}  # its effect is there (the file holds the new bytes, the receiver knows the key)
  Clean{}   # its effect is certainly not there, and its launcher is dead: it can never land

# A record of an effect's journal
type Rec is Data:
  Intended{}
  Started{}
  Finished{}
  Unknown{}
  Unstarted{}

# An effect as its journal tells it
type Life is Data:
  Absent{}             # no record
  Pending{}            # intended, never launched
  Running{again: Nat}  # launched 1 + again times, no end on record
  Ran{}               # finished
  Unsure{}               # settled unknown
  Void{}               # settled unstarted

# What a restart does with an effect
type Verdict is Data:
  Skip{}       # no record of it: nothing to do
  Launch{}     # journal started, then run it (a first launch, or one more)
  Adopt{}      # journal finished: it ran; its effect in the world is its result
  Interrupt{}  # journal unknown: report it interrupted; never run it
  Abandon{}    # journal unstarted: report it not started; never run it
  Settled{}    # it ended before: report what the journal says; never run it

# The life
# --------

# a record read before any launch
def life.fresh(r: Rec) -> Life:
  match r:
    case Intended{}:
      Pending{}
    case Started{}:
      Running{0n}
    case Finished{}:
      Ran{}
    case Unknown{}:
      Unsure{}
    case Unstarted{}:
      Void{}

# a record read after 1 + again launches
def life.launched(r: Rec, again: Nat) -> Life:
  match r:
    case Intended{}:
      Running{again}
    case Started{}:
      Running{1n+again}
    case Finished{}:
      Ran{}
    case Unknown{}:
      Unsure{}
    case Unstarted{}:
      Void{}

# the life after one more record: an end stays whatever follows it
def life.step(l: Life, r: Rec) -> Life:
  match l:
    case Absent{}:
      life.fresh(r)
    case Pending{}:
      life.fresh(r)
    case Running{again}:
      life.launched(r, again)
    case Ran{}:
      Ran{}
    case Unsure{}:
      Unsure{}
    case Void{}:
      Void{}

# the life after the records j, in order, from l
def life.go(j: List<&2, Rec>, l: Life) -> Life:
  match j:
    case Nil{}:
      l
    case Con{r, t}:
      life.go(t, life.step(l, r))

# the life a journal tells
def life(j: List<&2, Rec>) -> Life:
  life.go(j, Absent{})

# The restart
# -----------

# one more send of a keyed effect sent again `again` times: while fewer
# than cap
def keyed(cap: Nat, again: Nat) -> Verdict:
  match cap:
    case 0n:
      Interrupt{}
    case 1n+c:
      match again:
        case 0n:
          Launch{}
        case 1n+a:
          keyed(c, a)

# one more send of a keyed effect sent again `again` times: only when its
# target drops every repeat of the key (lasting), and while fewer than
# cap; elapsed time never sends it again
def dedup(d: Dedup, cap: Nat, again: Nat) -> Verdict:
  match d:
    case Undeclared{}:
      Interrupt{}
    case Lasting{}:
      keyed(cap, again)

# an effect that certainly never ran: it starts when its run goes on
def unrun(m: Mode) -> Verdict:
  match m:
    case Resume{}:
      Launch{}
    case Stop{}:
      Abandon{}

# a started effect nothing can be asked about: only a run that goes on
# launches again, and only what its policy allows
def dark(m: Mode, p: Policy, again: Nat) -> Verdict:
  match m:
    case Resume{}:
      match p:
        case Never{}:
          Interrupt{}
        case Safe{}:
          Launch{}
        case Keyed{d, cap}:
          dedup(d, cap, again)
    case Stop{}:
      Interrupt{}

# a started effect with no end on record
def started(s: Seen, m: Mode, p: Policy, again: Nat) -> Verdict:
  match s:
    case Dark{}:
      dark(m, p, again)
    case Landed{}:
      Adopt{}
    case Clean{}:
      unrun(m)

# what a restart does with an effect of life l
def recover(l: Life, s: Seen, m: Mode, p: Policy) -> Verdict:
  match l:
    case Absent{}:
      Skip{}
    case Pending{}:
      unrun(m)
    case Running{again}:
      started(s, m, p, again)
    case Ran{}:
      Settled{}
    case Unsure{}:
      Settled{}
    case Void{}:
      Settled{}

# The idempotency key
# -------------------

# the key every send of one effect carries: its scope (the session), then
# its id in the scope, each spelled with its length, so two effects never
# share a key and no send of one effect has another
def key(scope: String, id: String) -> String:
  W.put_str(scope, W.put_str(id, ""))
