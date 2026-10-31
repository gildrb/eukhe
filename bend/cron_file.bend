# cron_file: the passes of the cron job store over a whole jobs file
# (`AgentCronJobStore`, crates/eukhe-core/src/cron/store/state.rs and
# jobs.rs), the code the entry bend/ffi_cron_file.bend runs: a claim pass,
# a recovery and the finish step of a dispatch. Each pass decides every
# record the store read: which jobs a claim pass claims (one new claim
# record per claimed job, on the job's key), which claim records a
# recovery or a finish step keeps, and what each job becomes (the per-job
# decisions of bend/cron_store.bend). laws/cron_file.bend ties each pass,
# applied to the file, to the model's `recs` (bend/cron.bend).
#
# Rust reads the file under its lock and hands the records it read: each
# job record as a key (equal keys: equal job ids) and its facts; each
# claim record as the key of the job it names (none: no job read has its
# id), with, for a recovery, whose it is (bend/cron_store.bend `Who`), or,
# for a finish step, whether it is the dispatch being recorded, or as a
# claim record this build cannot read. Rust applies the answers record by
# record and keeps the bytes of the job records it cannot read.

import Base
import ./cron.bend as Cr
import ./cron_store.bend as CS

# Facts
# -----

# a job record the store read: its key and its facts
type Slot is Data:
  Slot{key: Nat, f: CS.Fact}

# a claim record, for a recovery: read (the key of the job it names, whose
# it is), or one this build cannot read
type Hold is Data:
  Held{key: Maybe<&2, Nat>, w: CS.Who}
  Unheld{}

# a claim record, for a finish step: read (the key of the job it names,
# whether it is the dispatch being recorded), or one this build cannot read
type Pin is Data:
  Pinned{key: Maybe<&2, Nat>, hit: Bool}
  Unpinned{}

# what Rust asks of a file: a claim pass (the job records, the key each
# read claim record names, the time it is due by, the clock), a recovery
# (the job records, the claim records), a finish step (the job records,
# the claim records, whether the run ran and failed, the clock)
type Pass is Data:
  PassTake{js: List<&2, Slot>, cs: List<&2, Maybe<&2, Nat>>, due: Nat, now: Nat}
  PassRecover{js: List<&2, Slot>, cs: List<&2, Hold>}
  PassFinish{js: List<&2, Slot>, cs: List<&2, Pin>, ran: Bool, failed: Bool, now: Nat}

# Answers
# -------

# a recovery: whether each claim record stays, what each job becomes
type Swept is Data:
  Swept{keep: List<&2, Bool>, js: List<&2, CS.Back>}

# a finish step: whether each claim record stays, what each job becomes
type Closed is Data:
  Closed{keep: List<&2, Bool>, js: List<&2, CS.Fin>}

# Small parts
# -----------

# a claim record names the job of key k
def names(+k: Nat, m: Maybe<&2, Nat>) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{x}:
      Nat.is_eq(x, k)

# A claim pass
# ------------

# some claim record names the job of key k
def claimed(+k: Nat, cs: List<&2, Maybe<&2, Nat>>) -> Bool:
  match cs:
    case Nil{}:
      False{}
    case m <> t:
      Bool.or(names(k, m), claimed(k, t))

# each job's claim pass (CS.take), claimed when a claim record names it;
# Rust adds one claim record of this process for each job claimed
def take(js: List<&2, Slot>, +cs: List<&2, Maybe<&2, Nat>>, +due: Nat, +now: Nat) -> List<&2, CS.Took>:
  match js:
    case Nil{}:
      Nil{}
    case j <> t:
      match j:
        case Slot{+key, f}:
          CS.take(f, claimed(key, cs), due, now) <> take(t, cs, due, now)

# A recovery
# ----------

# each claim record stays unless its verdict clears it (CS.clear); one
# this build cannot read stays
def keeps(cs: List<&2, Hold>) -> List<&2, Bool>:
  match cs:
    case Nil{}:
      Nil{}
    case c <> t:
      match c:
        case Held{m, w}:
          Bool.not(CS.clear(w)) <> keeps(t)
        case Unheld{}:
          True{} <> keeps(t)

def cleared.one(+k: Nat, c: Hold) -> Bool:
  match c:
    case Held{m, w}:
      Bool.and(names(k, m), CS.clear(w))
    case Unheld{}:
      False{}

# some claim record that names the job of key k is cleared
def cleared(+k: Nat, cs: List<&2, Hold>) -> Bool:
  match cs:
    case Nil{}:
      False{}
    case c <> t:
      Bool.or(cleared.one(k, c), cleared(k, t))

def recover.js(js: List<&2, Slot>, +cs: List<&2, Hold>) -> List<&2, CS.Back>:
  match js:
    case Nil{}:
      Nil{}
    case j <> t:
      match j:
        case Slot{+key, f}:
          CS.recover(f, cleared(key, cs)) <> recover.js(t, cs)

# the claim records cleared go, and each job whose claim record was
# cleared records the interruption (CS.recover)
def recover(js: List<&2, Slot>, +cs: List<&2, Hold>) -> Swept:
  Swept{keeps(cs), recover.js(js, cs)}

# The finish step
# ---------------

def hit.pick(h: Bool, k: Maybe<&2, Nat>, rest: Maybe<&2, Nat>) -> Maybe<&2, Nat>:
  match h:
    case True{}:
      k
    case False{}:
      rest

# the key the first claim record of the dispatch names (none: no such
# record, or it names no job read)
def hit(cs: List<&2, Pin>) -> Maybe<&2, Nat>:
  match cs:
    case Nil{}:
      None{}
    case c <> t:
      match c:
        case Pinned{k, h}:
          hit.pick(h, k, hit(t))
        case Unpinned{}:
          hit(t)

# each claim record stays but the first of the dispatch (found: that one
# is already passed)
def drops(cs: List<&2, Pin>, +found: Bool) -> List<&2, Bool>:
  match cs:
    case Nil{}:
      Nil{}
    case c <> t:
      match c:
        case Pinned{k, h}:
          +d = Bool.and(h, Bool.not(found))
          Bool.not(d) <> drops(t, Bool.or(found, d))
        case Unpinned{}:
          True{} <> drops(t, found)

def finish.one(go: Bool, f: CS.Fact, +u: Nat, ran: Bool, failed: Bool, +now: Nat) -> CS.Fin:
  match go:
    case True{}:
      CS.finish(u, f, ran, failed, now)
    case False{}:
      CS.Untouched{}

def finish.rest(go: Bool, k: Maybe<&2, Nat>) -> Maybe<&2, Nat>:
  match go:
    case True{}:
      None{}
    case False{}:
      k

# the first job of key k takes the finish step (CS.finish); every other
# job is untouched
def finish.js(js: List<&2, Slot>, +k: Maybe<&2, Nat>, +u: Nat, +ran: Bool, +failed: Bool, +now: Nat) -> List<&2, CS.Fin>:
  match js:
    case Nil{}:
      Nil{}
    case j <> t:
      match j:
        case Slot{+key, f}:
          +go = names(key, k)
          finish.one(go, f, u, ran, failed, now) <> finish.js(t, finish.rest(go, k), u, ran, failed, now)

# the claim record of the dispatch goes, and the first job it names takes
# the finish step; with no claim record of the dispatch, nothing changes
def finish(+u: Nat, js: List<&2, Slot>, +cs: List<&2, Pin>, +ran: Bool, +failed: Bool, +now: Nat) -> Closed:
  Closed{drops(cs, False{}), finish.js(js, hit(cs), u, ran, failed, now)}
