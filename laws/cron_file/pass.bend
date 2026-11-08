# eukhe: the laws of area cron_file: the passes (the store's passes over
# the jobs file, bend/cron_file.bend, each pinned to its spec)
#
# The cron store (crates/eukhe-core/src/cron/store/state.rs, jobs.rs)
# reads the jobs file under its lock and asks the entry
# bend/ffi_cron_file.bend (bend/cron_file.bend) what a pass does to every
# record it read: a claim pass (which jobs it claims, one new claim
# record per claimed job), a recovery (which claim records it clears) and
# the finish step of a dispatch (which claim record goes, which job counts
# the result). It asks bend/ffi_cron.bend (CS.open) whether a corrupt
# file is moved aside. The specs below state each pass; the wire laws pin
# the entry to them; the refines laws tie each pass, applied to the file
# by the rules Rust follows (`*_file`: a job takes its answer, a claim
# record stays or goes as answered, a claimed job gets one claim record of
# this process, a record this build cannot read is never touched), to the
# model's `recs` (bend/cron.bend) on a clock of any unit u, job by job.


import Base
import ../../bend/cron.bend as Cr
import ../../bend/cron_store.bend as CS
import ../../bend/cron_file.bend as CF
import ../cron_store.bend as CronStore

# The passes
# ----------

# the claim record names the job of key k
def names_spec(+k: Nat, m: Maybe<&2, Nat>) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{x}:
      Nat.is_eq(k, x)

# some claim record names the job of key k
def claimed_spec(+k: Nat, cs: List<&2, Maybe<&2, Nat>>) -> Bool:
  match cs:
    case Nil{}:
      False{}
    case m <> t:
      Bool.or(names_spec(k, m), claimed_spec(k, t))

# a claim pass: each job takes CronStore.take_spec, claimed exactly when
# some claim record names its key
def take_all_spec(js: List<&2, CF.Slot>, +cs: List<&2, Maybe<&2, Nat>>, +due: Nat, +now: Nat) -> List<&2, CS.Took>:
  match js:
    case Nil{}:
      Nil{}
    case j <> t:
      match j:
        case CF.Slot{+key, f}:
          CronStore.take_spec(f, claimed_spec(key, cs), due, now) <> take_all_spec(t, cs, due, now)

def keep_spec(c: CF.Hold) -> Bool:
  match c:
    case CF.Held{m, w}:
      Bool.not(CronStore.clear_spec(w))
    case CF.Unheld{}:
      True{}

def keeps_spec(cs: List<&2, CF.Hold>) -> List<&2, Bool>:
  match cs:
    case Nil{}:
      Nil{}
    case c <> t:
      keep_spec(c) <> keeps_spec(t)

def cleared_spec.one(+k: Nat, c: CF.Hold) -> Bool:
  match c:
    case CF.Held{m, w}:
      Bool.and(CronStore.clear_spec(w), names_spec(k, m))
    case CF.Unheld{}:
      False{}

# some claim record that names the job of key k is cleared
def cleared_spec(+k: Nat, cs: List<&2, CF.Hold>) -> Bool:
  match cs:
    case Nil{}:
      False{}
    case c <> t:
      Bool.or(cleared_spec.one(k, c), cleared_spec(k, t))

def recover_js_spec(js: List<&2, CF.Slot>, +cs: List<&2, CF.Hold>) -> List<&2, CS.Back>:
  match js:
    case Nil{}:
      Nil{}
    case j <> t:
      match j:
        case CF.Slot{+key, f}:
          CronStore.recover_spec(f, cleared_spec(key, cs)) <> recover_js_spec(t, cs)

# a recovery: a claim record stays unless its verdict (CronStore.clear_spec)
# clears it, one this build cannot read stays; each job takes
# CronStore.recover_spec, cleared when a cleared claim record names it
def recover_all_spec(js: List<&2, CF.Slot>, +cs: List<&2, CF.Hold>) -> CF.Swept:
  CF.Swept{keeps_spec(cs), recover_js_spec(js, cs)}

def stays_spec(cs: List<&2, CF.Pin>) -> List<&2, Bool>:
  match cs:
    case Nil{}:
      Nil{}
    case c <> t:
      True{} <> stays_spec(t)

def drops_spec.pin(h: Bool, t: List<&2, CF.Pin>, rest: List<&2, Bool>) -> List<&2, Bool>:
  match h:
    case True{}:
      False{} <> stays_spec(t)
    case False{}:
      True{} <> rest

# every claim record stays but the first of the dispatch
def drops_spec(cs: List<&2, CF.Pin>) -> List<&2, Bool>:
  match cs:
    case Nil{}:
      Nil{}
    case c <> +t:
      match c:
        case CF.Pinned{m, +h}:
          drops_spec.pin(h, t, drops_spec(t))
        case CF.Unpinned{}:
          True{} <> drops_spec(t)

def hit_spec.pin(h: Bool, m: Maybe<&2, Nat>, rest: Maybe<&2, Nat>) -> Maybe<&2, Nat>:
  match h:
    case True{}:
      m
    case False{}:
      rest

# the key the first claim record of the dispatch names
def hit_spec(cs: List<&2, CF.Pin>) -> Maybe<&2, Nat>:
  match cs:
    case Nil{}:
      None{}
    case c <> t:
      match c:
        case CF.Pinned{m, h}:
          hit_spec.pin(h, m, hit_spec(t))
        case CF.Unpinned{}:
          hit_spec(t)

def untouched_spec(js: List<&2, CF.Slot>) -> List<&2, CS.Fin>:
  match js:
    case Nil{}:
      Nil{}
    case j <> t:
      CS.Untouched{} <> untouched_spec(t)

def finish_js_spec.slot(b: Bool, f: CS.Fact, t: List<&2, CF.Slot>, +u: Nat, ran: Bool, failed: Bool, +now: Nat, rest: List<&2, CS.Fin>) -> List<&2, CS.Fin>:
  match b:
    case True{}:
      CronStore.finish_spec(u, f, ran, failed, now) <> untouched_spec(t)
    case False{}:
      CS.Untouched{} <> rest

# the first job of key k takes CronStore.finish_spec, every other job is
# untouched
def finish_js_spec(js: List<&2, CF.Slot>, +k: Maybe<&2, Nat>, +u: Nat, +ran: Bool, +failed: Bool, +now: Nat) -> List<&2, CS.Fin>:
  match js:
    case Nil{}:
      Nil{}
    case j <> +t:
      match j:
        case CF.Slot{+key, f}:
          finish_js_spec.slot(names_spec(key, k), f, t, u, ran, failed, now, finish_js_spec(t, k, u, ran, failed, now))

# a finish step (on clock unit u): the first claim record of the dispatch
# goes and the first job it names takes the finish step; with no claim
# record of the dispatch nothing changes
def finish_all_spec(+u: Nat, js: List<&2, CF.Slot>, +cs: List<&2, CF.Pin>, +ran: Bool, +failed: Bool, +now: Nat) -> CF.Closed:
  CF.Closed{drops_spec(cs), finish_js_spec(js, hit_spec(cs), u, ran, failed, now)}

# Laws
# ----

# LAW cron_file_take_exact: a claim pass of the code that runs is the spec's on every file, due time and clock
# EXCLUDES: a job claimed while a claim record names it, a claimed job missed, a pass that skips or
#   reorders jobs
law cron_file_take_exact:
  for +js: List<&2, CF.Slot>
  for +cs: List<&2, Maybe<&2, Nat>>
  for +d: Nat
  for +n: Nat
  {CF.take(js, cs, d, n) == take_all_spec(js, cs, d, n) : List<&2, CS.Took>}

# LAW cron_file_recover_exact: a recovery of the code that runs is the spec's on every file
# EXCLUDES: a live claim record dropped, a cleared one kept, a record this build cannot read dropped,
#   an interrupted job missed
law cron_file_recover_exact:
  for +js: List<&2, CF.Slot>
  for +cs: List<&2, CF.Hold>
  {CF.recover(js, cs) == recover_all_spec(js, cs) : CF.Swept}

# LAW cron_file_finish_exact: a finish step of the code that runs is the spec's on every file, clock unit, result and clock
# EXCLUDES: a claim record other than the dispatch's dropped, two dropped, a job other than the one
#   the dispatch names counting the result, a result counted with no claim record of the dispatch
law cron_file_finish_exact:
  for +u: Nat
  for +js: List<&2, CF.Slot>
  for +cs: List<&2, CF.Pin>
  for +r: Bool
  for +b: Bool
  for +n: Nat
  {CF.finish(u, js, cs, r, b, n) == finish_all_spec(u, js, cs, r, b, n) : CF.Closed}

