# eukhe: the laws of area cron_file: each pass of laws/cron_file/pass.bend,
# applied to the file by the rules Rust follows, is the model's `recs`
# (bend/cron.bend), job by job; a corrupt file is moved aside as the model
# heals it; no two job records of a reachable file share an id

import Base
import ../../bend/cron.bend as Cr
import ../../bend/cron_store.bend as CS
import ../../bend/cron_file.bend as CF
import ../cron.bend as Cron
import ../cron_store.bend as CronStore
import ./pass.bend as CronFile

# The file as the store holds it
# ------------------------------
# A model file (bend/cron.bend: its records rs, its claim records this
# build cannot read rd) on a clock of unit u, as the store reads it: each
# job record with its id as its key, each claim on record as a claim
# record naming the job's id (one per job with a claim, in the jobs'
# order), each record this build cannot read. A pass's answer applied to
# it is the file Rust writes.

# a job record: a job (its id, status, next run, failures in a row), or a
# record this build cannot read
type FRow is Data:
  FJob{i: Nat, st: Cr.Status, n: CS.Next, k: Nat}
  FRaw{t: Nat}

# a claim record: the id of the job it names, its claim (times in units u)
type FClaim is Data:
  FClaim{i: Nat, cl: Cr.Claim}

# a file: its job records, the claim records read, the claim records this
# build cannot read
type FFile is Data:
  FFile{rows: List<&2, FRow>, marks: List<&2, FClaim>, raws: List<&2, Nat>}

def id_of(j: Cr.Job) -> Nat:
  match j:
    case Cr.Job{i, s, st, nx, k, cl, rs, ss, h}:
      i

def row_of(j: Cr.Job, +u: Nat) -> FRow:
  match j:
    case Cr.Job{i, s, st, nx, k, cl, rs, ss, h}:
      FJob{i, st, CronStore.next_of_spec(Cron.scale_opt(nx, u)), k}

def rows_of(rs: List<&2, Cr.Rec>, +u: Nat) -> List<&2, FRow>:
  match rs:
    case Nil{}:
      Nil{}
    case r <> t:
      match r:
        case Cr.Known{j}:
          row_of(j, u) <> rows_of(t, u)
        case Cr.Raw{x}:
          FRaw{x} <> rows_of(t, u)

def marks_one(i: Nat, cl: Maybe<&2, Cr.Claim>, +u: Nat, rest: List<&2, FClaim>) -> List<&2, FClaim>:
  match cl:
    case None{}:
      rest
    case Some{x}:
      match x:
        case Cr.Claim{o, w}:
          FClaim{i, Cr.Claim{Nat.mul(o, u), w}} <> rest

def marks_of(rs: List<&2, Cr.Rec>, +u: Nat) -> List<&2, FClaim>:
  match rs:
    case Nil{}:
      Nil{}
    case r <> t:
      match r:
        case Cr.Known{j}:
          match j:
            case Cr.Job{i, s, st, nx, k, cl, ru, ss, h}:
              marks_one(i, cl, u, marks_of(t, u))
        case Cr.Raw{x}:
          marks_of(t, u)

def file_of(rs: List<&2, Cr.Rec>, rd: List<&2, Nat>, +u: Nat) -> FFile:
  +rs2 = rs
  FFile{rows_of(rs2, u), marks_of(rs2, u), rd}

# the job records Rust hands: key = id
def slots_of(rs: List<&2, Cr.Rec>, +u: Nat) -> List<&2, CF.Slot>:
  match rs:
    case Nil{}:
      Nil{}
    case r <> t:
      match r:
        case Cr.Known{+j}:
          CF.Slot{id_of(j), Cron.fact_of(j, u)} <> slots_of(t, u)
        case Cr.Raw{x}:
          slots_of(t, u)

def keys_one(i: Nat, cl: Maybe<&2, Cr.Claim>, rest: List<&2, Maybe<&2, Nat>>) -> List<&2, Maybe<&2, Nat>>:
  match cl:
    case None{}:
      rest
    case Some{x}:
      Some{i} <> rest

# the key each claim record names, for a claim pass
def keys_of(rs: List<&2, Cr.Rec>) -> List<&2, Maybe<&2, Nat>>:
  match rs:
    case Nil{}:
      Nil{}
    case r <> t:
      match r:
        case Cr.Known{j}:
          match j:
            case Cr.Job{i, s, st, nx, k, cl, ru, ss, h}:
              keys_one(i, cl, keys_of(t))
        case Cr.Raw{x}:
          keys_of(t)

def holds_one(i: Nat, cl: Maybe<&2, Cr.Claim>, +p: Nat, ru: List<&2, Nat>, +dead: List<&2, Nat>, rest: List<&2, CF.Hold>) -> List<&2, CF.Hold>:
  match cl:
    case None{}:
      rest
    case Some{x}:
      match x:
        case Cr.Claim{o, +w}:
          CF.Held{Some{i}, Cron.who_of.pick(Nat.is_eq(w, p), p, w, ru, dead)} <> rest

# the claim records read, for a recovery of p with the dead processes dead
def holds_of(+p: Nat, +dead: List<&2, Nat>, rs: List<&2, Cr.Rec>) -> List<&2, CF.Hold>:
  match rs:
    case Nil{}:
      Nil{}
    case r <> t:
      match r:
        case Cr.Known{j}:
          match j:
            case Cr.Job{i, s, st, nx, k, cl, ru, ss, h}:
              holds_one(i, cl, p, ru, dead, holds_of(p, dead, t))
        case Cr.Raw{x}:
          holds_of(p, dead, t)

def unheld(rd: List<&2, Nat>) -> List<&2, CF.Hold>:
  match rd:
    case Nil{}:
      Nil{}
    case x <> t:
      CF.Unheld{} <> unheld(t)

def pins_one(+i: Nat, cl: Maybe<&2, Cr.Claim>, +p: Nat, +ji: Nat, ru: List<&2, Nat>, rest: List<&2, CF.Pin>) -> List<&2, CF.Pin>:
  match cl:
    case None{}:
      rest
    case Some{x}:
      match x:
        case Cr.Claim{o, w}:
          CF.Pinned{Some{i}, Bool.and(Nat.is_eq(i, ji), Bool.and(Nat.is_eq(w, p), Cr.has(p, ru)))} <> rest

# the claim records read, for the finish step of p's run of job ji: the
# dispatch is the claim of job ji that p holds and runs
def pins_of(+p: Nat, +ji: Nat, rs: List<&2, Cr.Rec>) -> List<&2, CF.Pin>:
  match rs:
    case Nil{}:
      Nil{}
    case r <> t:
      match r:
        case Cr.Known{j}:
          match j:
            case Cr.Job{i, s, st, nx, k, cl, ru, ss, h}:
              pins_one(i, cl, p, ji, ru, pins_of(p, ji, t))
        case Cr.Raw{x}:
          pins_of(p, ji, t)

def unpinned(rd: List<&2, Nat>) -> List<&2, CF.Pin>:
  match rd:
    case Nil{}:
      Nil{}
    case x <> t:
      CF.Unpinned{} <> unpinned(t)

# Answers, applied

def took_row(t: CS.Took, j: Cr.Job, +u: Nat) -> FRow:
  match t:
    case CS.Keep{}:
      row_of(j, u)
    case CS.Roll{n}:
      match j:
        case Cr.Job{i, s, st, nx, k, cl, rs, ss, h}:
          FJob{i, st, n, k}
    case CS.Claimed{n}:
      match j:
        case Cr.Job{i, s, st, nx, k, cl, rs, ss, h}:
          FJob{i, st, n, k}

# the rows after a claim pass: each job takes its answer in turn (a job
# with no answer left stays)
def take_rows(rs: List<&2, Cr.Rec>, ts: List<&2, CS.Took>, +u: Nat) -> List<&2, FRow>:
  match rs:
    case Nil{}:
      Nil{}
    case r <> t:
      match r:
        case Cr.Raw{x}:
          FRaw{x} <> take_rows(t, ts, u)
        case Cr.Known{j}:
          match ts:
            case Nil{}:
              row_of(j, u) <> take_rows(t, Nil{}, u)
            case a <> rest:
              took_row(a, j, u) <> take_rows(t, rest, u)

def took_new(t: CS.Took, j: Cr.Job, +p: Nat, +u: Nat, rest: List<&2, FClaim>) -> List<&2, FClaim>:
  match t:
    case CS.Keep{}:
      rest
    case CS.Roll{n}:
      rest
    case CS.Claimed{n}:
      match j:
        case Cr.Job{i, s, st, nx, k, cl, rs, ss, h}:
          match nx:
            case None{}:
              rest
            case Some{o}:
              FClaim{i, Cr.Claim{Nat.mul(o, u), p}} <> rest

# the claim records a claim pass of p adds: one per claimed job, its
# occurrence the next run it was due at
def take_news(rs: List<&2, Cr.Rec>, ts: List<&2, CS.Took>, +p: Nat, +u: Nat) -> List<&2, FClaim>:
  match rs:
    case Nil{}:
      Nil{}
    case r <> t:
      match r:
        case Cr.Raw{x}:
          take_news(t, ts, p, u)
        case Cr.Known{j}:
          match ts:
            case Nil{}:
              take_news(t, Nil{}, p, u)
            case a <> rest:
              took_new(a, j, p, u, take_news(t, rest, p, u))

# a claim pass of p, applied: the claim records read stay, the new ones
# follow them
def take_file(+ts: List<&2, CS.Took>, +rs: List<&2, Cr.Rec>, rd: List<&2, Nat>, +p: Nat, +u: Nat) -> FFile:
  FFile{take_rows(rs, ts, u), List.append(&2, FClaim, marks_of(rs, u), take_news(rs, ts, p, u)), rd}

def back_row(b: CS.Back, j: Cr.Job, +u: Nat) -> FRow:
  match b:
    case CS.Kept{}:
      row_of(j, u)
    case CS.Interrupted{st2, m}:
      match j:
        case Cr.Job{i, s, st, nx, k, cl, rs, ss, h}:
          FJob{i, st2, CronStore.next_of_spec(m), k}

def recover_rows(rs: List<&2, Cr.Rec>, bs: List<&2, CS.Back>, +u: Nat) -> List<&2, FRow>:
  match rs:
    case Nil{}:
      Nil{}
    case r <> t:
      match r:
        case Cr.Raw{x}:
          FRaw{x} <> recover_rows(t, bs, u)
        case Cr.Known{j}:
          match bs:
            case Nil{}:
              row_of(j, u) <> recover_rows(t, Nil{}, u)
            case b <> rest:
              back_row(b, j, u) <> recover_rows(t, rest, u)

def fin_row(x: CS.Fin, j: Cr.Job, +u: Nat) -> FRow:
  match x:
    case CS.Untouched{}:
      row_of(j, u)
    case CS.Ran{st2, n, k2}:
      match j:
        case Cr.Job{i, s, st, nx, k, cl, rs, ss, h}:
          FJob{i, st2, n, k2}
    case CS.Skipped{st2, n, k2}:
      match j:
        case Cr.Job{i, s, st, nx, k, cl, rs, ss, h}:
          FJob{i, st2, n, k2}

def finish_rows(rs: List<&2, Cr.Rec>, fs: List<&2, CS.Fin>, +u: Nat) -> List<&2, FRow>:
  match rs:
    case Nil{}:
      Nil{}
    case r <> t:
      match r:
        case Cr.Raw{x}:
          FRaw{x} <> finish_rows(t, fs, u)
        case Cr.Known{j}:
          match fs:
            case Nil{}:
              row_of(j, u) <> finish_rows(t, Nil{}, u)
            case f <> rest:
              fin_row(f, j, u) <> finish_rows(t, rest, u)

def keep.pick(b: Bool, x: FClaim, rest: List<&2, FClaim>) -> List<&2, FClaim>:
  match b:
    case True{}:
      x <> rest
    case False{}:
      rest

# the claim records read that stay: each takes its answer in turn (one
# with no answer left stays)
def select_marks(ms: List<&2, FClaim>, ks: List<&2, Bool>) -> List<&2, FClaim>:
  match ms:
    case Nil{}:
      Nil{}
    case m <> t:
      match ks:
        case Nil{}:
          m <> select_marks(t, Nil{})
        case k <> rest:
          keep.pick(k, m, select_marks(t, rest))

# the answers left after the claim records read
def after_marks(ms: List<&2, FClaim>, ks: List<&2, Bool>) -> List<&2, Bool>:
  match ms:
    case Nil{}:
      ks
    case m <> t:
      match ks:
        case Nil{}:
          Nil{}
        case k <> rest:
          after_marks(t, rest)

def keep_raw.pick(b: Bool, x: Nat, rest: List<&2, Nat>) -> List<&2, Nat>:
  match b:
    case True{}:
      x <> rest
    case False{}:
      rest

# the claim records this build cannot read that stay
def select_raws(rd: List<&2, Nat>, ks: List<&2, Bool>) -> List<&2, Nat>:
  match rd:
    case Nil{}:
      Nil{}
    case x <> t:
      match ks:
        case Nil{}:
          x <> select_raws(t, Nil{})
        case k <> rest:
          keep_raw.pick(k, x, select_raws(t, rest))

# a recovery, applied
def recover_file(x: CF.Swept, +rs: List<&2, Cr.Rec>, rd: List<&2, Nat>, +u: Nat) -> FFile:
  match x:
    case CF.Swept{+ks, bs}:
      FFile{recover_rows(rs, bs, u), select_marks(marks_of(rs, u), ks), select_raws(rd, after_marks(marks_of(rs, u), ks))}

# a finish step, applied
def finish_file(x: CF.Closed, +rs: List<&2, Cr.Rec>, rd: List<&2, Nat>, +u: Nat) -> FFile:
  match x:
    case CF.Closed{+ks, fs}:
      FFile{finish_rows(rs, fs, u), select_marks(marks_of(rs, u), ks), select_raws(rd, after_marks(marks_of(rs, u), ks))}

# What the laws compare, job by job

def row_at.pick(b: Bool, r: FRow, rest: Maybe<&2, FRow>) -> Maybe<&2, FRow>:
  match b:
    case True{}:
      Some{r}
    case False{}:
      rest

# the first job record of id x
def row_at(+x: Nat, rows: List<&2, FRow>) -> Maybe<&2, FRow>:
  match rows:
    case Nil{}:
      None{}
    case r <> t:
      match r:
        case FJob{+i, st, n, k}:
          row_at.pick(Nat.is_eq(i, x), FJob{i, st, n, k}, row_at(x, t))
        case FRaw{y}:
          row_at(x, t)

def marks_at.pick(b: Bool, cl: Cr.Claim, rest: List<&2, Cr.Claim>) -> List<&2, Cr.Claim>:
  match b:
    case True{}:
      cl <> rest
    case False{}:
      rest

# the claims of the claim records that name the job of id x, in order
def marks_at(+x: Nat, ms: List<&2, FClaim>) -> List<&2, Cr.Claim>:
  match ms:
    case Nil{}:
      Nil{}
    case m <> t:
      match m:
        case FClaim{i, cl}:
          marks_at.pick(Nat.is_eq(i, x), cl, marks_at(x, t))

# the job records this build cannot read, in order
def raw_rows(rows: List<&2, FRow>) -> List<&2, Nat>:
  match rows:
    case Nil{}:
      Nil{}
    case r <> t:
      match r:
        case FJob{i, st, n, k}:
          raw_rows(t)
        case FRaw{y}:
          y <> raw_rows(t)

def Obs() -> Type:
  Maybe<&2, FRow> & (List<&2, Cr.Claim> & (List<&2, Nat> & List<&2, Nat>))

# what a file holds of the job of id x: its record, the claim records
# naming it; and the records this build cannot read
def obs(+x: Nat, f: FFile) -> Obs():
  match f:
    case FFile{+rows, ms, rd}:
      (row_at(x, rows), (marks_at(x, ms), (raw_rows(rows), rd)))

def has_id(+x: Nat, rs: List<&2, Cr.Rec>) -> Bool:
  match rs:
    case Nil{}:
      False{}
    case r <> t:
      match r:
        case Cr.Known{j}:
          Bool.or(Nat.is_eq(id_of(j), x), has_id(x, t))
        case Cr.Raw{y}:
          has_id(x, t)

# no two job records of rs share an id
def distinct(rs: List<&2, Cr.Rec>) -> Bool:
  match rs:
    case Nil{}:
      True{}
    case r <> +t:
      match r:
        case Cr.Known{+j}:
          Bool.and(Bool.not(has_id(id_of(j), t)), distinct(t))
        case Cr.Raw{y}:
          distinct(t)

# what an update of a corrupt file does to the files moved aside: the
# corrupt file goes first when the decision moves it
def aside_after(bad: Maybe<&2, Nat>, go: Bool, aside: List<&2, Nat>) -> List<&2, Nat>:
  match bad:
    case None{}:
      aside
    case Some{t}:
      match go:
        case True{}:
          t <> aside
        case False{}:
          aside

# an update: a new job, a claim pass, a recovery, a finish step
def is_update(e: Cr.Ev) -> Bool:
  match e:
    case Cr.Create{p, s}:
      True{}
    case Cr.Take{p}:
      True{}
    case Cr.Recover{p}:
      True{}
    case Cr.Finish{p, i, o}:
      True{}
    case Cr.Abort{p}:
      False{}
    case Cr.Die{p}:
      False{}
    case Cr.Cancel{p, i}:
      False{}
    case Cr.Resume{p, i}:
      False{}
    case Cr.Tick{d}:
      False{}
    case Cr.RawJob{t}:
      False{}
    case Cr.RawClaim{t}:
      False{}
    case Cr.Corrupt{t}:
      False{}
    case Cr.Pause{p, i}:
      False{}
    case Cr.Stop{p, i}:
      False{}
    case Cr.Delete{p, i}:
      False{}
    case Cr.Edit{p, i, k}:
      False{}

# Laws
# ----

# LAW cron_file_take_refines: on a clock of any unit u, a claim pass of p over a file whose job ids are distinct (cron_ids_distinct: every file the model reaches), applied, holds for every job id x the model's claim step of p (Cr.recs of Take): the same record (status, next run, failures in a row), the same claim records naming x (so one new claim record per claimed job, of p, at its due occurrence), the same records this build cannot read
# EXCLUDES: a job claimed twice or by two records, a due job with a claim record claimed again, a due
#   unclaimed job left unclaimed, a claim record dropped or added for another job, an unread record
#   lost
law cron_file_take_refines:
  for +v: Nat
  for +p: Nat
  for +c: Nat
  for +x: Nat
  for +dead: List<&2, Nat>
  for +rs: List<&2, Cr.Rec>
  for +rd: List<&2, Nat>
  for ok: {distinct(rs) == True{} : Bool}
  {obs(x, take_file(CronFile.take_all_spec(slots_of(rs, 1n+v), keys_of(rs), Nat.mul(c, 1n+v), Nat.mul(c, 1n+v)), rs, rd, p, 1n+v)) == obs(x, file_of(Cr.recs(Cr.Take{p}, c, dead, rs), rd, 1n+v)) : Obs()}

# LAW cron_file_recover_refines: on a clock of any unit u, a recovery of a live process p (each claim record's verdict from whose it is, whether p still runs it and whether its owner is dead) over a file whose job ids are distinct, applied, holds for every job id x the model's recovery step of p (Cr.recs of Recover), and keeps every claim record this build cannot read
# EXCLUDES: a live claim of another process cleared, a dead one's or an own unwound one kept, a
#   cleared claim whose job does not record the interruption, an unread claim record dropped
law cron_file_recover_refines:
  for +v: Nat
  for +p: Nat
  for +c: Nat
  for +x: Nat
  for +dead: List<&2, Nat>
  for +rs: List<&2, Cr.Rec>
  for +rd: List<&2, Nat>
  for ok: {distinct(rs) == True{} : Bool}
  for alive: {Cr.has(p, dead) == False{} : Bool}
  {obs(x, recover_file(CronFile.recover_all_spec(slots_of(rs, 1n+v), List.append(&2, CF.Hold, holds_of(p, dead, rs), unheld(rd))), rs, rd, 1n+v)) == obs(x, file_of(Cr.recs(Cr.Recover{p}, c, dead, rs), rd, 1n+v)) : Obs()}

# LAW cron_file_finish_refines: on a clock of any unit u, the finish step of p's run of job ji (the dispatch: the claim record of ji that p holds and runs) over a file whose job ids are distinct, applied, holds for every job id x the model's finish step (Cr.recs of Finish): with no such claim record (cleared by another process, or never p's) nothing changes
# EXCLUDES: a result counted by a job whose claim p no longer holds, another job's claim record
#   dropped, the dispatch's claim record kept, an unread claim record dropped
law cron_file_finish_refines:
  for +v: Nat
  for +p: Nat
  for +c: Nat
  for +ji: Nat
  for +o: Cr.Out
  for +x: Nat
  for +dead: List<&2, Nat>
  for +rs: List<&2, Cr.Rec>
  for +rd: List<&2, Nat>
  for ok: {distinct(rs) == True{} : Bool}
  {obs(x, finish_file(CronFile.finish_all_spec(1n+v, slots_of(rs, 1n+v), List.append(&2, CF.Pin, pins_of(p, ji, rs), unpinned(rd)), Cron.ran_of(o), Cron.failed_of(o), Nat.mul(c, 1n+v)), rs, rd, 1n+v)) == obs(x, file_of(Cr.recs(Cr.Finish{p, ji, o}, c, dead, rs), rd, 1n+v)) : Obs()}

# LAW cron_open_refines: an update by a live process (a new job, a claim pass, a recovery, a finish step) of a file it finds corrupt moves it aside as the decision on a corrupt file read for an update says, exactly as the model's step does; the file is read afterwards
# EXCLUDES: a corrupt file written over, lost, or moved aside twice; a file that stays corrupt after
#   an update
law cron_open_refines:
  for +s: Cr.S
  for +e: Cr.Ev
  for +p: Nat
  for by: {Cr.Ev.by(e) == Some{p} : Maybe<&2, Nat>}
  for alive: {Cr.has(p, Cr.S.dead(s)) == False{} : Bool}
  for up: {is_update(e) == True{} : Bool}
  {aside_after(Cr.S.bad(s), CronStore.open_spec(True{}), Cr.S.aside(s)) == Cr.S.aside(Cr.step(s, e)) : List<&2, Nat>} & {Cr.S.bad(Cr.step(s, e)) == None{} : Maybe<&2, Nat>}

# LAW cron_ids_distinct: after any events, no two job records of the file share an id (a new job takes a fresh id)
# EXCLUDES: a new job reusing an id; the premise of the cron_file_*_refines laws failing on a file
#   the model reaches
law cron_ids_distinct:
  for +evs: List<&2, Cr.Ev>
  {distinct(Cr.S.recs(Cr.run(evs))) == True{} : Bool}

