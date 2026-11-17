# eukhe: the laws of area log

import Base
import ../spec/durable/log.bend as Lg
import ../bend/log.bend as Lr
import ../bend/wire.bend as Wr
import ../bend/ffi_log.bend as FLg
import ./base.bend as LawsBase

# ---- storage ----

# LAWS (D1): the durable storage of a session. Each law is an open claim
# about the models in spec/durable/log.bend and bend/staging.bend; PROOF.bend
# proves them (as Log.<law>) with the lemmas of proof/log/
# and proof/staging/.

# (D1) Storage
# ------------
# spec/README.md D1. The commit log `main.jsonl` (spec/durable/log.bend): every
# input is free: any disk (any bytes, a torn tail, no file), any commits,
# any crash point, any number of bytes not flushed that the crash keeps,
# and whether the crash drops the directory entries not flushed.

# LAW log_reads_lines: open reads exactly the complete lines, in order; a torn tail (the
# bytes after the last newline) is never read as an entry
law log_reads_lines:
  for +ls: List<&2, List<&2, Nat>>
  for +t: List<&2, Nat>
  {Lg.recover(List.append(&2, Nat, Lg.render(ls), Lg.data(t))) == ls : List<&2, List<&2, Nat>>}

# LAW log_ack_durable: a crash at any point never loses a commit: after an epoch the log
# is the log before it, then every commit it acknowledged, then maybe more
law log_ack_durable:
  for d: Lg.Disk
  for e: Lg.Epoch
  exs rest: List<&2, List<&2, Nat>>
  {Lg.Disk.log(Lg.after(d, e)) == List.append(&2, List<&2, Nat>, List.append(&2, List<&2, Nat>, Lg.Disk.log(d), Lg.acked(d, e)), rest) : List<&2, List<&2, Nat>>}

# LAW log_only_commits: after an epoch the log is the log before it, then a prefix of the
# commits it tried, in order: nothing torn, nothing out of order, nothing
# twice
law log_only_commits:
  for d: Lg.Disk
  for e: Lg.Epoch
  exs n: Nat
  {Lg.Disk.log(Lg.after(d, e)) == List.append(&2, List<&2, Nat>, Lg.Disk.log(d), List.take(&2, List<&2, Nat>, Lg.Epoch.cs(e), n)) : List<&2, List<&2, Nat>>}

# ---- log: the rules JsonlStorage runs ----

# LAWS: the rules of bend/log.bend that JsonlStorage runs through the
# compiled core (entry bend/ffi_log.bend; Rust
# crates/eukhe-bend/src/rules/log.rs, asked by eukhe-durable's
# storage/jsonl/storage.rs and eukhe-budget's ledger/file.rs): what an open
# does with a file (Lr.tail), and the plan of steps of the storage
# (Lr.Store.open, Lr.Store.commit). Rust reads the facts (a file's length
# and the index of its last newline; which directory entries it made
# durable) and does the steps; the laws below refine the model above.
# Every input is free: any file, any facts, fsync on or off, any number of
# sidecar files with any durability, any commits, any crash point.
#
# R1: an open reads exactly the complete lines of a file (Lg.recover): it
#     keeps a file whose bytes all lie in complete lines, cuts any other to
#     its complete lines, and refuses facts no file has.
# R2: with fsync, the plan of an open and of commits that touch no sidecar
#     file is the model's epoch (Lg.run) at every crash point: a crash never
#     loses an acknowledged commit, and the log only ever holds a prefix of
#     the commits.
# R3: a commit's plan is its records, then (fsync) their flushes and a
#     directory flush while a sidecar's entry is not durable, then its
#     marker, then (fsync) its flush and a directory flush while
#     main.jsonl's entry is not durable, then (a stamped storage, after
#     that directory flush) the link of the storage's stamp, then the
#     ack: nothing else, in this order; an open's plan is (fsync) the flush
#     of the parent directory, unless the storage's stamp names
#     main.jsonl: then nothing, and main.jsonl's entry is durable.
# R4: the entry answers each request Rust writes with the spelling of the
#     rule's decision, and the wire's error form to every other input; a
#     refused step keeps the stepper's state.
# R5: the budget ledger (spec/README.md B5) keeps each account file by the
#     same rules: an operation opens the file under its lock as a stamped
#     storage (kept when the file's stamp names it) and appends its
#     records as commits that touch no sidecar file. Between operations a
#     file keeps whether its entries are durable (Lg.Rest): a crash that
#     kills the process keeps a file whose entries may not be durable, and
#     a later crash that drops entries loses it. After any history of
#     operations, each of which may crash at any point and the next of
#     which opens what the crash left, from a file whose entries are
#     durable (one an earlier release left, with no stamp), the file holds
#     the log before, then each operation's acknowledged records followed
#     by maybe more, and only a prefix of each operation's records, in the
#     order of the operations.
# R6: a ledger record costs one flush once the file is stamped: every
#     record of an operation whose stamp names the file flushes the file
#     and nothing else, and an operation that acknowledged a record leaves
#     the file stamped.
# Runtime limits: the laws quantify over unbounded Nats; the runtime's Nat
#     is an immediate of at most 2^48 - 1, and the wire carries Nats up to
#     10^14 - 1 (crates/eukhe-bend/WIRE.md). That no value the rule computes
#     passes the runtime's bound on any input the wire carries is covered by
#     tests, not by the laws: rules/log.rs `an_open_of_any_size_the_wire_carries`
#     runs the compiled entry on a 128 KiB file and on files of the largest
#     length the wire carries.
# A failed step: the rules plan steps and never see one fail. A step
#     that fails stops the plan where it failed, which R2's laws cover as
#     a crash at that point (log_plan_ack_durable, log_plan_only_commits:
#     any crash point, any bytes not flushed kept or not). That JsonlStorage
#     then runs no later plan (it poisons the storage) is Rust's and is
#     covered by tests, not by the laws: eukhe-durable tests/jsonl_storage.rs
#     `poisons_after_append_failure_and_recovers_only_confirmed_state`,
#     `poisons_after_flush_failure_and_never_writes_a_marker`,
#     `poisons_after_a_directory_flush_failure_and_never_writes_a_marker`,
#     `poisons_after_main_flush_failure_and_defers_reclamation`; the
#     ledger's operation ends at the failed step with its error.

# The open of a file
# ------------------

# the index of the last newline of a file, None when it has none (Rust:
# `rposition` of b'\n'); m is that of the bytes after b
def log_last.at(b: Nat, m: Maybe<&2, Nat>) -> Maybe<&2, Nat>:
  match b:
    case 0n:
      match m:
        case None{}:
          Some{0n}
        case Some{i}:
          Some{1n+i}
    case 1n+c:
      match m:
        case None{}:
          None{}
        case Some{i}:
          Some{1n+i}

def log_last(f: List<&2, Nat>) -> Maybe<&2, Nat>:
  match f:
    case Nil{}:
      None{}
    case b <> rest:
      log_last.at(b, log_last(rest))

# what an open must do with a file that parses to the lines ls and the
# tail t: keep it when nothing follows its last newline, else cut it to the
# bytes of its lines
def log_tail_spec.of(ls: List<&2, List<&2, Nat>>, t: List<&2, Nat>) -> Lr.Tail:
  match t:
    case Nil{}:
      Lr.Whole{}
    case x <> rest:
      Lr.Torn{List.length(&2, Nat, Lg.render(ls))}

def log_tail_spec.p(p: Lg.P) -> Lr.Tail:
  match p:
    case Lg.P{ls, t}:
      log_tail_spec.of(ls, t)

def log_tail_spec(f: List<&2, Nat>) -> Lr.Tail:
  log_tail_spec.p(Lg.parse(f))

# the bytes of f an open keeps: all of them, its first `to`, or none (a
# refused open)
def log_kept(t: Lr.Tail, f: List<&2, Nat>) -> Maybe<&2, List<&2, Nat>>:
  match t:
    case Lr.Whole{}:
      Some{f}
    case Lr.Torn{to}:
      Some{List.take(&2, Nat, f, to)}
    case Lr.Odd{}:
      None{}

# LAW log_open_cuts_the_torn_tail (R1): an open keeps a file whose bytes all lie in complete
# lines, and cuts any other to the length of its complete lines
# EXCLUDES: a cut one byte off (the last newline lost, a torn byte kept), a
#   cut of a whole file, a torn tail kept, the newline index read from the
#   start, an empty file or a file with no newline mistaken
law log_open_cuts_the_torn_tail:
  for +f: List<&2, Nat>
  {Lr.tail(List.length(&2, Nat, f), log_last(f)) == log_tail_spec(f) : Lr.Tail}

# LAW log_open_keeps_the_complete_lines (R1): the bytes an open keeps of a file are exactly
# those of the lines open reads (Lg.recover): the recovery Rust runs is the
# model's
# EXCLUDES: a kept prefix that loses a complete line or keeps a torn byte,
#   a refused open of a real file
law log_open_keeps_the_complete_lines:
  for +f: List<&2, Nat>
  {log_kept(Lr.tail(List.length(&2, Nat, f), log_last(f)), f) == Some{Lg.render(Lg.recover(f))} : Maybe<&2, List<&2, Nat>>}

# The plan
# --------

# a step of a plan, with the commit it serves (Nil: the open)
type LogDo is Data:
  LogDo{a: Lr.Act, c: List<&2, Nat>}

def log_st(p: Lr.Plan) -> Lr.Store:
  match p:
    case Lr.Plan{s, acts}:
      s

def log_acts(p: Lr.Plan) -> List<&2, Lr.Act>:
  match p:
    case Lr.Plan{s, acts}:
      acts

# the steps acts, each serving c, then rest
def log_tag(acts: List<&2, Lr.Act>, +c: List<&2, Nat>, rest: List<&2, LogDo>) -> List<&2, LogDo>:
  match acts:
    case Nil{}:
      rest
    case a <> more:
      LogDo{a, c} <> log_tag(more, c, rest)

# the plans of the commits cs, which touch no sidecar file, from the
# storage s
def log_plan(cs: List<&2, List<&2, Nat>>, s: Lr.Store) -> List<&2, LogDo>:
  match cs:
    case Nil{}:
      Nil{}
    case +c <> rest:
      +p = Lr.Store.commit(s, Nil{})
      log_tag(log_acts(p), c, log_plan(rest, log_st(p)))

# the plan of an epoch of an fsync storage: its open, then the commits cs
def log_epoch_plan(cs: List<&2, List<&2, Nat>>) -> List<&2, LogDo>:
  +o = Lr.Store.open(Lr.Synced{})
  log_tag(log_acts(o), Nil{}, log_plan(cs, log_st(o)))

# what the steps xs of a plan do to the model's storage s when the crash
# comes after the first p of them: each step is the model's step of the
# same name (a sidecar's append or flush, and the link of a stamp, are
# steps of a file the model's storage does not hold); an Ack is no step of
# the file system: it follows the step before it
def log_exec(xs: List<&2, LogDo>, p: Nat, s: Lg.St) -> Lg.St:
  match xs:
    case Nil{}:
      s
    case x <> rest:
      match x:
        case LogDo{a, +c}:
          match a:
            case Lr.Ack{}:
              log_exec(rest, p, Lg.ack(c, s))
            case Lr.FlushParent{}:
              match p:
                case 0n:
                  s
                case 1n+q:
                  log_exec(rest, q, Lg.parent(s))
            case Lr.AppendSide{i}:
              match p:
                case 0n:
                  s
                case 1n+q:
                  log_exec(rest, q, s)
            case Lr.FlushSide{i}:
              match p:
                case 0n:
                  s
                case 1n+q:
                  log_exec(rest, q, s)
            case Lr.FlushDir{}:
              match p:
                case 0n:
                  s
                case 1n+q:
                  log_exec(rest, q, Lg.dir(s))
            case Lr.AppendMain{}:
              match p:
                case 0n:
                  s
                case 1n+q:
                  log_exec(rest, q, Lg.append(c, s))
            case Lr.FlushMain{}:
              match p:
                case 0n:
                  s
                case 1n+q:
                  log_exec(rest, q, Lg.flush(s))
            case Lr.Stamp{}:
              match p:
                case 0n:
                  s
                case 1n+q:
                  log_exec(rest, q, s)

# whether the steps xs, when the crash comes after the first p of them
# (counted as log_exec counts them), linked the stamp
def log_stamped(xs: List<&2, LogDo>, p: Nat) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case x <> rest:
      match x:
        case LogDo{a, c}:
          match a:
            case Lr.Ack{}:
              log_stamped(rest, p)
            case Lr.Stamp{}:
              match p:
                case 0n:
                  False{}
                case 1n+q:
                  True{}
            case Lr.FlushParent{}:
              match p:
                case 0n:
                  False{}
                case 1n+q:
                  log_stamped(rest, q)
            case Lr.AppendSide{i}:
              match p:
                case 0n:
                  False{}
                case 1n+q:
                  log_stamped(rest, q)
            case Lr.FlushSide{i}:
              match p:
                case 0n:
                  False{}
                case 1n+q:
                  log_stamped(rest, q)
            case Lr.FlushDir{}:
              match p:
                case 0n:
                  False{}
                case 1n+q:
                  log_stamped(rest, q)
            case Lr.AppendMain{}:
              match p:
                case 0n:
                  False{}
                case 1n+q:
                  log_stamped(rest, q)
            case Lr.FlushMain{}:
              match p:
                case 0n:
                  False{}
                case 1n+q:
                  log_stamped(rest, q)

# the disk after an epoch that runs the plan, and the commits it
# acknowledged
def log_after(d: Lg.Disk, e: Lg.Epoch) -> Lg.Disk:
  match e:
    case Lg.Epoch{cs, p, k, drop}:
      Lg.crash(k, drop, log_exec(log_epoch_plan(cs), p, Lg.open(d)))

def log_acked(d: Lg.Disk, e: Lg.Epoch) -> List<&2, List<&2, Nat>>:
  match e:
    case Lg.Epoch{cs, p, k, drop}:
      Lg.St.acked(log_exec(log_epoch_plan(cs), p, Lg.open(d)))

# LAW log_plan_runs_the_model (R2): the plan of an fsync storage's open and of commits that
# touch no sidecar file, cut after any number of steps, does to the storage
# exactly what the model's epoch does (Lg.run): the refinement of the model
# by the rule JsonlStorage runs
# EXCLUDES: an ack before the marker's flush or before the first commit's
#   directory flush, a missing parent or directory flush, a flush before
#   the append, a directory flush only on a later commit, steps in another
#   order, a commit appended twice or never
law log_plan_runs_the_model:
  for d: Lg.Disk
  for cs: List<&2, List<&2, Nat>>
  for p: Nat
  {log_exec(log_epoch_plan(cs), p, Lg.open(d)) == Lg.run(d, cs, p) : Lg.St}

# LAW log_plan_ack_durable (R2): log_ack_durable for the plan JsonlStorage runs: after a crash at
# any point the log is the log before, then every commit the plan
# acknowledged, then maybe more
# EXCLUDES: an acknowledged commit that a crash loses
law log_plan_ack_durable:
  for +d: Lg.Disk
  for e: Lg.Epoch
  exs rest: List<&2, List<&2, Nat>>
  {Lg.Disk.log(log_after(d, e)) == List.append(&2, List<&2, Nat>, List.append(&2, List<&2, Nat>, Lg.Disk.log(d), log_acked(d, e)), rest) : List<&2, List<&2, Nat>>}

# LAW log_plan_only_commits (R2): log_only_commits for the plan JsonlStorage runs: after a crash
# at any point the log is the log before, then a prefix of the commits
# EXCLUDES: a torn, reordered or doubled commit read after a crash
law log_plan_only_commits:
  for +d: Lg.Disk
  for e: Lg.Epoch
  exs n: Nat
  {Lg.Disk.log(log_after(d, e)) == List.append(&2, List<&2, Nat>, Lg.Disk.log(d), List.take(&2, List<&2, Nat>, Lg.Epoch.cs(e), n)) : List<&2, List<&2, Nat>>}

# The ledger
# ----------

# A history of the budget ledger's account file: one epoch per operation,
# in order, each the open of the file under its lock (a stamped storage,
# kept when the file's stamp names it), the records the operation appends
# (the commits), and the crash that may cut it; each opens the file as the
# crash before left it (Lg.Rest: whether its entries are durable is kept
# between operations). The history starts from the disk d with durable
# entries and no stamp: no file, or one an earlier release left.

# the first item of a list, Nil when it has none
def log_first(xs: List<&2, List<&2, List<&2, Nat>>>) -> List<&2, List<&2, Nat>>:
  match xs:
    case Nil{}:
      Nil{}
    case x <> more:
      x

def log_more(xs: List<&2, List<&2, List<&2, Nat>>>) -> List<&2, List<&2, List<&2, Nat>>>:
  match xs:
    case Nil{}:
      Nil{}
    case x <> more:
      more

# the first item of a list of Nats, 0n when it has none
def log_first_n(ns: List<&2, Nat>) -> Nat:
  match ns:
    case Nil{}:
      0n
    case n <> more:
      n

def log_more_n(ns: List<&2, Nat>) -> List<&2, Nat>:
  match ns:
    case Nil{}:
      Nil{}
    case n <> more:
      more

# the plan of a ledger operation: the open of a stamped storage, kept or
# not, then the commits cs
def log_ledger_plan(cs: List<&2, List<&2, Nat>>, +kept: Bool) -> List<&2, LogDo>:
  +o = Lr.Store.open(Lr.Stamped{kept})
  log_tag(log_acts(o), Nil{}, log_plan(cs, log_st(o)))

# the file at rest after the operation e from the file r: its storage
# after the steps the crash let it do, and whether its stamp names it
def log_ledger_step(+r: Lg.Rest, e: Lg.Epoch) -> Lg.Rest:
  match e:
    case Lg.Epoch{cs, +p, k, drop}:
      +kept = Lg.Rest.kept(r)
      +xs = log_ledger_plan(cs, kept)
      Lg.rest(k, drop, log_exec(xs, p, Lg.Rest.open(r)), Bool.or(kept, log_stamped(xs, p)))

# the records the operation e acknowledged, from the file r
def log_ledger_acked(+r: Lg.Rest, e: Lg.Epoch) -> List<&2, List<&2, Nat>>:
  match e:
    case Lg.Epoch{cs, p, k, drop}:
      Lg.St.acked(log_exec(log_ledger_plan(cs, Lg.Rest.kept(r)), p, Lg.Rest.open(r)))

# the file at rest after the operations es, from the file r
def log_ledger_rest(es: List<&2, Lg.Epoch>, r: Lg.Rest) -> Lg.Rest:
  match es:
    case Nil{}:
      r
    case e <> rest:
      log_ledger_rest(rest, log_ledger_step(r, e))

# the file a history starts from: the disk d, its entries durable, no stamp
def log_ledger_start(d: Lg.Disk) -> Lg.Rest:
  Lg.Rest{d, True{}, False{}}

# the disk after the operations es of the ledger, from the disk d, each
# running the plan the ledger runs
def log_ledger_after(es: List<&2, Lg.Epoch>, d: Lg.Disk) -> Lg.Disk:
  Lg.Rest.d(log_ledger_rest(es, log_ledger_start(d)))

# the records each operation of es acknowledged, from the file r, each
# operation's followed by the records of its item of xs
def log_ledger_kept.r(es: List<&2, Lg.Epoch>, +r: Lg.Rest, +xs: List<&2, List<&2, List<&2, Nat>>>) -> List<&2, List<&2, Nat>>:
  match es:
    case Nil{}:
      Nil{}
    case +e <> rest:
      List.append(&2, List<&2, Nat>, List.append(&2, List<&2, Nat>, log_ledger_acked(r, e), log_first(xs)), log_ledger_kept.r(rest, log_ledger_step(r, e), log_more(xs)))

# the records each operation of es acknowledged, from the disk d, each
# operation's followed by the records of its item of xs
def log_ledger_kept(es: List<&2, Lg.Epoch>, d: Lg.Disk, xs: List<&2, List<&2, List<&2, Nat>>>) -> List<&2, List<&2, Nat>>:
  log_ledger_kept.r(es, log_ledger_start(d), xs)

# the first records of each operation of es, as many as its item of ns
def log_ledger_taken(es: List<&2, Lg.Epoch>, +ns: List<&2, Nat>) -> List<&2, List<&2, Nat>>:
  match es:
    case Nil{}:
      Nil{}
    case e <> rest:
      List.append(&2, List<&2, Nat>, List.take(&2, List<&2, Nat>, Lg.Epoch.cs(e), log_first_n(ns)), log_ledger_taken(rest, log_more_n(ns)))

# LAW ledger_ack_durable (R5): an acknowledged ledger record survives any crash: after any
# history of the ledger's operations, each of which may crash at any point
# and the next of which opens what the crash left (an open reads the
# complete lines, R1), the file holds the log before, then each
# operation's acknowledged records, in order, each operation's followed by
# maybe more
# EXCLUDES: an acknowledged record that a later crash or a later
#   operation's open loses, an operation that acknowledges a record before
#   it is durable, records of two operations out of order, an open that
#   trusts the entries of a file a killed operation left (its directory
#   flush not done) or a stamp linked before both entries are durable
law ledger_ack_durable:
  for d: Lg.Disk
  for es: List<&2, Lg.Epoch>
  exs xs: List<&2, List<&2, List<&2, Nat>>>
  {Lg.Disk.log(log_ledger_after(es, d)) == List.append(&2, List<&2, Nat>, Lg.Disk.log(d), log_ledger_kept(es, d, xs)) : List<&2, List<&2, Nat>>}

# LAW ledger_only_records (R5): the ledger holds a prefix of its records in order: after any
# history of the ledger's operations, crashes included, the file holds the
# log before, then a prefix of each operation's records, in the order of
# the operations
# EXCLUDES: a torn, reordered or doubled record read after a crash, a
#   record no operation appended
law ledger_only_records:
  for d: Lg.Disk
  for es: List<&2, Lg.Epoch>
  exs ns: List<&2, Nat>
  {Lg.Disk.log(log_ledger_after(es, d)) == List.append(&2, List<&2, Nat>, Lg.Disk.log(d), log_ledger_taken(es, ns)) : List<&2, List<&2, Nat>>}

# the steps of commits cs that each append a record, flush the file and
# are acknowledged
def log_one_flush(cs: List<&2, List<&2, Nat>>) -> List<&2, LogDo>:
  match cs:
    case Nil{}:
      Nil{}
    case +c <> rest:
      LogDo{Lr.AppendMain{}, c} <> LogDo{Lr.FlushMain{}, c} <> LogDo{Lr.Ack{}, c} <> log_one_flush(rest)

# LAW ledger_kept_flushes_once (R6): an operation whose stamp names the
# file flushes nothing at its open, and each of its records appends,
# flushes the file once and is acknowledged: one flush per record
# EXCLUDES: a kept open that still flushes the parent or the directory, a
#   record of it flushed twice, stamped again or not flushed
law ledger_kept_flushes_once:
  for cs: List<&2, List<&2, Nat>>
  {log_ledger_plan(cs, True{}) == log_one_flush(cs) : List<&2, LogDo>}

# LAW ledger_stamped_after_ack (R6): after any history of the ledger's
# operations from a file with durable entries, an operation that
# acknowledged a record leaves a file its stamp names, whatever crash
# follows: the operation after it is kept
# EXCLUDES: a ledger that never stamps (every operation flushes the
#   directories), a stamp linked after the ack (a crash between loses it),
#   a stamp that a crash after the ack loses
law ledger_stamped_after_ack:
  for d: Lg.Disk
  for es: List<&2, Lg.Epoch>
  for e: Lg.Epoch
  for acked: {List.is_empty(&2, List<&2, Nat>, log_ledger_acked(log_ledger_rest(es, log_ledger_start(d)), e)) == False{} : Bool}
  {Lg.Rest.kept(log_ledger_step(log_ledger_rest(es, log_ledger_start(d)), e)) == True{} : Bool}

# The plan of a commit
# --------------------
# A commit's plan is read step by step, as a file system sees it: R3's
# order is checked per sidecar file and for main.jsonl, without writing the
# plan out.

# the durable directory entry of the sidecar i of ds, None when the commit
# has no sidecar i
def log_nth(ds: List<&2, Bool>, i: Nat) -> Maybe<&2, Bool>:
  match ds:
    case Nil{}:
      None{}
    case d <> more:
      match i:
        case 0n:
          Some{d}
        case 1n+j:
          log_nth(more, j)

# the steps acts touch neither the records nor the flush of the sidecar i
def log_side_none(acts: List<&2, Lr.Act>, +i: Nat) -> Bool:
  match acts:
    case Nil{}:
      True{}
    case a <> rest:
      match a:
        case Lr.AppendSide{j}:
          Bool.and(Bool.not(Nat.is_eq(j, i)), log_side_none(rest, i))
        case Lr.FlushSide{j}:
          Bool.and(Bool.not(Nat.is_eq(j, i)), log_side_none(rest, i))
        case Lr.FlushParent{}:
          log_side_none(rest, i)
        case Lr.FlushDir{}:
          log_side_none(rest, i)
        case Lr.AppendMain{}:
          log_side_none(rest, i)
        case Lr.FlushMain{}:
          log_side_none(rest, i)
        case Lr.Ack{}:
          log_side_none(rest, i)
        case Lr.Stamp{}:
          log_side_none(rest, i)

# a sidecar is ready for the marker that depends on it: its records are
# appended and, with fsync, flushed since and its directory entry durable
def log_side_ready(w: Bool, f: Bool, e: Bool, fsync: Bool) -> Bool:
  Bool.and(w, Bool.or(Bool.not(fsync), Bool.and(f, e)))

# the sidecar i through the steps acts, up to the marker: w its records
# appended, f flushed since, e its directory entry durable. Its records are
# appended once; a flush of the file flushes what is appended; a directory
# flush makes the entry of an appended file durable. At the marker the
# sidecar must be ready, and no later step touches it; no marker: the plan
# is not a commit's
def log_side_walk(acts: List<&2, Lr.Act>, +i: Nat, +w: Bool, f: Bool, +e: Bool, +fsync: Bool) -> Bool:
  match acts:
    case Nil{}:
      False{}
    case a <> rest:
      match a:
        case Lr.AppendSide{j}:
          +hit = Nat.is_eq(j, i)
          Bool.and(Bool.not(Bool.and(hit, w)), log_side_walk(rest, i, Bool.or(hit, w), Bool.and(Bool.not(hit), f), e, fsync))
        case Lr.FlushSide{j}:
          +hit = Nat.is_eq(j, i)
          log_side_walk(rest, i, w, Bool.or(Bool.and(hit, w), Bool.and(Bool.not(hit), f)), e, fsync)
        case Lr.FlushDir{}:
          log_side_walk(rest, i, w, f, Bool.or(e, w), fsync)
        case Lr.AppendMain{}:
          Bool.and(log_side_ready(w, f, e, fsync), log_side_none(rest, i))
        case Lr.FlushParent{}:
          log_side_walk(rest, i, w, f, e, fsync)
        case Lr.FlushMain{}:
          log_side_walk(rest, i, w, f, e, fsync)
        case Lr.Ack{}:
          log_side_walk(rest, i, w, f, e, fsync)
        case Lr.Stamp{}:
          log_side_walk(rest, i, w, f, e, fsync)

# R3 for the sidecar i of a commit whose sidecars have the durable entries
# ds: a sidecar of the commit is ready at the marker (its directory entry
# starts durable as ds says, not flushed), any other index is untouched
def log_side(acts: List<&2, Lr.Act>, +i: Nat, m: Maybe<&2, Bool>, fsync: Bool) -> Bool:
  match m:
    case None{}:
      log_side_none(acts, i)
    case Some{d}:
      log_side_walk(acts, i, False{}, False{}, d, fsync)

# a and b are the same Bool
def log_same(a: Bool, b: Bool) -> Bool:
  match a:
    case True{}:
      b
    case False{}:
      Bool.not(b)

# main.jsonl through the steps acts of a commit: m its marker appended, fl
# flushed since, e its directory entry durable (the file exists from the
# open, so any directory flush makes it durable), st the stamp linked. The
# marker is appended once; the stamp is linked once, only by a storage that
# stamps, with fsync, after the marker's flush and once the entry is
# durable; the ack is the last step, after the marker and, with fsync, its
# flush and a durable entry; the stamp is linked exactly when the storage
# stamps, with fsync, and main.jsonl's entry was not durable before (was)
def log_main_walk(acts: List<&2, Lr.Act>, +m: Bool, +fl: Bool, +e: Bool, +st: Bool, +fsync: Bool, +stamps: Bool, +was: Bool) -> Bool:
  match acts:
    case Nil{}:
      False{}
    case a <> rest:
      match a:
        case Lr.AppendMain{}:
          Bool.and(Bool.not(m), log_main_walk(rest, True{}, False{}, e, st, fsync, stamps, was))
        case Lr.FlushMain{}:
          log_main_walk(rest, m, m, e, st, fsync, stamps, was)
        case Lr.FlushDir{}:
          log_main_walk(rest, m, fl, True{}, st, fsync, stamps, was)
        case Lr.Stamp{}:
          Bool.and(Bool.and(Bool.and(Bool.and(stamps, fsync), Bool.and(m, fl)), Bool.and(e, Bool.not(st))), log_main_walk(rest, m, fl, e, True{}, fsync, stamps, was))
        case Lr.Ack{}:
          Bool.and(List.is_empty(&2, Lr.Act, rest), Bool.and(m, Bool.and(Bool.or(Bool.not(fsync), Bool.and(fl, e)), log_same(st, Bool.and(Bool.and(stamps, fsync), Bool.not(was))))))
        case Lr.FlushParent{}:
          log_main_walk(rest, m, fl, e, st, fsync, stamps, was)
        case Lr.AppendSide{j}:
          log_main_walk(rest, m, fl, e, st, fsync, stamps, was)
        case Lr.FlushSide{j}:
          log_main_walk(rest, m, fl, e, st, fsync, stamps, was)

# some entry of ds is not durable
def log_fresh(ds: List<&2, Bool>) -> Bool:
  match ds:
    case Nil{}:
      False{}
    case d <> more:
      Bool.or(Bool.not(d), log_fresh(more))

# 1 for True, 0 for False
def log_bit(b: Bool) -> Nat:
  match b:
    case True{}:
      1n
    case False{}:
      0n

# the flushes a commit owes with fsync, R3's "nothing else": each sidecar
# file once, the directory once when a sidecar's entry is not durable,
# main.jsonl once, and the directory once more when main.jsonl's entry is
# not durable; none without fsync
def log_flush_due(fsync: Bool, main: Bool, +ds: List<&2, Bool>) -> Nat:
  match fsync:
    case False{}:
      0n
    case True{}:
      Nat.add(List.length(&2, Bool, ds), Nat.add(log_bit(log_fresh(ds)), 1n+log_bit(Bool.not(main))))

# a step that flushes a file or a directory (the link of a stamp flushes
# nothing)
def log_is_flush(a: Lr.Act) -> Bool:
  match a:
    case Lr.FlushParent{}:
      True{}
    case Lr.AppendSide{i}:
      False{}
    case Lr.FlushSide{i}:
      True{}
    case Lr.FlushDir{}:
      True{}
    case Lr.AppendMain{}:
      False{}
    case Lr.FlushMain{}:
      True{}
    case Lr.Ack{}:
      False{}
    case Lr.Stamp{}:
      False{}

# some step of acts is a flush
def log_any_flush(acts: List<&2, Lr.Act>) -> Bool:
  match acts:
    case Nil{}:
      False{}
    case a <> more:
      Bool.or(log_is_flush(a), log_any_flush(more))

# some step of the commits dss (per commit, the durable entries of its
# sidecar files) is a flush, each commit planned from the storage the one
# before it left, the first from s
def log_session_flushes(dss: List<&2, List<&2, Bool>>, s: Lr.Store) -> Bool:
  match dss:
    case Nil{}:
      False{}
    case ds <> rest:
      +p = Lr.Store.commit(s, ds)
      Bool.or(log_any_flush(log_acts(p)), log_session_flushes(rest, log_st(p)))

# the number of steps of acts that flush a file or a directory
def log_flush_count(acts: List<&2, Lr.Act>) -> Nat:
  match acts:
    case Nil{}:
      0n
    case a <> more:
      Nat.add(log_bit(log_is_flush(a)), log_flush_count(more))

# LAW log_commit_sidecars (R3): in every commit's plan, for every storage
# and every sidecar list, each sidecar file's records are appended once,
# before the marker that depends on them, and with fsync flushed after
# their append and with a durable directory entry (durable before, or a
# directory flush after the append) before the marker; no step touches a
# sidecar after the marker, nor any sidecar index the commit does not have
# EXCLUDES: a marker before a record or before a flush it depends on, a
#   sidecar's directory flush skipped for a new entry, a sidecar skipped,
#   doubled or misnumbered, a flush before the append it must make durable
law log_commit_sidecars:
  for fsync: Bool
  for main: Bool
  for stamp: Bool
  for +ds: List<&2, Bool>
  for +i: Nat
  {log_side(log_acts(Lr.Store.commit(Lr.Store{fsync, main, stamp}, ds)), i, log_nth(ds, i), fsync) == True{} : Bool}

# LAW log_commit_marker_then_ack (R3): every commit's plan, for every
# storage and every sidecar list, appends its marker once and ends with its
# one ack, after the marker and, with fsync, after the marker's flush and
# with main.jsonl's directory entry durable; a storage that stamps links
# its stamp once, after that flush and that durable entry and before the
# ack, exactly when it has fsync and main.jsonl's entry was not durable;
# no other storage links one
# EXCLUDES: an ack before the last step or before the marker's flush, two
#   acks or markers, main.jsonl's entry forgotten (an ack before its
#   directory flush), a stamp linked before the directory flush, without
#   one, again, by a kept storage or by a storage that does not stamp
law log_commit_marker_then_ack:
  for fsync: Bool
  for main: Bool
  for stamp: Bool
  for +ds: List<&2, Bool>
  {log_main_walk(log_acts(Lr.Store.commit(Lr.Store{fsync, main, stamp}, ds)), False{}, False{}, main, False{}, fsync, stamp, main) == True{} : Bool}

# LAW log_commit_flushes (R3): every commit's plan flushes exactly what R3
# names and nothing else: with fsync each sidecar file once, the directory
# once when a sidecar's entry is not durable, main.jsonl once, the
# directory once more when main.jsonl's entry is not durable; without
# fsync nothing
# EXCLUDES: an extra or missing flush, a directory flush done for none or
#   skipped for a new entry, a flush without fsync
law log_commit_flushes:
  for fsync: Bool
  for main: Bool
  for stamp: Bool
  for +ds: List<&2, Bool>
  {log_flush_count(log_acts(Lr.Store.commit(Lr.Store{fsync, main, stamp}, ds))) == log_flush_due(fsync, main, ds) : Nat}

# LAW log_commit_storage (R3): a commit keeps the storage's fsync and its
# stamp, and with fsync main.jsonl's directory entry is durable after it;
# without fsync it stays as it was
# EXCLUDES: a commit that turns fsync on or off, forgets main.jsonl's
#   durable entry or assumes it without fsync, drops or adds the stamp
law log_commit_storage:
  for fsync: Bool
  for main: Bool
  for stamp: Bool
  for +ds: List<&2, Bool>
  {log_st(Lr.Store.commit(Lr.Store{fsync, main, stamp}, ds)) == Lr.Store{fsync, Bool.or(fsync, main), stamp} : Lr.Store}

# the storage an open leaves: fsync as asked, main.jsonl's directory entry
# durable only when a stamp names it, a stamp only for a stamped storage
def log_open_store(h: Lr.How) -> Lr.Store:
  match h:
    case Lr.Unsynced{}:
      Lr.Store{False{}, False{}, False{}}
    case Lr.Synced{}:
      Lr.Store{True{}, False{}, False{}}
    case Lr.Stamped{kept}:
      Lr.Store{True{}, kept, True{}}

# the steps an open owes the storage it leaves: the flush of the parent
# directory when that storage flushes (fsync) and main.jsonl's entry is not
# durable (no stamp names it); nothing else
def log_parent_flush(s: Lr.Store) -> List<&2, Lr.Act>:
  match s:
    case Lr.Store{fsync, main, stamp}:
      match fsync:
        case False{}:
          Nil{}
        case True{}:
          match main:
            case True{}:
              Nil{}
            case False{}:
              [Lr.FlushParent{}]

# LAW log_open_storage (R3): the storage an open leaves has the fsync it
# was opened with, main.jsonl's directory entry durable only when the
# storage's stamp names it (no commit has flushed it), and a stamp only
# when it was opened stamped
# EXCLUDES: an open that turns fsync on or off (a storage opened without
#   fsync whose every commit then flushes, one opened with fsync that
#   never does), a storage whose first commit skips the directory flush of
#   main.jsonl that no stamp names, a JsonlStorage that links a stamp, a
#   ledger that never does
law log_open_storage:
  for h: Lr.How
  {log_st(Lr.Store.open(h)) == log_open_store(h) : Lr.Store}

# LAW log_open_flushes_the_parent (R3): an open flushes the parent
# directory exactly when the storage it leaves flushes and main.jsonl's
# entry is not durable (no stamp names it), and does nothing else
# EXCLUDES: an open that skips the parent's flush for a file no stamp
#   names, a kept open that still flushes it, an open that flushes without
#   fsync or does any other step
law log_open_flushes_the_parent:
  for h: Lr.How
  {log_acts(Lr.Store.open(h)) == log_parent_flush(log_st(Lr.Store.open(h))) : List<&2, Lr.Act>}

# LAW log_without_fsync_never_flushes (R3): a storage opened without fsync
# flushes nothing: neither its open nor any commit after it, whatever the
# commits and their sidecar files (R3 names every flush "(fsync)")
# EXCLUDES: an open without fsync that flushes the parent directory or
#   leaves a storage that flushes, a commit without fsync that flushes a
#   sidecar, main.jsonl or the directory
law log_without_fsync_never_flushes:
  for dss: List<&2, List<&2, Bool>>
  {Bool.or(log_any_flush(log_acts(Lr.Store.open(Lr.Unsynced{}))), log_session_flushes(dss, log_st(Lr.Store.open(Lr.Unsynced{})))) == False{} : Bool}

# The entry
# ---------

# the facts of a file as Rust writes them: its length, then its last
# newline (0 none | 1 the index)
def log_spell_last(m: Maybe<&2, Nat>, rest: String) -> String:
  match m:
    case None{}:
      Wr.put_nat(0n, rest)
    case Some{i}:
      Wr.put_nat(1n, Wr.put_nat(i, rest))

def log_spell_req(len: Nat, last: Maybe<&2, Nat>) -> String:
  Wr.put_nat(len, log_spell_last(last, ""))

# a decision of an open as Rust reads it: 0 whole | 1 the length | 2 odd
def log_spell_tail(t: Lr.Tail) -> String:
  match t:
    case Lr.Whole{}:
      Wr.put_nat(0n, "")
    case Lr.Torn{to}:
      Wr.put_nat(1n, Wr.put_nat(to, ""))
    case Lr.Odd{}:
      Wr.put_nat(2n, "")

# a step as Rust reads it: its tag, then a sidecar's index
def log_spell_act(a: Lr.Act, rest: String) -> String:
  match a:
    case Lr.FlushParent{}:
      Wr.put_nat(0n, rest)
    case Lr.AppendSide{i}:
      Wr.put_nat(1n, Wr.put_nat(i, rest))
    case Lr.FlushSide{i}:
      Wr.put_nat(2n, Wr.put_nat(i, rest))
    case Lr.FlushDir{}:
      Wr.put_nat(3n, rest)
    case Lr.AppendMain{}:
      Wr.put_nat(4n, rest)
    case Lr.FlushMain{}:
      Wr.put_nat(5n, rest)
    case Lr.Ack{}:
      Wr.put_nat(6n, rest)
    case Lr.Stamp{}:
      Wr.put_nat(7n, rest)

# how a storage opens as Rust writes it, then rest: 0 without fsync, 1
# with fsync, 2 stamped then kept
def log_spell_how(h: Lr.How, rest: String) -> String:
  match h:
    case Lr.Unsynced{}:
      Wr.put_nat(0n, rest)
    case Lr.Synced{}:
      Wr.put_nat(1n, rest)
    case Lr.Stamped{kept}:
      Wr.put_nat(2n, Wr.put_bool(kept, rest))

# the stepper's answer to a plan: the storage after it, and its steps
def log_answer(p: Lr.Plan) -> FLg.St & String:
  match p:
    case Lr.Plan{s, acts}:
      (FLg.Running{s}, Wr.put_list(~Lr.Act, ~log_spell_act, acts, ""))

# the sidecar entries of a commit as Rust writes them
def log_spell_sides(ds: List<&2, Bool>) -> String:
  Wr.put_list(~Bool, ~Wr.put_bool, ds, "")

# the reply and the state of a stepper's answer
def log_reply(r: FLg.St & String) -> String:
  (st, s) = r
  s

def log_state(r: FLg.St & String) -> FLg.St:
  (st, s) = r
  st

# the replies of the stepper to the events evs, fed in order from the
# state st
def log_replies(+evs: List<&2, String>, +st: FLg.St) -> List<&2, String>:
  match evs:
    case Nil{}:
      Nil{}
    case e <> t:
      log_reply(FLg.step(st, e)) <> log_replies(t, log_state(FLg.step(st, e)))

# the state of the stepper after the events evs, fed in order from the
# state st
def log_fed_state(evs: List<&2, String>, st: FLg.St) -> FLg.St:
  match evs:
    case Nil{}:
      st
    case e <> t:
      log_fed_state(t, log_state(FLg.step(st, e)))

# one error form "log: the open was refused" for each event of evs
def log_refused(evs: List<&2, String>) -> List<&2, String>:
  match evs:
    case Nil{}:
      Nil{}
    case e <> t:
      Wr.err("log: the open was refused") <> log_refused(t)

# a last newline that fits the wire
def log_last_fits(m: Maybe<&2, Nat>) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{i}:
      LawsBase.wire_fits(i)

# LAW log_ffi_answers_the_open (R4): the entry answers the facts of a file, as Rust writes
# them, with the spelling of the open's decision
# EXCLUDES: an entry that answers anything but the rule's decision, a
#   field read into the wrong place, a reply the Rust reader reads as
#   another decision
law log_ffi_answers_the_open:
  for +len: Nat
  for +last: Maybe<&2, Nat>
  for fits: {Bool.and(LawsBase.wire_fits(len), log_last_fits(last)) == True{} : Bool}
  {FLg.ffi(log_spell_req(len, last)) == log_spell_tail(Lr.tail(len, last)) : String}

# LAW log_ffi_reads_only_fitting_requests (R4): an input the entry answers with no error form is the
# spelling of a request whose numbers fit the wire
# EXCLUDES: a decoder that reads a number of 15 digits or more (a length
#   or a last newline past the wire: misread, or past the runtime's Nat)
law log_ffi_reads_only_fitting_requests:
  for +s: String
  for ok: {LawsBase.wire_opens_err(FLg.ffi(s)) == False{} : Bool}
  exs len: Nat
  exs last: Maybe<&2, Nat>
  {s == log_spell_req(len, last) : String} & {Bool.and(LawsBase.wire_fits(len), log_last_fits(last)) == True{} : Bool}

# LAW log_stepper_open (R4): the stepper opens how a storage opens, as Rust writes it, with the
# open's plan: its storage and the spelling of its steps
# EXCLUDES: a stepper that answers or keeps anything but the rule's plan
law log_stepper_open:
  for h: Lr.How
  {FLg.open(log_spell_how(h, "")) == log_answer(Lr.Store.open(h)) : FLg.St & String}

# LAW log_stepper_open_reads_only_a_how (R4): an open the stepper answers with no error form
# reads how a storage opens and nothing else
# EXCLUDES: a default for malformed input, input left over ignored, a tag
#   past the stamped one read as some way to open
law log_stepper_open_reads_only_a_how:
  for +s: String
  for ok: {LawsBase.wire_opens_err(log_reply(FLg.open(s))) == False{} : Bool}
  exs h: Lr.How
  {s == log_spell_how(h, "") : String}

# LAW log_stepper_commit (R4): the stepper answers a commit's sidecar entries, as Rust writes
# them, with the commit's plan: the storage after it and the spelling of
# its steps
# EXCLUDES: a stepper that answers or keeps anything but the rule's plan,
#   a durability read for another sidecar
law log_stepper_commit:
  for +s: Lr.Store
  for +ds: List<&2, Bool>
  for fits: {LawsBase.wire_fits(List.length(&2, Bool, ds)) == True{} : Bool}
  {FLg.step(FLg.Running{s}, log_spell_sides(ds)) == log_answer(Lr.Store.commit(s, ds)) : FLg.St & String}

# LAW log_stepper_reads_only_fitting_commits (R4): an event the stepper answers with no error form is
# the spelling of a commit whose count fits the wire
# EXCLUDES: a decoder that reads a count of 15 digits or more
law log_stepper_reads_only_fitting_commits:
  for +st: FLg.St
  for +s: String
  for ok: {LawsBase.wire_opens_err(log_reply(FLg.step(st, s))) == False{} : Bool}
  exs ds: List<&2, Bool>
  {s == log_spell_sides(ds) : String} & {LawsBase.wire_fits(List.length(&2, Bool, ds)) == True{} : Bool}

# LAW log_stepper_refusal_keeps_the_state (R4): a refused event keeps the stepper's state
# EXCLUDES: a malformed event that marks main.jsonl's entry durable or
#   changes fsync
law log_stepper_refusal_keeps_the_state:
  for +st: FLg.St
  for +s: String
  for no: {LawsBase.wire_opens_err(log_reply(FLg.step(st, s))) == True{} : Bool}
  {log_state(FLg.step(st, s)) == st : FLg.St}

# LAW log_stepper_shut_refuses (R4): after a refused open, the stepper refuses every event
# EXCLUDES: a plan from a stepper whose open was refused
law log_stepper_shut_refuses:
  for +s: String
  {LawsBase.wire_opens_err(log_reply(FLg.step(FLg.Shut{}, s))) == True{} : Bool}

# the facts of a file as Rust writes them, then rest (log_spell_req is it
# before nothing)
def log_spell_req_then(len: Nat, last: Maybe<&2, Nat>, rest: String) -> String:
  Wr.put_nat(len, log_spell_last(last, rest))

# LAW log_ffi_left_over_spelled (R4): the facts of a file that fit, followed by any more input,
# answer exactly the error form "log: input left over"
# EXCLUDES: trailing input ignored or read as part of the request, the
#   left-over error reworded or swapped with the malformed one
law log_ffi_left_over_spelled:
  for +len: Nat
  for +last: Maybe<&2, Nat>
  for fits: {Bool.and(LawsBase.wire_fits(len), log_last_fits(last)) == True{} : Bool}
  for +c: Char
  for +t: String
  {FLg.ffi(log_spell_req_then(len, last, SCon{c, t})) == Wr.err("log: input left over") : String}

# LAW log_ffi_malformed_unless_request (R4): every answer of the entry but the error form "log:
# malformed request" comes from an input that begins with the facts of a
# file that fit
# EXCLUDES: the left-over error (or any answer) for input that does not
#   begin with a request, the malformed error reworded or swapped with a
#   stepper's error text
law log_ffi_malformed_unless_request:
  for +s: String
  for other: {String.eq(FLg.ffi(s), Wr.err("log: malformed request")) == False{} : Bool}
  exs len: Nat
  exs last: Maybe<&2, Nat>
  exs rest: String
  {(s, Bool.and(LawsBase.wire_fits(len), log_last_fits(last))) == (log_spell_req_then(len, last, rest), True{}) : String & Bool}

# LAW log_stepper_open_left_over (R4): an open with how a storage opens and any more input
# answers exactly the error form "log: input left over"
# EXCLUDES: trailing input ignored, the left-over error reworded or swapped
#   with the malformed open
law log_stepper_open_left_over:
  for h: Lr.How
  for +c: Char
  for +t: String
  {log_reply(FLg.open(log_spell_how(h, SCon{c, t}))) == Wr.err("log: input left over") : String}

# LAW log_stepper_open_malformed_unless_how (R4): every answer of the open but the error form
# "log: malformed open" comes from an input that begins with how a storage
# opens
# EXCLUDES: the left-over error (or a plan) for an open that does not begin
#   with how a storage opens, the malformed open reworded or swapped with
#   another text
law log_stepper_open_malformed_unless_how:
  for +s: String
  for other: {String.eq(log_reply(FLg.open(s)), Wr.err("log: malformed open")) == False{} : Bool}
  exs h: Lr.How
  exs rest: String
  {s == log_spell_how(h, rest) : String}

# LAW log_stepper_left_over (R4): from every storage, a commit's sidecar entries whose count
# fits, followed by any more input, answer exactly the error form "log:
# input left over"
# EXCLUDES: trailing input ignored or read as part of the commit, the
#   left-over error reworded or swapped with the malformed commit
law log_stepper_left_over:
  for +st: Lr.Store
  for +ds: List<&2, Bool>
  for fits: {LawsBase.wire_fits(List.length(&2, Bool, ds)) == True{} : Bool}
  for +c: Char
  for +t: String
  {log_reply(FLg.step(FLg.Running{st}, Wr.put_list(~Bool, ~Wr.put_bool, ds, SCon{c, t}))) == Wr.err("log: input left over") : String}

# LAW log_stepper_malformed_unless_commit (R4): from every storage, every answer of a step but
# the error form "log: malformed commit" comes from an input that begins
# with a commit's sidecar entries whose count fits
# EXCLUDES: the left-over error (or a plan) for input that does not begin
#   with a commit, the malformed commit reworded or swapped with the
#   refused open's text
law log_stepper_malformed_unless_commit:
  for +st: Lr.Store
  for +s: String
  for other: {String.eq(log_reply(FLg.step(FLg.Running{st}, s)), Wr.err("log: malformed commit")) == False{} : Bool}
  exs ds: List<&2, Bool>
  exs rest: String
  {(s, LawsBase.wire_fits(List.length(&2, Bool, ds))) == (Wr.put_list(~Bool, ~Wr.put_bool, ds, rest), True{}) : String & Bool}

# LAW log_stepper_refused_open_history (R4): after an open the stepper refuses (its reply is
# an error form), any events fed to it in order are each answered exactly
# the error form "log: the open was refused", and the stepper is still
# shut after them
# EXCLUDES: a refused open that keeps a default storage, a refused stepper
#   that plans a commit or opens again after some event, the refusal
#   reworded or swapped with another error text
law log_stepper_refused_open_history:
  for +s: String
  for no: {LawsBase.wire_opens_err(log_reply(FLg.open(s))) == True{} : Bool}
  for +evs: List<&2, String>
  {log_replies(evs, log_state(FLg.open(s))) == log_refused(evs) : List<&2, String>} & {log_fed_state(evs, log_state(FLg.open(s))) == FLg.Shut{} : FLg.St}

# LAW log_fits_example (R4): witness: the premises of log_ffi_answers_the_open and
# log_stepper_commit hold for requests Rust writes
# EXCLUDES: a vacuous log_ffi_answers_the_open or log_stepper_commit
law log_fits_example:
  {Bool.and(Bool.and(LawsBase.wire_fits(10n), log_last_fits(Some{4n})), LawsBase.wire_fits(List.length(&2, Bool, [True{}, False{}]))) == True{} : Bool}

# LAW log_ffi_example (R4): anchor: the facts Rust writes, as text, with the replies: a torn
# tail after the newline at 4 of 10 bytes, a whole file, an empty file, a
# file with no newline, a newline past the end, malformed input, input
# left over
# EXCLUDES: a request or reply format other than WIRE.md's
law log_ffi_example:
  {[FLg.ffi("10,1,4,"), FLg.ffi("10,1,9,"), FLg.ffi("0,0,"), FLg.ffi("7,0,"), FLg.ffi("3,1,5,"), FLg.ffi("1,2,"), FLg.ffi("0,0,x")] == ["1,5,", "0,", "0,", "1,0,", "2,", Wr.err("log: malformed request"), Wr.err("log: input left over")] : List<&2, String>}

# LAW log_stepper_example (R4): anchor: the events Rust writes, as text, with the replies: an
# fsync open, an open without fsync, a stamped open its stamp does not
# name and one it names, a first commit with no sidecar, a stamped
# storage's first commit and a kept one's, a commit with a durable and a
# new sidecar, a commit without fsync, a malformed commit, malformed opens
# (a letter, the Bool of earlier releases, a tag past the stamped one), a
# commit after one
# EXCLUDES: a request or reply format other than WIRE.md's (the open's
#   tags, Bools as T and F, the act tags, the sidecar indexes)
law log_stepper_example:
  {[log_reply(FLg.open("1,")), log_reply(FLg.open("0,")), log_reply(FLg.open("2,F")), log_reply(FLg.open("2,T")), log_reply(FLg.step(FLg.Running{Lr.Store{True{}, False{}, False{}}}, "0,")), log_reply(FLg.step(FLg.Running{Lr.Store{True{}, False{}, True{}}}, "0,")), log_reply(FLg.step(FLg.Running{Lr.Store{True{}, True{}, True{}}}, "0,")), log_reply(FLg.step(FLg.Running{Lr.Store{True{}, True{}, False{}}}, "2,TF")), log_reply(FLg.step(FLg.Running{Lr.Store{False{}, False{}, False{}}}, "1,F")), log_reply(FLg.step(FLg.Running{Lr.Store{True{}, True{}, False{}}}, "1,X")), log_reply(FLg.open("X")), log_reply(FLg.open("T")), log_reply(FLg.open("3,")), log_reply(FLg.step(FLg.Shut{}, "0,"))] == ["1,0,", "0,", "1,0,", "0,", "4,4,5,3,6,", "5,4,5,3,7,6,", "3,4,5,6,", "8,1,0,1,1,2,0,2,1,3,4,5,6,", "3,1,0,4,6,", Wr.err("log: malformed commit"), Wr.err("log: malformed open"), Wr.err("log: malformed open"), Wr.err("log: malformed open"), Wr.err("log: the open was refused")] : List<&2, String>}

# The entry, whole
# ----------------
# The laws above pin the entry on the requests Rust writes and send every
# other input to the error form; these pin its reply on every input
# string, from spec helpers alone: the wire primitives (Wr.get_nat,
# Wr.get_bool, Wr.end, Wr.err: pinned by laws/wire.bend), the spellers
# above and the model of the log (spec/durable/log.bend, through
# log_tail_spec).

# the file of len bytes whose only newline (0n) is at the index last (None:
# it has none) and whose every other byte is the data byte 1n; a newline at
# or past the end is no byte of it
def log_file(len: Nat, last: Maybe<&2, Nat>) -> List<&2, Nat>:
  match len:
    case 0n:
      Nil{}
    case 1n+k:
      match last:
        case None{}:
          1n <> log_file(k, None{})
        case Some{i}:
          match i:
            case 0n:
              0n <> log_file(k, None{})
            case 1n+j:
              1n <> log_file(k, Some{j})

def log_tail_facts.in(inside: Bool, len: Nat, i: Nat) -> Lr.Tail:
  match inside:
    case True{}:
      log_tail_spec(log_file(len, Some{i}))
    case False{}:
      Lr.Odd{}

# what an open must do from the facts of a file (R1), its length and its
# last newline: what it must do with a file of those facts (log_tail_spec
# of log_file); facts no file has (a newline at or past the end) are
# refused
def log_tail_facts(+len: Nat, last: Maybe<&2, Nat>) -> Lr.Tail:
  match last:
    case None{}:
      log_tail_spec(log_file(len, None{}))
    case Some{+i}:
      log_tail_facts.in(Nat.is_lt(i, len), len, i)

# the last newline of a request, read with the wire primitives: 0 none, 1
# then the index
def log_rd_last.some(r: Wr.Dec<Nat>) -> Wr.Dec<Maybe<&2, Nat>>:
  match r:
    case Wr.Got{n, s}:
      Wr.Got{Some{n}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def log_rd_last(r: Wr.Dec<Nat>) -> Wr.Dec<Maybe<&2, Nat>>:
  match r:
    case Wr.Got{t, s}:
      match t:
        case 0n:
          Wr.Got{None{}, s}
        case 1n:
          log_rd_last.some(Wr.get_nat(s))
        case 2n+k:
          Wr.Bad{}
    case Wr.Bad{}:
      Wr.Bad{}

def log_ffi_spec.end(done: Bool, len: Nat, last: Maybe<&2, Nat>) -> String:
  match done:
    case True{}:
      log_spell_tail(log_tail_facts(len, last))
    case False{}:
      Wr.err("log: input left over")

def log_ffi_spec.last(len: Nat, r: Wr.Dec<Maybe<&2, Nat>>) -> String:
  match r:
    case Wr.Got{m, s}:
      log_ffi_spec.end(Wr.end(s), len, m)
    case Wr.Bad{}:
      Wr.err("log: malformed request")

def log_ffi_spec.len(r: Wr.Dec<Nat>) -> String:
  match r:
    case Wr.Got{n, s}:
      log_ffi_spec.last(n, log_rd_last(Wr.get_nat(s)))
    case Wr.Bad{}:
      Wr.err("log: malformed request")

# the reply to the input s of the open of a file: its length, then its
# last newline, then nothing, answered with the spelling of the open's
# decision; a malformed field: "log: malformed request"; input left over:
# "log: input left over"
def log_ffi_spec(s: String) -> String:
  log_ffi_spec.len(Wr.get_nat(s))

# LAW log_tail_exact (R1): the open's decision on any facts is what the
# open must do with a file of those facts: keep a file whose bytes all lie
# in complete lines, cut any other to its complete lines; facts no file
# has (a newline at or past the end) are refused
# EXCLUDES: a cut one byte off, a torn tail kept, a whole file cut, a
#   real file refused or odd facts cut, on facts that the laws above pin
#   only through a file (log_open_cuts_the_torn_tail) and no law pins alone
law log_tail_exact:
  for +len: Nat
  for +last: Maybe<&2, Nat>
  {Lr.tail(len, last) == log_tail_facts(len, last) : Lr.Tail}

# LAW log_ffi_exact (R1, R4): the entry's reply to every input string is
# the spec's: the open's decision on the facts of the one request it
# spells, or the exact error form of a malformed field or of input left
# over
# EXCLUDES: a reply that the specs do not determine for some input (a
#   decision of the model's own, a value answered to malformed input, an
#   error form with another text or for the other fault)
law log_ffi_exact:
  for +s: String
  {FLg.ffi(s) == log_ffi_spec(s) : String}
