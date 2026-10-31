# eukhe: the laws of area log

import Base
import ../spec/durable/log.bend as Lg
import ../bend/log.bend as Lr
import ../bend/wire.bend as Wr
import ../bend/ffi_log.bend as FLg
import ./base.bend as LawsBase

# ---- storage ----

# LAWS (D2): the durable storage of a session. Each law is an open claim
# about the models in spec/durable/log.bend and bend/staging.bend; PROOF.bend
# proves them (as Log.<law>) with the lemmas of proof/log/
# and proof/staging/.

# (D2) Storage
# ------------
# docs/state.md D2. The commit log `main.jsonl` (spec/durable/log.bend): every
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
# crates/eukhe-durable/src/storage/jsonl/plan.rs): what an open does with a
# file (Lr.tail), and the plan of steps of the storage (Lr.Store.open,
# Lr.Store.commit). Rust reads the facts (a file's length and the index of
# its last newline; which directory entries it made durable) and does the
# steps; the laws below refine the model above. Every input is free: any
# file, any facts, fsync on or off, any number of sidecar files with any
# durability, any commits, any crash point.
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
#     main.jsonl's entry is not durable, then the ack: nothing else, in
#     this order; an open's plan is (fsync) the flush of the parent
#     directory.
# R4: the entry answers each request Rust writes with the spelling of the
#     rule's decision, and the wire's error form to every other input; a
#     refused step keeps the stepper's state.

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

# LAW log_open_refuses_odd_facts (R1): a newline at or past the end of a file is no fact of a
# file: the open refuses it
# EXCLUDES: a cut past the end of the file read from facts that cannot be
law log_open_refuses_odd_facts:
  for +len: Nat
  for +i: Nat
  for past: {Nat.is_lt(i, len) == False{} : Bool}
  {Lr.tail(len, Some{i}) == Lr.Odd{} : Lr.Tail}

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
  +o = Lr.Store.open(True{})
  log_tag(log_acts(o), Nil{}, log_plan(cs, log_st(o)))

# what the steps xs of a plan do to the model's storage s when the crash
# comes after the first p of them: each step is the model's step of the
# same name (a sidecar's append or flush is a step of a file the model
# does not hold); an Ack is no step of the file system: it follows the step
# before it
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

# the indexes of the sidecars ds, from i
def log_ixs(ds: List<&2, Bool>, +i: Nat) -> List<&2, Nat>:
  match ds:
    case Nil{}:
      Nil{}
    case d <> more:
      i <> log_ixs(more, 1n+i)

# an append, and a flush, of each sidecar index of ns
def log_appends(ns: List<&2, Nat>) -> List<&2, Lr.Act>:
  match ns:
    case Nil{}:
      Nil{}
    case n <> more:
      Lr.AppendSide{n} <> log_appends(more)

def log_flushes(ns: List<&2, Nat>) -> List<&2, Lr.Act>:
  match ns:
    case Nil{}:
      Nil{}
    case n <> more:
      Lr.FlushSide{n} <> log_flushes(more)

# a flush of the storage directory when need
def log_dir(need: Bool) -> List<&2, Lr.Act>:
  match need:
    case True{}:
      [Lr.FlushDir{}]
    case False{}:
      Nil{}

# some entry of ds is not durable
def log_fresh(ds: List<&2, Bool>) -> Bool:
  match ds:
    case Nil{}:
      False{}
    case d <> more:
      Bool.or(Bool.not(d), log_fresh(more))

# the plan of a commit of the storage Store{fsync, main} whose sidecar
# files have the durable entries ds
def log_commit_spec(fsync: Bool, main: Bool, +ds: List<&2, Bool>) -> Lr.Plan:
  match fsync:
    case False{}:
      Lr.Plan{Lr.Store{False{}, main}, List.append(&2, Lr.Act, log_appends(log_ixs(ds, 0n)), [Lr.AppendMain{}, Lr.Ack{}])}
    case True{}:
      Lr.Plan{Lr.Store{True{}, True{}}, List.append(&2, Lr.Act, log_appends(log_ixs(ds, 0n)), List.append(&2, Lr.Act, log_flushes(log_ixs(ds, 0n)), List.append(&2, Lr.Act, log_dir(log_fresh(ds)), List.append(&2, Lr.Act, [Lr.AppendMain{}, Lr.FlushMain{}], List.append(&2, Lr.Act, log_dir(Bool.not(main)), [Lr.Ack{}])))))}

# the plan of an open
def log_open_spec(fsync: Bool) -> Lr.Plan:
  match fsync:
    case True{}:
      Lr.Plan{Lr.Store{True{}, False{}}, [Lr.FlushParent{}]}
    case False{}:
      Lr.Plan{Lr.Store{False{}, False{}}, Nil{}}

# LAW log_commit_plan (R3): every commit's plan, for every storage and every sidecar
# list: its records (each sidecar once, in order), then with fsync their
# flushes and a directory flush when a sidecar's entry is not durable,
# then its marker, then with fsync its flush and a directory flush when
# main.jsonl's entry is not durable, then the ack; with fsync main.jsonl's
# entry is durable after it
# EXCLUDES: a marker before a record or before a flush it depends on, a
#   missing or extra flush, a directory flush skipped for a new entry or
#   done for none, a sidecar skipped, doubled or misnumbered, an ack before
#   the last step, main.jsonl's entry forgotten or assumed durable
law log_commit_plan:
  for fsync: Bool
  for main: Bool
  for +ds: List<&2, Bool>
  {Lr.Store.commit(Lr.Store{fsync, main}, ds) == log_commit_spec(fsync, main, ds) : Lr.Plan}

# LAW log_open_plan (R3): an open's plan: with fsync the flush of the storage directory's
# parent, and main.jsonl's entry not yet durable
# EXCLUDES: an fsync storage whose own directory entry a power loss drops,
#   a first commit that skips the directory flush of main.jsonl
law log_open_plan:
  for fsync: Bool
  {Lr.Store.open(fsync) == log_open_spec(fsync) : Lr.Plan}

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

# LAW log_ffi_reads_only_requests (R4): an input the entry answers with no error form is the
# spelling of the facts of a file
# EXCLUDES: a default decision for malformed input, an unknown Maybe tag
#   read as a value, input left over ignored
law log_ffi_reads_only_requests:
  for +s: String
  for ok: {LawsBase.wire_opens_err(FLg.ffi(s)) == False{} : Bool}
  exs len: Nat
  exs last: Maybe<&2, Nat>
  {s == log_spell_req(len, last) : String}

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

# LAW log_stepper_open (R4): the stepper opens fsync, as Rust writes it, with the open's
# plan: its storage and the spelling of its steps
# EXCLUDES: a stepper that answers or keeps anything but the rule's plan
law log_stepper_open:
  for fsync: Bool
  {FLg.open(Wr.put_bool(fsync, "")) == log_answer(Lr.Store.open(fsync)) : FLg.St & String}

# LAW log_stepper_open_reads_only_a_bool (R4): an open the stepper answers with no error form
# reads a Bool and nothing else
# EXCLUDES: a default fsync for malformed input, input left over ignored
law log_stepper_open_reads_only_a_bool:
  for +s: String
  for ok: {LawsBase.wire_opens_err(log_reply(FLg.open(s))) == False{} : Bool}
  exs fsync: Bool
  {s == Wr.put_bool(fsync, "") : String}

# LAW log_stepper_open_refused_shuts (R4): a refused open opens no storage
# EXCLUDES: a stepper that plans commits after a malformed open
law log_stepper_open_refused_shuts:
  for +s: String
  for no: {LawsBase.wire_opens_err(log_reply(FLg.open(s))) == True{} : Bool}
  {log_state(FLg.open(s)) == FLg.Shut{} : FLg.St}

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

# LAW log_stepper_reads_only_commits (R4): an event the stepper answers with no error form is
# the spelling of a commit's sidecar entries
# EXCLUDES: a default plan for malformed input, input left over ignored
law log_stepper_reads_only_commits:
  for +st: FLg.St
  for +s: String
  for ok: {LawsBase.wire_opens_err(log_reply(FLg.step(st, s))) == False{} : Bool}
  exs ds: List<&2, Bool>
  {s == log_spell_sides(ds) : String}

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
# fsync open, an open without fsync, a first commit with no sidecar, a
# commit with a durable and a new sidecar, a commit without fsync, a
# malformed commit, a malformed open, a commit after it
# EXCLUDES: a request or reply format other than WIRE.md's (Bools as T and
#   F, the act tags, the sidecar indexes)
law log_stepper_example:
  {[log_reply(FLg.open("T")), log_reply(FLg.open("F")), log_reply(FLg.step(FLg.Running{Lr.Store{True{}, False{}}}, "0,")), log_reply(FLg.step(FLg.Running{Lr.Store{True{}, True{}}}, "2,TF")), log_reply(FLg.step(FLg.Running{Lr.Store{False{}, False{}}}, "1,F")), log_reply(FLg.step(FLg.Running{Lr.Store{True{}, True{}}}, "1,X")), log_reply(FLg.open("X")), log_reply(FLg.step(FLg.Shut{}, "0,"))] == ["1,0,", "0,", "4,4,5,3,6,", "8,1,0,1,1,2,0,2,1,3,4,5,6,", "3,1,0,4,6,", Wr.err("log: malformed commit"), Wr.err("log: malformed open"), Wr.err("log: the open was refused")] : List<&2, String>}
