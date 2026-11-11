# eukhe: the laws of area launcher

import Base
import ../bend/launcher.bend as La
import ../bend/ffi_launcher.bend as FLa
import ../bend/wire.bend as Wr
import ./base.bend as LawsBase

# ---- launcher ----

# A daemon replacement: the idle shutdown and the adoption of live
# workers. The decisions Rust asks for (a run start at a worker's gate, a
# worker's quiesce, the supervisor's commit of an idle shutdown, the
# adoption verdict) run as bend/launcher.bend (`admits`, `quiesce`,
# `quiesce.answer`, `commits`, `adoption`) through the entry
# bend/ffi_launcher.bend; the same gate rules drive the model's whole
# replacement (`run`, `step`), on which the idle shutdown is proven safe.
# PROOF.bend proves the laws (as Launcher.<law>) with the lemmas of
# proof/launcher/.
#
# Requirements (inferred from crates/eukhe-daemon/src/work_gate.rs, its
# module doc and test `the_replacement_decisions_come_from_the_compiled_core`,
# and supervisor/adoption.rs `adoption_verdict`):
# A1: a run starts only at an open gate (`WorkGate::admits`); a closed gate
#   refuses it.
# A2: a quiesce of an idle worker closes its gate and answers quiesced; a
#   busy worker answers busy and keeps its gate as it was
#   (`WorkGate::quiesce`).
# A3: a release opens the gate again (`WorkGate::release`); a run's end
#   leaves its worker idle.
# A4: the supervisor commits an idle shutdown, which stops every worker,
#   only when every worker quiesced (`idle_shutdown_commits`); a stop
#   aborts every run it finds.
# A5: an idle shutdown never aborts a running run, in any order of run
#   starts, run ends, quiesces, releases and commits on any workers (the
#   two-phase protocol of work_gate.rs).
# A6: a supervisor adopts a worker exactly when the worker reports the
#   supervisor's build; a worker that reports none is replaced (`adopts`).
# A7: the entry answers every request Rust writes with the spelled
#   decision, reads nothing else (an answer that is no error form means
#   the input was one request, spelled, whose numbers fit the wire), and
#   every error it answers is the one form `E launcher: malformed request`.
# A8: the model's replacement starts on the given workers with every gate
#   open, no run aborted, serving; it takes each operation in order, one
#   step each; an operation on a worker changes no other worker; a stopped
#   daemon stays as it stopped.

# Terms
# -----

def la_ws(s: La.St) -> List<&2, La.Wk>:
  match s:
    case La.St{ws, a, d}:
      ws

def la_stopped(s: La.St) -> Bool:
  match s:
    case La.St{ws, a, d}:
      d

def la_aborted(s: La.St) -> Nat:
  match s:
    case La.St{ws, a, d}:
      a

# The idle shutdown
# -----------------

# LAW idle_shutdown_never_aborts (A5): an idle shutdown never aborts a run, in any order of prompts, run
# ends, quiesces, releases and commits on any workers: the state's count of
# aborted runs stays 0
law idle_shutdown_never_aborts:
  for +bs: List<&2, Bool>
  for +ops: List<&2, La.Op>
  {la_aborted(La.run(bs, ops)) == 0n : Nat}

# a worker with run b and an open gate, where bs has b
def la_open_at(m: Maybe<&2, Bool>) -> Maybe<&2, La.Wk>:
  match m:
    case None{}:
      None{}
    case Some{b}:
      Some{La.Wk{b, False{}}}

# LAW launcher_run_starts_serving (A8): the replacement started on workers with runs bs, before any
# operation, serves, has aborted no run, and its i-th worker has the i-th run
# of bs and an open gate (no i-th worker when bs has no i-th run)
# EXCLUDES: a start already stopped (every later law then vacuous), a start
#   with a closed gate or an aborted count, workers lost, added or reordered
law launcher_run_starts_serving:
  for +bs: List<&2, Bool>
  for i: Nat
  {la_stopped(La.run(bs, [])) == False{} : Bool} & {la_aborted(La.run(bs, [])) == 0n : Nat} & {List.get(&2, La.Wk, la_ws(La.run(bs, [])), i) == la_open_at(List.get(&2, Bool, bs, i)) : Maybe<&2, La.Wk>}

# LAW launcher_run_steps (A8): the replacement after ops then op is one step on op from the
# replacement after ops
# EXCLUDES: a run that drops, repeats or reorders operations, or stops
#   taking them before the end
law launcher_run_steps:
  for +bs: List<&2, Bool>
  for +ops: List<&2, La.Op>
  for +op: La.Op
  {La.run(bs, List.append(&2, La.Op, ops, [op])) == La.step(La.run(bs, ops), op) : La.St}

# LAW launcher_stopped_is_final (A8): once the replacement stopped, no later operation changes it
# EXCLUDES: a daemon that serves again after its stop, a second stop that
#   counts more aborted runs
law launcher_stopped_is_final:
  for +bs: List<&2, Bool>
  for +ops: List<&2, La.Op>
  for more: List<&2, La.Op>
  for stopped: {la_stopped(La.run(bs, ops)) == True{} : Bool}
  {La.run(bs, List.append(&2, La.Op, ops, more)) == La.run(bs, ops) : La.St}

# The gate, operation by operation (on a serving daemon)
# ------------------------------------------------------

# LAW launcher_prompt_starts_at_open_gate (A1): a run start on worker i whose gate is open starts its run
# EXCLUDES: a run start refused at an open gate (no run ever starts, and
#   idle_shutdown_never_aborts holds vacuously)
law launcher_prompt_starts_at_open_gate:
  for ws: List<&2, La.Wk>
  for a: Nat
  for i: Nat
  for b: Bool
  for at: {List.get(&2, La.Wk, ws, i) == Some{La.Wk{b, False{}}} : Maybe<&2, La.Wk>}
  {List.get(&2, La.Wk, la_ws(La.step(La.St{ws, a, False{}}, La.Prompt{i})), i) == Some{La.Wk{True{}, False{}}} : Maybe<&2, La.Wk>}

# LAW launcher_prompt_waits_at_closed_gate (A1): a run start on worker i whose gate is closed changes it not
# EXCLUDES: a run started at a closed gate, a gate a run start reopens
law launcher_prompt_waits_at_closed_gate:
  for ws: List<&2, La.Wk>
  for a: Nat
  for i: Nat
  for b: Bool
  for at: {List.get(&2, La.Wk, ws, i) == Some{La.Wk{b, True{}}} : Maybe<&2, La.Wk>}
  {List.get(&2, La.Wk, la_ws(La.step(La.St{ws, a, False{}}, La.Prompt{i})), i) == Some{La.Wk{b, True{}}} : Maybe<&2, La.Wk>}

# LAW launcher_quiesce_closes_idle (A2): a quiesce of idle worker i closes its gate
# EXCLUDES: an idle worker left open (a run may start under the stop), a
#   quiesce that never closes a gate (no idle shutdown ever commits)
law launcher_quiesce_closes_idle:
  for ws: List<&2, La.Wk>
  for a: Nat
  for i: Nat
  for c: Bool
  for at: {List.get(&2, La.Wk, ws, i) == Some{La.Wk{False{}, c}} : Maybe<&2, La.Wk>}
  {List.get(&2, La.Wk, la_ws(La.step(La.St{ws, a, False{}}, La.Quiesce{i})), i) == Some{La.Wk{False{}, True{}}} : Maybe<&2, La.Wk>}

# LAW launcher_quiesce_keeps_busy (A2): a quiesce of busy worker i changes it not: its run goes on, its
# gate stays as it was
# EXCLUDES: a busy worker's gate closed (the commit then stops its run), a
#   run dropped by a quiesce
law launcher_quiesce_keeps_busy:
  for ws: List<&2, La.Wk>
  for a: Nat
  for i: Nat
  for c: Bool
  for at: {List.get(&2, La.Wk, ws, i) == Some{La.Wk{True{}, c}} : Maybe<&2, La.Wk>}
  {List.get(&2, La.Wk, la_ws(La.step(La.St{ws, a, False{}}, La.Quiesce{i})), i) == Some{La.Wk{True{}, c}} : Maybe<&2, La.Wk>}

# LAW launcher_finish_ends_run (A3): a run's end leaves worker i idle, its gate as it was
# EXCLUDES: a run that never ends (no idle shutdown after any run), a gate
#   a run's end changes
law launcher_finish_ends_run:
  for ws: List<&2, La.Wk>
  for a: Nat
  for i: Nat
  for b: Bool
  for c: Bool
  for at: {List.get(&2, La.Wk, ws, i) == Some{La.Wk{b, c}} : Maybe<&2, La.Wk>}
  {List.get(&2, La.Wk, la_ws(La.step(La.St{ws, a, False{}}, La.Finish{i})), i) == Some{La.Wk{False{}, c}} : Maybe<&2, La.Wk>}

# LAW launcher_release_opens_gate (A3): a release opens worker i's gate, its run as it was
# EXCLUDES: a gate left closed after a refused shutdown (the worker never
#   starts a run again), a run a release changes
law launcher_release_opens_gate:
  for ws: List<&2, La.Wk>
  for a: Nat
  for i: Nat
  for b: Bool
  for c: Bool
  for at: {List.get(&2, La.Wk, ws, i) == Some{La.Wk{b, c}} : Maybe<&2, La.Wk>}
  {List.get(&2, La.Wk, la_ws(La.step(La.St{ws, a, False{}}, La.Release{i})), i) == Some{La.Wk{b, False{}}} : Maybe<&2, La.Wk>}

# the worker an operation is on (a commit: none)
def la_target(op: La.Op) -> Maybe<&2, Nat>:
  match op:
    case La.Prompt{i}:
      Some{i}
    case La.Finish{i}:
      Some{i}
    case La.Quiesce{i}:
      Some{i}
    case La.Release{i}:
      Some{i}
    case La.Commit{}:
      None{}

# LAW launcher_op_leaves_others (A8): an operation on worker i of a serving daemon leaves every other
# worker j as it was
# EXCLUDES: a run start, run end, quiesce or release that changes another
#   worker's run or gate
law launcher_op_leaves_others:
  for ws: List<&2, La.Wk>
  for a: Nat
  for op: La.Op
  for +i: Nat
  for +j: Nat
  for on: {la_target(op) == Some{i} : Maybe<&2, Nat>}
  for other: {Nat.is_eq(i, j) == False{} : Bool}
  {List.get(&2, La.Wk, la_ws(La.step(La.St{ws, a, False{}}, op)), j) == List.get(&2, La.Wk, ws, j) : Maybe<&2, La.Wk>}

# LAW launcher_op_keeps_workers (A8): no operation adds or drops a worker
# EXCLUDES: an operation on a worker past the last that adds one, a
#   worker dropped
law launcher_op_keeps_workers:
  for +ws: List<&2, La.Wk>
  for a: Nat
  for op: La.Op
  {List.length(&2, La.Wk, la_ws(La.step(La.St{ws, a, False{}}, op))) == List.length(&2, La.Wk, ws) : Nat}

# LAW launcher_op_keeps_serving (A4, A8): a run start, run end, quiesce or release on any worker of a
# serving daemon keeps it serving and aborts no run: only a commit stops it
# EXCLUDES: a run start (or run end, quiesce, release) that stops the daemon
#   or counts a run as aborted, though no commit was made and no worker
#   quiesced
law launcher_op_keeps_serving:
  for ws: List<&2, La.Wk>
  for a: Nat
  for op: La.Op
  for +i: Nat
  for on: {la_target(op) == Some{i} : Maybe<&2, Nat>}
  {la_stopped(La.step(La.St{ws, a, False{}}, op)) == False{} : Bool} & {la_aborted(La.step(La.St{ws, a, False{}}, op)) == a : Nat}

# The commit
# ----------

# LAW launcher_commit_waits_open_gate (A4): a commit while some worker's gate is open changes nothing:
# no stop, no run aborted
# EXCLUDES: an idle shutdown committed before every worker quiesced (a run
#   may start between the answers and the stop)
law launcher_commit_waits_open_gate:
  for ws: List<&2, La.Wk>
  for a: Nat
  for j: Nat
  for b: Bool
  for at: {List.get(&2, La.Wk, ws, j) == Some{La.Wk{b, False{}}} : Maybe<&2, La.Wk>}
  {La.step(La.St{ws, a, False{}}, La.Commit{}) == La.St{ws, a, False{}} : La.St}

# workers with runs bs, every gate closed
def la_closed(bs: List<&2, Bool>) -> List<&2, La.Wk>:
  match bs:
    case Nil{}:
      Nil{}
    case b <> t:
      La.Wk{b, True{}} <> la_closed(t)

def la_id(b: Bool) -> Bool:
  b

# LAW launcher_commit_stops_closed (A4): a commit while every gate is closed stops the daemon, its
# workers as they were, and counts as aborted every run it finds (the runs
# of bs, counted by a filter)
# EXCLUDES: a commit that never stops (no idle shutdown ever happens), a
#   stop that counts no run or another number (idle_shutdown_never_aborts
#   then reads a false count), workers changed by the stop
law launcher_commit_stops_closed:
  for +bs: List<&2, Bool>
  for a: Nat
  {La.step(La.St{la_closed(bs), a, False{}}, La.Commit{}) == La.St{la_closed(bs), Nat.add(List.length(&2, Bool, List.filter(~Bool, ~la_id, bs)), a), True{}} : La.St}

# Adoption
# --------

# LAW adopt_same_build (A6): a supervisor adopts a worker only when the worker reports the
# supervisor's build
law adopt_same_build:
  for +sup: Nat
  for +w: Maybe<&2, Nat>
  for adopted: {La.adoption(sup, w) == La.Adopt{} : La.Adoption}
  {w == Some{sup} : Maybe<&2, Nat>}

# LAW launcher_adopt_own_build (A6): a supervisor adopts every worker that reports its own build
# EXCLUDES: a supervisor that replaces its own build's workers (with
#   adopt_same_build: the verdict is adopt exactly for the own build)
law launcher_adopt_own_build:
  for +sup: Nat
  {La.adoption(sup, Some{sup}) == La.Adopt{} : La.Adoption}

# The entry Rust calls
# --------------------
# The spellers below are the wire grammar of bend/ffi_launcher.bend's
# header (crates/eukhe-bend/WIRE.md), written with the wire primitives
# alone (laws/wire.bend proves them): the requests work_gate.rs writes and
# the replies it reads. Rust numbers the builds of an adoption by
# equality: 0 the supervisor's build, 1 another.

# the gate after a quiesce: a busy worker's gate stays as it was, an idle
# worker's closes
def closed_after(busy: Bool, closed: Bool) -> Bool:
  match busy:
    case True{}:
      closed
    case False{}:
      True{}

# every answer is quiesced
def all_quiesced(xs: List<&2, Bool>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case a <> t:
      Bool.and(a, all_quiesced(t))

# the adoption of a worker that reports build w: adopt (0) only the
# supervisor's build, else replace (1)
def adopt_spec(w: Maybe<&2, Nat>) -> Nat:
  match w:
    case None{}:
      1n
    case Some{b}:
      match b:
        case 0n:
          0n
        case 1n+p:
          1n

def spell_bools(xs: List<&2, Bool>, rest: String) -> String:
  match xs:
    case Nil{}:
      rest
    case a <> t:
      Wr.put_bool(a, spell_bools(t, rest))

# the request Rust writes for a
def spell_ask(a: La.Ask) -> String:
  match a:
    case La.AskPrompt{c}:
      Wr.put_nat(0n, Wr.put_bool(c, ""))
    case La.AskQuiesce{b, c}:
      Wr.put_nat(1n, Wr.put_bool(b, Wr.put_bool(c, "")))
    case La.AskCommit{+xs}:
      Wr.put_nat(2n, Wr.put_nat(List.length(&2, Bool, xs), spell_bools(xs, "")))
    case La.AskAdopt{w}:
      match w:
        case None{}:
          Wr.put_nat(3n, Wr.put_nat(0n, ""))
        case Some{n}:
          Wr.put_nat(3n, Wr.put_nat(1n, Wr.put_nat(n, "")))

# every number of a fits the wire
def ask_fits(a: La.Ask) -> Bool:
  match a:
    case La.AskPrompt{c}:
      True{}
    case La.AskQuiesce{b, c}:
      True{}
    case La.AskCommit{xs}:
      LawsBase.wire_fits(List.length(&2, Bool, xs))
    case La.AskAdopt{w}:
      match w:
        case None{}:
          True{}
        case Some{n}:
          LawsBase.wire_fits(n)

# the reply to a: a run starts only at an open gate; a quiesce answers the
# gate after it, then whether the worker quiesced (it held no work); the
# commit happens only when every worker quiesced; the adoption's verdict
def spell_answer(a: La.Ask) -> String:
  match a:
    case La.AskPrompt{c}:
      Wr.put_bool(Bool.not(c), "")
    case La.AskQuiesce{+b, c}:
      Wr.put_bool(closed_after(b, c), Wr.put_bool(Bool.not(b), ""))
    case La.AskCommit{xs}:
      Wr.put_bool(all_quiesced(xs), "")
    case La.AskAdopt{w}:
      Wr.put_nat(adopt_spec(w), "")

# LAW launcher_ffi_answers (A1, A2, A4, A6, A7): on every request Rust writes, the entry answers: a run starts only at an open gate; a quiesce closes the gate of a worker with no work and answers quiesced, and leaves a busy worker's gate as it was with the answer busy; the supervisor commits an idle shutdown only when every worker quiesced; a worker is adopted only when it reports the supervisor's build
law launcher_ffi_answers:
  for +a: La.Ask
  for fits: {ask_fits(a) == True{} : Bool}
  {FLa.ffi(spell_ask(a)) == spell_answer(a) : String}

# LAW launcher_ffi_reads_only_requests (A7): an input the entry answers with no error form is the
# spelling of one request whose numbers fit the wire
# EXCLUDES: a default answer to malformed input, input left over ignored,
#   an unknown tag read as a request, a count or a build past the wire read
law launcher_ffi_reads_only_requests:
  for +s: String
  for ok: {LawsBase.wire_opens_err(FLa.ffi(s)) == False{} : Bool}
  exs a: La.Ask
  {s == spell_ask(a) : String} & {ask_fits(a) == True{} : Bool}

# LAW launcher_ffi_refuses_one_error (A7): every error the entry answers is exactly
# `E launcher: malformed request`
# EXCLUDES: an error text that varies with the input, a second error form
law launcher_ffi_refuses_one_error:
  for +s: String
  for bad: {LawsBase.wire_opens_err(FLa.ffi(s)) == True{} : Bool}
  {FLa.ffi(s) == Wr.err("launcher: malformed request") : String}

# LAW launcher_ffi_example (A7): anchor: the strings Rust sends: a run start at a closed gate, a quiesce of a busy worker at an open gate, a commit with one busy answer, the adoption of a worker of another build and of the supervisor's; input left over is refused
law launcher_ffi_example:
  {FLa.ffi("0,T") == "F" : String} &
  {FLa.ffi("1,TF") == "FF" : String} &
  {FLa.ffi("2,3,TFT") == "F" : String} &
  {FLa.ffi("3,1,1,") == "1," : String} &
  {FLa.ffi("3,1,0,") == "0," : String} &
  {LawsBase.wire_opens_err(FLa.ffi("0,TT")) == True{} : Bool}

# LAW launcher_closed_gate_waits_example (A1): anchor: an idle worker quiesced, then prompted, does not start the run
law launcher_closed_gate_waits_example:
  {La.run([False{}], [La.Quiesce{0n}, La.Prompt{0n}]) == La.St{[La.Wk{False{}, True{}}], 0n, False{}} : La.St}
