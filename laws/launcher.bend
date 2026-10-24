# eukhe: the laws of area launcher

import Base
import ../bend/launcher.bend as La
import ../bend/ffi_launcher.bend as FLa
import ../bend/wire.bend as Wr
import ./base.bend as LawsBase

# The orphan entry of the compiled core (bend/ffi_orphan.bend)

# LAW idle_shutdown_never_aborts: an idle shutdown never aborts a run, in any order of prompts, run
# ends, quiesces, releases and commits on any workers
law idle_shutdown_never_aborts:
  for +bs: List<&2, Bool>
  for +ops: List<&2, La.Op>
  {La.St.aborted(La.run(bs, ops)) == 0n : Nat}

# LAW adopt_same_build: a supervisor adopts a worker only when the worker reports the
# supervisor's build
law adopt_same_build:
  for +sup: Nat
  for +w: Maybe<&2, Nat>
  for adopted: {La.adoption(sup, w) == La.Adopt{} : La.Adoption}
  {w == Some{sup} : Maybe<&2, Nat>}

# The decisions exactly, and the entry Rust calls
# -----------------------------------------------
# A run start at a worker's gate, a worker's quiesce and the supervisor's
# commit (crates/eukhe-daemon/src/work_gate.rs `WorkGate`,
# `idle_shutdown_commits`) and the adoption verdict
# (`supervisor/adoption.rs` `adoption_verdict`) run as
# bend/launcher.bend through the entry bend/ffi_launcher.bend. The
# spellers and the reader below are the wire grammar of that entry
# written with the wire primitives alone (laws/wire.bend proves their
# round trips); they never call the entry's own codec. Rust numbers the
# builds of an adoption by equality, as `adoption` reads them: 0 the
# supervisor's build, 1 another.

# Terms
# -----

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

# Spellers

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

# Reader: the requests the entry accepts, read with the wire primitives

def read_prompt(r: Wr.Dec<Bool>) -> Wr.Dec<La.Ask>:
  match r:
    case Wr.Got{c, s}:
      Wr.Got{La.AskPrompt{c}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def read_quiesce.closed(b: Bool, r: Wr.Dec<Bool>) -> Wr.Dec<La.Ask>:
  match r:
    case Wr.Got{c, s}:
      Wr.Got{La.AskQuiesce{b, c}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def read_quiesce(r: Wr.Dec<Bool>) -> Wr.Dec<La.Ask>:
  match r:
    case Wr.Got{b, s}:
      read_quiesce.closed(b, Wr.get_bool(s))
    case Wr.Bad{}:
      Wr.Bad{}

def read_answers.cons(a: Bool, r: Wr.Dec<List<&2, Bool>>) -> Wr.Dec<List<&2, Bool>>:
  match r:
    case Wr.Got{xs, s}:
      Wr.Got{a <> xs, s}
    case Wr.Bad{}:
      Wr.Bad{}

# n more answers after the one cur answers
def read_answers(n: Nat, cur: Wr.Dec<Bool>) -> Wr.Dec<List<&2, Bool>>:
  match n:
    case 0n:
      match cur:
        case Wr.Got{a, s}:
          Wr.Got{[a], s}
        case Wr.Bad{}:
          Wr.Bad{}
    case 1n+m:
      match cur:
        case Wr.Got{a, s}:
          read_answers.cons(a, read_answers(m, Wr.get_bool(s)))
        case Wr.Bad{}:
          Wr.Bad{}

def read_commit.answers(r: Wr.Dec<List<&2, Bool>>) -> Wr.Dec<La.Ask>:
  match r:
    case Wr.Got{xs, s}:
      Wr.Got{La.AskCommit{xs}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def read_commit(r: Wr.Dec<Nat>) -> Wr.Dec<La.Ask>:
  match r:
    case Wr.Got{n, s}:
      match n:
        case 0n:
          Wr.Got{La.AskCommit{Nil{}}, s}
        case 1n+m:
          read_commit.answers(read_answers(m, Wr.get_bool(s)))
    case Wr.Bad{}:
      Wr.Bad{}

def read_adopt.some(r: Wr.Dec<Nat>) -> Wr.Dec<La.Ask>:
  match r:
    case Wr.Got{b, s}:
      Wr.Got{La.AskAdopt{Some{b}}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def read_adopt.tag(t: Nat, s: String) -> Wr.Dec<La.Ask>:
  match t:
    case 0n:
      Wr.Got{La.AskAdopt{None{}}, s}
    case 1n:
      read_adopt.some(Wr.get_nat(s))
    case 2n+p:
      Wr.Bad{}

def read_adopt(r: Wr.Dec<Nat>) -> Wr.Dec<La.Ask>:
  match r:
    case Wr.Got{t, s}:
      read_adopt.tag(t, s)
    case Wr.Bad{}:
      Wr.Bad{}

def read_ask.tag(t: Nat, s: String) -> Wr.Dec<La.Ask>:
  match t:
    case 0n:
      read_prompt(Wr.get_bool(s))
    case 1n:
      read_quiesce(Wr.get_bool(s))
    case 2n:
      read_commit(Wr.get_nat(s))
    case 3n:
      read_adopt(Wr.get_nat(s))
    case 4n+p:
      Wr.Bad{}

def read_ask.go(r: Wr.Dec<Nat>) -> Wr.Dec<La.Ask>:
  match r:
    case Wr.Got{t, s}:
      read_ask.tag(t, s)
    case Wr.Bad{}:
      Wr.Bad{}

def read_ask.end(whole: Bool, a: La.Ask) -> Maybe<&2, La.Ask>:
  match whole:
    case True{}:
      Some{a}
    case False{}:
      None{}

def read_ask.whole(r: Wr.Dec<La.Ask>) -> Maybe<&2, La.Ask>:
  match r:
    case Wr.Got{a, s}:
      read_ask.end(Wr.end(s), a)
    case Wr.Bad{}:
      None{}

# the request s is, when s is exactly one request
def read_ask(s: String) -> Maybe<&2, La.Ask>:
  read_ask.whole(read_ask.go(Wr.get_nat(s)))

# Laws
# ----

# LAW launcher_ffi_answers: on every request Rust writes, the entry answers: a run starts only at an open gate; a quiesce closes the gate of a worker with no work and answers quiesced, and leaves a busy worker's gate as it was with the answer busy; the supervisor commits an idle shutdown only when every worker quiesced; a worker is adopted only when it reports the supervisor's build
law launcher_ffi_answers:
  for +a: La.Ask
  for fits: {ask_fits(a) == True{} : Bool}
  {FLa.ffi(spell_ask(a)) == spell_answer(a) : String}

# LAW launcher_ffi_malformed: every input that is not exactly one request gets the error form
law launcher_ffi_malformed:
  for +s: String
  for no: {read_ask(s) == None{} : Maybe<&2, La.Ask>}
  {LawsBase.wire_opens_err(FLa.ffi(s)) == True{} : Bool}

# LAW launcher_ffi_example: anchor: the strings Rust sends: a run start at a closed gate, a quiesce of a busy worker at an open gate, a commit with one busy answer, the adoption of a worker of another build and of the supervisor's; input left over is refused
law launcher_ffi_example:
  {FLa.ffi("0,T") == "F" : String} &
  {FLa.ffi("1,TF") == "FF" : String} &
  {FLa.ffi("2,3,TFT") == "F" : String} &
  {FLa.ffi("3,1,1,") == "1," : String} &
  {FLa.ffi("3,1,0,") == "0," : String} &
  {read_ask("0,TT") == None{} : Maybe<&2, La.Ask>} &
  {LawsBase.wire_opens_err(FLa.ffi("0,TT")) == True{} : Bool}

# the runs a stop finds: one per worker with a run
def busy_spec(ws: List<&2, La.Wk>) -> Nat:
  match ws:
    case Nil{}:
      0n
    case La.Wk{b, c} <> t:
      match b:
        case True{}:
          Nat.add(1n, busy_spec(t))
        case False{}:
          busy_spec(t)

# LAW launcher_stop_counts_runs: a stop counts as aborted exactly the runs it finds, one per worker with a run (so idle_shutdown_never_aborts reads a true count)
law launcher_stop_counts_runs:
  for ws: List<&2, La.Wk>
  {La.busy_count(ws) == busy_spec(ws) : Nat}

# The whole replacement, step by step
# -----------------------------------
# idle_shutdown_never_aborts runs bend/launcher.bend's own simulation
# (`run`, `step`); this pins that simulation to the rule itself, so the
# law is about the gate the entry answers (a run starts only at an open
# gate, a quiesce closes only an idle worker's gate, ...).

# what an operation does to its worker (a commit touches none)
def wk_spec(op: La.Op, w: La.Wk) -> La.Wk:
  match op:
    case La.Prompt{i}:
      match w:
        case La.Wk{b, c}:
          match c:
            case True{}:
              La.Wk{b, True{}}
            case False{}:
              La.Wk{True{}, False{}}
    case La.Finish{i}:
      match w:
        case La.Wk{b, c}:
          La.Wk{False{}, c}
    case La.Quiesce{i}:
      match w:
        case La.Wk{b, c}:
          match b:
            case True{}:
              La.Wk{True{}, c}
            case False{}:
              La.Wk{False{}, True{}}
    case La.Release{i}:
      match w:
        case La.Wk{b, c}:
          La.Wk{b, False{}}
    case La.Commit{}:
      w

# the workers after op on worker i (no worker i: unchanged)
def at_spec(op: La.Op, i: Nat, ws: List<&2, La.Wk>) -> List<&2, La.Wk>:
  match i:
    case 0n:
      match ws:
        case Nil{}:
          Nil{}
        case w <> t:
          wk_spec(op, w) <> t
    case 1n+j:
      match ws:
        case Nil{}:
          Nil{}
        case w <> t:
          w <> at_spec(op, j, t)

# every gate is closed
def closed_spec(ws: List<&2, La.Wk>) -> Bool:
  match ws:
    case Nil{}:
      True{}
    case La.Wk{b, c} <> t:
      Bool.and(c, closed_spec(t))

def commit_spec(ok: Bool, +ws: List<&2, La.Wk>, a: Nat) -> La.St:
  match ok:
    case True{}:
      La.St{ws, Nat.add(busy_spec(ws), a), True{}}
    case False{}:
      La.St{ws, a, False{}}

# one step: a stopped daemon changes nothing; a commit stops it only when
# every gate is closed, and aborts every run it finds; any other operation
# changes its worker as wk_spec says
def step_spec(s: La.St, op: La.Op) -> La.St:
  match s:
    case La.St{+ws, a, d}:
      match d:
        case True{}:
          La.St{ws, a, True{}}
        case False{}:
          match op:
            case La.Prompt{+i}:
              La.St{at_spec(La.Prompt{i}, i, ws), a, False{}}
            case La.Finish{+i}:
              La.St{at_spec(La.Finish{i}, i, ws), a, False{}}
            case La.Quiesce{+i}:
              La.St{at_spec(La.Quiesce{i}, i, ws), a, False{}}
            case La.Release{+i}:
              La.St{at_spec(La.Release{i}, i, ws), a, False{}}
            case La.Commit{}:
              commit_spec(closed_spec(ws), ws, a)

# LAW launcher_step_exact: each step of the replacement's simulation is the rule: a run starts only at an open gate, a run end clears the run, a quiesce closes an idle worker's gate and leaves a busy one's as it was, a release opens the gate, a commit stops the daemon only when every gate is closed (aborting the runs it finds), a stopped daemon changes nothing, and no other worker changes
law launcher_step_exact:
  for +s: La.St
  for +op: La.Op
  {La.step(s, op) == step_spec(s, op) : La.St}

# LAW launcher_closed_gate_waits_example: anchor: an idle worker quiesced, then prompted, does not start the run
law launcher_closed_gate_waits_example:
  {La.run([False{}], [La.Quiesce{0n}, La.Prompt{0n}]) == La.St{[La.Wk{False{}, True{}}], 0n, False{}} : La.St}

# LAW launcher_ffi_malformed_exact: every input that is not exactly one request gets exactly the error form 'E ', then "launcher: malformed request" (the text Rust's Reader reports)
law launcher_ffi_malformed_exact:
  for +s: String
  for no: {read_ask(s) == None{} : Maybe<&2, La.Ask>}
  {FLa.ffi(s) == SCon{'E', SCon{' ', "launcher: malformed request"}} : String}

def adoption_spec.pick(same: Bool) -> La.Adoption:
  match same:
    case True{}:
      La.Adopt{}
    case False{}:
      La.Replace{}

# a worker of no build is replaced; one of build b is adopted exactly when
# b is the supervisor's
def adoption_spec(+sup: Nat, w: Maybe<&2, Nat>) -> La.Adoption:
  match w:
    case None{}:
      La.Replace{}
    case Some{b}:
      adoption_spec.pick(Nat.is_eq(b, sup))

# LAW launcher_adoption_exact: for every supervisor build, a worker that reports no build is replaced, and one that reports a build is adopted exactly when it is the supervisor's (adopt_same_build is one direction of this)
law launcher_adoption_exact:
  for +sup: Nat
  for w: Maybe<&2, Nat>
  {La.adoption(sup, w) == adoption_spec(sup, w) : La.Adoption}
