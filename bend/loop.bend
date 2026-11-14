# loop: the decisions of `/loop` (spec/README.md L1-L9). A loop re-sends
# one prompt after every turn until its stop condition is confirmed, a
# bound is reached, or the user stops it. It
# runs as the compiled Bend core (entry bend/ffi_loop.bend, a plain call:
# Rust keeps the state in the session's durable storage and sends it with
# each event). Rust gathers the facts (the clock, the exit status of the
# condition command, whether the session is busy, whether the budget still
# funds a turn), does the IO each answer names, and decides nothing.
#
# One loop per session. Its life: Off -> (Enter) -> Armed or Turn -> ...
# -> Ended. A turn of the loop is an iteration; `iter` numbers them from 1.
# After a turn settles the loop runs the condition command (Judging) and
# reads its evidence; only then, and only inside every bound, the next
# iteration starts. Pure: no IO, no @unsafe.

import Base

# The condition: a shell command whose exit status is the evidence.
# Until: the loop stops once the command succeeds. While: the loop stops
# once the command fails (exits nonzero, other than 126 or 127).
type Cond is Data:
  NoCond{}
  Until{cmd: String}
  While{cmd: String}

# What one run of the condition command showed: its exit status; no exit
# status (killed by a signal); the deadline passed; it could not start; the
# run was cancelled before it answered.
type Evid is Data:
  Exited{code: Nat}
  NoStatus{}
  TimedOut{}
  SpawnFailed{}
  Cancelled{}

# What the evidence says of the loop's stop condition: it holds; it does
# not hold yet; the check itself is broken (never read as either); nothing
# was learned.
type Verdict is Data:
  Confirmed{}
  Refuted{}
  Broken{}
  Unjudged{}

# Why a loop ended: its stop condition was confirmed; the check broke; the
# iteration count is used up; the time is used up; too many turns failed in
# a row; the budget funds no further turn; the user stopped it.
type End is Data:
  Satisfied{}
  CheckBroke{}
  OutOfTurns{}
  OutOfTime{}
  TurnsFailed{}
  OutOfBudget{}
  Stopped{}

# Off: no loop. Armed: on, waiting for the prompt to repeat. Turn: an
# iteration's turn is in flight. Judging: the turn settled, the condition
# command runs. Paused: suspended by the user, waiting for a new prompt.
# Ended: over, with its reason.
type Phase is Data:
  Off{}
  Armed{}
  Turn{}
  Judging{}
  Paused{}
  Ended{why: End}

# The bound given at the start: none; a count of automatic iterations; a
# span of milliseconds from the start.
type Limit is Data:
  NoLimit{}
  Count{n: Nat}
  Span{ms: Nat}

# How a turn settled: it ran to its end; it failed; it did not run to its
# end (refused, consumed locally, or interrupted by the user).
type Out is Data:
  Ran{}
  Errored{}
  Halted{}

# The last evidence read: none yet; ev, read after iteration `at`.
type Last is Data:
  NoCheck{}
  Check{at: Nat, ev: Evid}

# phase; the iterations started; the automatic iterations left (None: no
# count); the deadline in ms (None: no span); the condition; the prompt
# repeated (empty while armed or paused); the turns that failed in a row;
# the last evidence read
type St is Data:
  St{phase: Phase, iter: Nat, left: Maybe<&2, Nat>, deadline: Maybe<&2, Nat>, cond: Cond, body: String, fails: Nat, last: Last}

# Enter: `/loop` with its bound, its condition, its inline prompt and the
# clock: it starts a loop, or ends the one that is on. Stop: `/loop --stop`.
# Abort: the user's interrupt (Esc). Prompt: the user sent a prompt that
# starts a turn. Settled: iteration `iter`'s turn settled (blocked: the
# session is not idle: queued input or unsettled work is still ahead); the
# clock; funded: the budget funds one more turn. Judged: the condition
# command ran after iteration `iter`, with the same facts. Restart: the
# pending work is taken up again (a worker that started again and read
# this state from storage).
type Ev is Data:
  Enter{limit: Limit, cond: Cond, prompt: Maybe<&2, String>, now: Nat}
  Stop{}
  Abort{}
  Prompt{text: String}
  Settled{iter: Nat, out: Out, blocked: Bool, now: Nat, funded: Bool}
  Judged{iter: Nat, ev: Evid, blocked: Bool, now: Nat, funded: Bool}
  Restart{}

# Rest: nothing to do. Submit: start iteration `iter` with this text.
# Adopt: the user's own prompt is iteration `iter`. Judge: run the
# condition command after iteration `iter`. Resume: iteration `iter`'s turn
# is the one in flight: continue it (send this text only if it never was
# sent). Report: the loop ended, tell why. Defer: ask again once the
# session is idle.
type Act is Data:
  Rest{}
  Submit{iter: Nat, text: String}
  Adopt{iter: Nat}
  Judge{iter: Nat}
  Resume{iter: Nat, text: String}
  Report{why: End}
  Defer{}

# The verdict
# -----------

# exit 126 (found, not executable) or 127 (not found): the shell could not
# run the command
def cannot_run(+code: Nat) -> Bool:
  Bool.or(Nat.is_eq(code, 126n), Nat.is_eq(code, 127n))

# the verdict of a nonzero exit: broken when the shell could not run the
# command, else v
def judge.nonzero(broke: Bool, v: Verdict) -> Verdict:
  match broke:
    case True{}:
      Broken{}
    case False{}:
      v

def judge.until(code: Nat) -> Verdict:
  match code:
    case 0n:
      Confirmed{}
    case 1n+k:
      judge.nonzero(cannot_run(1n+k), Refuted{})

def judge.while(code: Nat) -> Verdict:
  match code:
    case 0n:
      Refuted{}
    case 1n+k:
      judge.nonzero(cannot_run(1n+k), Confirmed{})

def judge.exit(until: Bool, code: Nat) -> Verdict:
  match until:
    case True{}:
      judge.until(code)
    case False{}:
      judge.while(code)

# what the evidence says of the stop condition of an `--until` (True) or a
# `--while` (False) loop
def judge(until: Bool, ev: Evid) -> Verdict:
  match ev:
    case Exited{code}:
      judge.exit(until, code)
    case NoStatus{}:
      Broken{}
    case TimedOut{}:
      Broken{}
    case SpawnFailed{}:
      Broken{}
    case Cancelled{}:
      Unjudged{}

# The bounds
# ----------

# three turns failed in a row: the loop gives up
def tired(fails: Nat) -> Bool:
  match fails:
    case 0n:
      False{}
    case 1n:
      False{}
    case 2n:
      False{}
    case 3n+k:
      True{}

# the loop is on
def on(p: Phase) -> Bool:
  match p:
    case Off{}:
      False{}
    case Armed{}:
      True{}
    case Turn{}:
      True{}
    case Judging{}:
      True{}
    case Paused{}:
      True{}
    case Ended{why}:
      False{}

def in_turn(p: Phase) -> Bool:
  match p:
    case Off{}:
      False{}
    case Armed{}:
      False{}
    case Turn{}:
      True{}
    case Judging{}:
      False{}
    case Paused{}:
      False{}
    case Ended{why}:
      False{}

def in_judging(p: Phase) -> Bool:
  match p:
    case Off{}:
      False{}
    case Armed{}:
      False{}
    case Turn{}:
      False{}
    case Judging{}:
      True{}
    case Paused{}:
      False{}
    case Ended{why}:
      False{}

def spent.nat(n: Nat) -> Bool:
  match n:
    case 0n:
      True{}
    case 1n+p:
      False{}

# no automatic iteration is left
def spent(left: Maybe<&2, Nat>) -> Bool:
  match left:
    case None{}:
      False{}
    case Some{n}:
      spent.nat(n)

# the deadline is reached
def late(deadline: Maybe<&2, Nat>, now: Nat) -> Bool:
  match deadline:
    case None{}:
      False{}
    case Some{d}:
      Nat.is_le(d, now)

def less.nat(n: Nat) -> Nat:
  match n:
    case 0n:
      0n
    case 1n+p:
      p

# one automatic iteration fewer
def less(left: Maybe<&2, Nat>) -> Maybe<&2, Nat>:
  match left:
    case None{}:
      None{}
    case Some{n}:
      Some{less.nat(n)}

def halt.time(late: Bool) -> Maybe<&2, End>:
  match late:
    case True{}:
      Some{OutOfTime{}}
    case False{}:
      None{}

def halt.turns(spent: Bool, late: Bool) -> Maybe<&2, End>:
  match spent:
    case True{}:
      Some{OutOfTurns{}}
    case False{}:
      halt.time(late)

def halt.budget(funded: Bool, spent: Bool, late: Bool) -> Maybe<&2, End>:
  match funded:
    case True{}:
      halt.turns(spent, late)
    case False{}:
      Some{OutOfBudget{}}

def halt.fails(tired: Bool, funded: Bool, spent: Bool, late: Bool) -> Maybe<&2, End>:
  match tired:
    case True{}:
      Some{TurnsFailed{}}
    case False{}:
      halt.budget(funded, spent, late)

# the bound that forbids one more automatic iteration, if any: the failed
# turns, then the budget, then the count, then the time
def halt(fails: Nat, funded: Bool, left: Maybe<&2, Nat>, deadline: Maybe<&2, Nat>, now: Nat) -> Maybe<&2, End>:
  halt.fails(tired(fails), funded, spent(left), late(deadline, now))

# The step
# --------

def advance.on(h: Maybe<&2, End>, +i: Nat, l: Maybe<&2, Nat>, d: Maybe<&2, Nat>, c: Cond, +b: String, f: Nat, x: Last) -> St & Act:
  match h:
    case Some{+why}:
      (St{Ended{why}, i, l, d, c, b, f, x}, Report{why})
    case None{}:
      (St{Turn{}, 1n+i, less(l), d, c, b, f, x}, Submit{1n+i, b})

# after a turn that the condition did not stop: the next iteration, unless
# a bound forbids it
def advance(+i: Nat, +l: Maybe<&2, Nat>, +d: Maybe<&2, Nat>, c: Cond, +b: String, +f: Nat, x: Last, now: Nat, funded: Bool) -> St & Act:
  advance.on(halt(f, funded, l, d, now), i, l, d, c, b, f, x)

# the automatic iterations a limit allows
def turns(lim: Limit) -> Maybe<&2, Nat>:
  match lim:
    case NoLimit{}:
      None{}
    case Count{n}:
      Some{n}
    case Span{ms}:
      None{}

# the deadline a limit sets from the clock
def until(lim: Limit, now: Nat) -> Maybe<&2, Nat>:
  match lim:
    case NoLimit{}:
      None{}
    case Count{n}:
      None{}
    case Span{ms}:
      Some{Nat.add(now, ms)}

# a new loop: armed without a prompt, else in its first turn
def start(+lim: Limit, c: Cond, pr: Maybe<&2, String>, now: Nat) -> St & Act:
  match pr:
    case None{}:
      (St{Armed{}, 0n, turns(lim), until(lim, now), c, "", 0n, NoCheck{}}, Rest{})
    case Some{+t}:
      (St{Turn{}, 1n, turns(lim), until(lim, now), c, t, 0n, NoCheck{}}, Submit{1n, t})

def enter(live: Bool, i: Nat, l: Maybe<&2, Nat>, d: Maybe<&2, Nat>, c: Cond, b: String, f: Nat, x: Last, lim: Limit, c2: Cond, pr: Maybe<&2, String>, now: Nat) -> St & Act:
  match live:
    case True{}:
      (St{Ended{Stopped{}}, i, l, d, c, b, f, x}, Report{Stopped{}})
    case False{}:
      start(lim, c2, pr, now)

def stop(live: Bool, p: Phase, i: Nat, l: Maybe<&2, Nat>, d: Maybe<&2, Nat>, c: Cond, b: String, f: Nat, x: Last) -> St & Act:
  match live:
    case True{}:
      (St{Ended{Stopped{}}, i, l, d, c, b, f, x}, Report{Stopped{}})
    case False{}:
      (St{p, i, l, d, c, b, f, x}, Rest{})

def abort(live: Bool, p: Phase, i: Nat, l: Maybe<&2, Nat>, d: Maybe<&2, Nat>, c: Cond, b: String, f: Nat, x: Last) -> St & Act:
  match live:
    case True{}:
      (St{Paused{}, i, l, d, c, "", f, x}, Rest{})
    case False{}:
      (St{p, i, l, d, c, b, f, x}, Rest{})

def prompt(live: Bool, p: Phase, +i: Nat, l: Maybe<&2, Nat>, d: Maybe<&2, Nat>, c: Cond, b: String, f: Nat, x: Last, t: String) -> St & Act:
  match live:
    case True{}:
      (St{Turn{}, 1n+i, l, d, c, t, 0n, x}, Adopt{1n+i})
    case False{}:
      (St{p, i, l, d, c, b, f, x}, Rest{})

# after a settled turn: with a condition, read its evidence first; with
# none, the next iteration
def gate(c: Cond, +i: Nat, l: Maybe<&2, Nat>, d: Maybe<&2, Nat>, b: String, f: Nat, x: Last, now: Nat, funded: Bool) -> St & Act:
  match c:
    case NoCond{}:
      advance(i, l, d, NoCond{}, b, f, x, now, funded)
    case Until{cmd}:
      (St{Judging{}, i, l, d, Until{cmd}, b, f, x}, Judge{i})
    case While{cmd}:
      (St{Judging{}, i, l, d, While{cmd}, b, f, x}, Judge{i})

def settled.out(out: Out, i: Nat, l: Maybe<&2, Nat>, d: Maybe<&2, Nat>, c: Cond, b: String, f: Nat, x: Last, now: Nat, funded: Bool) -> St & Act:
  match out:
    case Ran{}:
      gate(c, i, l, d, b, 0n, x, now, funded)
    case Errored{}:
      gate(c, i, l, d, b, 1n+f, x, now, funded)
    case Halted{}:
      (St{Paused{}, i, l, d, c, "", f, x}, Rest{})

def settled.mine(blocked: Bool, out: Out, i: Nat, l: Maybe<&2, Nat>, d: Maybe<&2, Nat>, c: Cond, b: String, f: Nat, x: Last, now: Nat, funded: Bool) -> St & Act:
  match blocked:
    case True{}:
      (St{Turn{}, i, l, d, c, b, f, x}, Defer{})
    case False{}:
      settled.out(out, i, l, d, c, b, f, x, now, funded)

def settled(mine: Bool, p: Phase, i: Nat, l: Maybe<&2, Nat>, d: Maybe<&2, Nat>, c: Cond, b: String, f: Nat, x: Last, out: Out, blocked: Bool, now: Nat, funded: Bool) -> St & Act:
  match mine:
    case True{}:
      settled.mine(blocked, out, i, l, d, c, b, f, x, now, funded)
    case False{}:
      (St{p, i, l, d, c, b, f, x}, Rest{})

def judged.verdict(v: Verdict, +i: Nat, l: Maybe<&2, Nat>, d: Maybe<&2, Nat>, c: Cond, b: String, f: Nat, x: Last, ev: Evid, now: Nat, funded: Bool) -> St & Act:
  match v:
    case Confirmed{}:
      (St{Ended{Satisfied{}}, i, l, d, c, b, f, Check{i, ev}}, Report{Satisfied{}})
    case Refuted{}:
      advance(i, l, d, c, b, f, Check{i, ev}, now, funded)
    case Broken{}:
      (St{Ended{CheckBroke{}}, i, l, d, c, b, f, Check{i, ev}}, Report{CheckBroke{}})
    case Unjudged{}:
      (St{Judging{}, i, l, d, c, b, f, x}, Rest{})

def judged.cond(c: Cond, i: Nat, l: Maybe<&2, Nat>, d: Maybe<&2, Nat>, b: String, f: Nat, x: Last, +ev: Evid, now: Nat, funded: Bool) -> St & Act:
  match c:
    case NoCond{}:
      advance(i, l, d, NoCond{}, b, f, x, now, funded)
    case Until{cmd}:
      judged.verdict(judge(True{}, ev), i, l, d, Until{cmd}, b, f, x, ev, now, funded)
    case While{cmd}:
      judged.verdict(judge(False{}, ev), i, l, d, While{cmd}, b, f, x, ev, now, funded)

def judged.mine(blocked: Bool, i: Nat, l: Maybe<&2, Nat>, d: Maybe<&2, Nat>, c: Cond, b: String, f: Nat, x: Last, ev: Evid, now: Nat, funded: Bool) -> St & Act:
  match blocked:
    case True{}:
      (St{Judging{}, i, l, d, c, b, f, x}, Defer{})
    case False{}:
      judged.cond(c, i, l, d, b, f, x, ev, now, funded)

def judged(mine: Bool, p: Phase, i: Nat, l: Maybe<&2, Nat>, d: Maybe<&2, Nat>, c: Cond, b: String, f: Nat, x: Last, ev: Evid, blocked: Bool, now: Nat, funded: Bool) -> St & Act:
  match mine:
    case True{}:
      judged.mine(blocked, i, l, d, c, b, f, x, ev, now, funded)
    case False{}:
      (St{p, i, l, d, c, b, f, x}, Rest{})

# the work a restarted worker takes up again: the turn in flight, or the
# condition command; nothing changes
def restart(p: Phase, +i: Nat, l: Maybe<&2, Nat>, d: Maybe<&2, Nat>, c: Cond, +b: String, f: Nat, x: Last) -> St & Act:
  match p:
    case Off{}:
      (St{Off{}, i, l, d, c, b, f, x}, Rest{})
    case Armed{}:
      (St{Armed{}, i, l, d, c, b, f, x}, Rest{})
    case Turn{}:
      (St{Turn{}, i, l, d, c, b, f, x}, Resume{i, b})
    case Judging{}:
      (St{Judging{}, i, l, d, c, b, f, x}, Judge{i})
    case Paused{}:
      (St{Paused{}, i, l, d, c, b, f, x}, Rest{})
    case Ended{why}:
      (St{Ended{why}, i, l, d, c, b, f, x}, Rest{})

def step.on(+p: Phase, +i: Nat, l: Maybe<&2, Nat>, d: Maybe<&2, Nat>, c: Cond, b: String, f: Nat, x: Last, e: Ev) -> St & Act:
  match e:
    case Enter{lim, c2, pr, now}:
      enter(on(p), i, l, d, c, b, f, x, lim, c2, pr, now)
    case Stop{}:
      stop(on(p), p, i, l, d, c, b, f, x)
    case Abort{}:
      abort(on(p), p, i, l, d, c, b, f, x)
    case Prompt{t}:
      prompt(on(p), p, i, l, d, c, b, f, x, t)
    case Settled{k, out, blocked, now, funded}:
      settled(Bool.and(in_turn(p), Nat.is_eq(k, i)), p, i, l, d, c, b, f, x, out, blocked, now, funded)
    case Judged{k, ev, blocked, now, funded}:
      judged(Bool.and(in_judging(p), Nat.is_eq(k, i)), p, i, l, d, c, b, f, x, ev, blocked, now, funded)
    case Restart{}:
      restart(p, i, l, d, c, b, f, x)

# the state after event e, and what Rust does now
def step(s: St, e: Ev) -> St & Act:
  match s:
    case St{p, i, l, d, c, b, f, x}:
      step.on(p, i, l, d, c, b, f, x, e)
