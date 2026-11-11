# eukhe: the laws of area infer_guard

import Base
import ../bend/infer.bend as If
import ../bend/infer_guard.bend as M
import ../bend/ffi_infer_guard.bend as FG
import ../bend/wire.bend as Wr
import ./base.bend as LawsBase

# (S6.5) The repetition guard, one chunk at a time
# ------------------------------------------------
# The model `guard` in bend/infer.bend section 4;
# a stream's lines go to a stepper of the compiled core
# (bend/ffi_infer_guard.bend) one id per line. Every input is free: any
# window, any chunks read before, any chunk.
#
# R1: a chunk cuts the stream exactly when the last k chunks, it the
#     newest, repeat with a period p of 1 to max(1, k/4); the cut reports
#     the chunks read and the shortest such period; else the chunk is
#     kept (crates/eukhe-ai src/utils/stream_repeat.rs, RepetitionGuard).
# R2: the longest period checked is k/4 rounded down, at least 1
#     (stream_repeat.rs: "a period of at most `max(1, k / 4)`"; the
#     default window 64 checks periods up to 16).
# R3: an open spelled as one Nat (the window) opens a fresh guard and
#     answers nothing; any other open input opens the refused state with
#     exactly the error form 'E ', then "infer_guard: malformed window",
#     and the refused state answers every step with exactly 'E ', then
#     "infer_guard: the open was refused".
# R4: a step spelled as one Nat (the chunk's id) moves the guard as R1
#     and answers 0 (kept) or 1, the chunks read, the period (cut); any
#     other step input answers exactly 'E ', then "infer_guard: malformed
#     chunk", and keeps the guard; a cut stream stays cut: every later
#     step answers the same cut.
# R1 is infer_guard_feed_exact and infer_guard_steps (driven over a
# stream, the steps are `guard`); R2 is infer_guard_periods and
# infer_guard_periods_small; R3 is infer_guard_ffi_open,
# infer_guard_ffi_open_malformed_exact and infer_guard_ffi_refused_run; R4
# is infer_guard_ffi_step, infer_guard_ffi_step_malformed_exact and
# infer_guard_ffi_stays_cut.

# The step, independently: the chunks are newest first. The last k
# chunks repeat with period p when each of the newest k - p equals the
# chunk p places before it (a window of at most p chunks always does). The
# guard checks the periods 1 to If.periods(k) (R2, pinned by
# infer_guard_periods and infer_guard_periods_small) and cuts at the chunk
# that completes such a window, reporting the shortest such period; else
# it keeps the chunk.

# s without its first n items
def skip(n: Nat, s: List<&2, Nat>) -> List<&2, Nat>:
  match n:
    case 0n:
      s
    case 1n+j:
      match s:
        case Nil{}:
          Nil{}
        case x <> rest:
          skip(j, rest)

# a and b both hold at least m items, and their first m are equal
def agree(m: Nat, a: List<&2, Nat>, b: List<&2, Nat>) -> Bool:
  match m:
    case 0n:
      True{}
    case 1n+j:
      match a:
        case Nil{}:
          False{}
        case x <> ra:
          match b:
            case Nil{}:
              False{}
            case y <> rb:
              Bool.and(Nat.is_eq(x, y), agree(j, ra, rb))

# LAW infer_guard_periods (R2): the longest period the guard checks is
# k/4 rounded down for a window of 8 or more: for every q with
# 4(1 + q) <= k < 4(2 + q) it is 1 + q
# EXCLUDES: another bound on the periods (k/2, k/4 rounded up, k/4 + 1, a
#   fixed 16), so a block that repeats fewer than four times cut, or one
#   that repeats four times kept
law infer_guard_periods:
  for +k: Nat
  for +q: Nat
  for lo: {Nat.is_le(Nat.mul(1n+q, 4n), k) == True{} : Bool}
  for hi: {Nat.is_lt(k, Nat.mul(2n+q, 4n)) == True{} : Bool}
  {If.periods(k) == 1n+q : Nat}

# LAW infer_guard_periods_small (R2): a window below 8 checks period 1
# only (k/4 is 0 or 1, and at least 1)
# EXCLUDES: no period checked for a small window (a window of 1, 2 or 3
#   that never cuts), a period of 2 for a window below 8
law infer_guard_periods_small:
  for +k: Nat
  for lo: {Nat.is_lt(k, 8n) == True{} : Bool}
  {If.periods(k) == 1n : Nat}

def least.pick(m: Maybe<&2, Nat>, ok: Bool, p: Nat) -> Maybe<&2, Nat>:
  match m:
    case Some{d}:
      Some{d}
    case None{}:
      match ok:
        case True{}:
          Some{p}
        case False{}:
          None{}

# the shortest period p <= n with which the last k chunks of s repeat
def least(+s: List<&2, Nat>, +k: Nat, n: Nat) -> Maybe<&2, Nat>:
  match n:
    case 0n:
      None{}
    case 1n++q:
      least.pick(least(s, k, q), agree(Nat.sub(k, 1n+q), s, skip(1n+q, s)), 1n+q)

def feed_spec.of(m: Maybe<&2, Nat>, k: Nat, s: List<&2, Nat>, n: Nat) -> M.Next:
  match m:
    case None{}:
      M.Goes{M.St{k, s, 1n+n}}
    case Some{p}:
      M.Cuts{1n+n, p}

def feed_spec(st: M.St, x: Nat) -> M.Next:
  match st:
    case M.St{+k, seen, n}:
      +s = {x <> seen : List<&2, Nat>}
      feed_spec.of(least(s, k, If.periods(k)), k, s, n)

# LAW infer_guard_feed_exact: a chunk is exactly: the cut after one more chunk, with the shortest period p (1 to max(1, k/4)) with which the last k chunks, it the newest, repeat; else kept, the guard holding it newest first and one more chunk read
law infer_guard_feed_exact:
  for st: M.St
  for x: Nat
  {M.feed(st, x) == feed_spec(st, x) : M.Next}

# the guard driven over a stream: each chunk fed in turn, until one cuts
def drive(xs: List<&2, Nat>, nx: M.Next) -> If.Cut:
  match xs nx:
    case _ M.Cuts{at, p}:
      If.CutAt{at}
    case Nil{} M.Goes{st}:
      If.Whole{}
    case x <> rest M.Goes{st}:
      drive(rest, M.feed(st, x))

# LAW infer_guard_steps: the steps the stream takes, driven over its chunks from a fresh guard, are `guard`: every law of `guard` holds for them
law infer_guard_steps:
  for xs: List<&2, Nat>
  for +k: Nat
  {drive(xs, M.Goes{M.start(k)}) == If.guard(xs, k) : If.Cut}

# The entry (bend/ffi_infer_guard.bend)
# -------------------------------------
# The spellers write what Rust writes, with the wire primitives only.

# the open: the window
def spell_open(k: Nat) -> String:
  Wr.put_nat(k, "")

# a step: the chunk's id
def spell_chunk(x: Nat) -> String:
  Wr.put_nat(x, "")

# what Rust reads after a chunk: 0 kept | 1, the chunks read, the period
def spell_cut(at: Nat, p: Nat) -> String:
  Wr.put_nat(1n, Wr.put_nat(at, Wr.put_nat(p, "")))

# the stepper after a chunk the model reads
def spell_next(n: M.Next) -> FG.St & String:
  match n:
    case M.Goes{g}:
      (FG.Live{g}, Wr.put_nat(0n, ""))
    case M.Cuts{+at, +p}:
      (FG.Ended{at, p}, spell_cut(at, p))

# Reader: a Nat that is the whole input
def read_nat.end(whole: Bool, n: Nat) -> Maybe<&2, Nat>:
  match whole:
    case True{}:
      Some{n}
    case False{}:
      None{}

def read_nat.whole(d: Wr.Dec<Nat>) -> Maybe<&2, Nat>:
  match d:
    case Wr.Got{n, s}:
      read_nat.end(Wr.end(s), n)
    case Wr.Bad{}:
      None{}

# the Nat s is, when s is exactly one
def read_nat(s: String) -> Maybe<&2, Nat>:
  read_nat.whole(Wr.get_nat(s))

# LAW infer_guard_ffi_open: an open with a window that fits answers a fresh guard of that window, and an empty reply
law infer_guard_ffi_open:
  for +k: Nat
  for fits: {LawsBase.wire_fits(k) == True{} : Bool}
  {FG.open(spell_open(k)) == (FG.Live{M.start(k)}, "") : FG.St & String}

# LAW infer_guard_ffi_open_malformed_exact: an open whose input is not exactly a window opens the refused state, with exactly the error form 'E ', then "infer_guard: malformed window"
law infer_guard_ffi_open_malformed_exact:
  for +s: String
  for no: {read_nat(s) == None{} : Maybe<&2, Nat>}
  {FG.open(s) == (FG.Shut{}, SCon{'E', SCon{' ', "infer_guard: malformed window"}}) : FG.St & String}

# LAW infer_guard_ffi_step: on every guard and every chunk that fits, the stepper moves as the model's feed and answers it: kept, or the cut with its chunks read and period
law infer_guard_ffi_step:
  for +g: M.St
  for +x: Nat
  for fits: {LawsBase.wire_fits(x) == True{} : Bool}
  {FG.step(FG.Live{g}, spell_chunk(x)) == spell_next(M.feed(g, x)) : FG.St & String}

# LAW infer_guard_ffi_step_malformed_exact: a step whose input is not exactly a chunk keeps the guard and answers exactly the error form 'E ', then "infer_guard: malformed chunk"
law infer_guard_ffi_step_malformed_exact:
  for +g: M.St
  for +s: String
  for no: {read_nat(s) == None{} : Maybe<&2, Nat>}
  {FG.step(FG.Live{g}, s) == (FG.Live{g}, SCon{'E', SCon{' ', "infer_guard: malformed chunk"}}) : FG.St & String}

# the reply r, then the replies of the stepper fed the inputs ins, one
# step each from the state of r
def feed(ins: List<&2, String>, r: FG.St & String) -> List<&2, String>:
  match ins:
    case Nil{}:
      (st, out) = r
      [out]
    case i <> t:
      (st, out) = r
      out <> feed(t, FG.step(st, i))

# LAW infer_guard_ffi_stays_cut (R4): once a chunk that fits cuts the
# stream (the model's feed cuts after `at` chunks with period p), the
# stepper answers that cut, then the same cut to every later input,
# whatever it is (a chunk, a malformed one, anything)
# EXCLUDES: a cut stream that reopens, reads more chunks, answers kept or
#   an error, or reports another cut
law infer_guard_ffi_stays_cut:
  for +g: M.St
  for +x: Nat
  for +at: Nat
  for +p: Nat
  for +ins: List<&2, String>
  for fits: {LawsBase.wire_fits(x) == True{} : Bool}
  for cut: {M.feed(g, x) == M.Cuts{at, p} : M.Next}
  {feed(ins, FG.step(FG.Live{g}, spell_chunk(x))) == List.replicate(String, 1n+List.length(&2, String, ins), spell_cut(at, p)) : List<&2, String>}

# LAW infer_guard_ffi_refused_run (R3): an open the stepper refuses (its
# reply opens with 'E') answers exactly the error form 'E ', then
# "infer_guard: malformed window", and every later step, whatever its
# input, exactly 'E ', then "infer_guard: the open was refused": no chunk
# is read and no cut is answered
# EXCLUDES: a refused open that runs a guard (a default window), a step
#   after a refused open answered kept or cut, another error text
law infer_guard_ffi_refused_run:
  for +s: String
  for +ins: List<&2, String>
  for no: {LawsBase.wire_opens_err(Pair.snd(FG.St, String, FG.open(s))) == True{} : Bool}
  {feed(ins, FG.open(s)) == SCon{'E', SCon{' ', "infer_guard: malformed window"}} <> List.replicate(String, List.length(&2, String, ins), SCon{'E', SCon{' ', "infer_guard: the open was refused"}}) : List<&2, String>}

# LAW infer_guard_ffi_example: anchor: the bytes Rust sends and reads: a window of 3 cuts the third equal line, period 1, and stays cut; a window of 8 cuts a two-line block at its fourth repetition, period 2; a window of 2 keeps distinct lines; a malformed chunk keeps the guard; a malformed window is refused
law infer_guard_ffi_example:
  {feed(["7,", "7,", "7,", "8,"], FG.open("3,")) == ["", "0,", "0,", "1,3,1,", "1,3,1,"] : List<&2, String>} &
  {feed(["1,", "2,", "1,", "2,", "1,", "2,", "1,", "2,"], FG.open("8,")) == ["", "0,", "0,", "0,", "0,", "0,", "0,", "0,", "1,8,2,"] : List<&2, String>} &
  {feed(["1,", "2,", "x", "3,", "3,"], FG.open("2,")) == ["", "0,", "0,", SCon{'E', SCon{' ', "infer_guard: malformed chunk"}}, "0,", "1,4,1,"] : List<&2, String>} &
  {feed(["1,"], FG.open("2")) == [SCon{'E', SCon{' ', "infer_guard: malformed window"}}, SCon{'E', SCon{' ', "infer_guard: the open was refused"}}] : List<&2, String>}
