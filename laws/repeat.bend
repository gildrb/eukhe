# eukhe: the laws of area repeat

import Base
import ../bend/repeat.bend as Rp
import ../bend/ffi_repeat.bend as FRp
import ../bend/wire.bend as Wr
import ./base.bend as LawsBase

# LAWS (R1): the rounds in a row with the same tool calls and the same
# results (bend/repeat.bend, the port of eukhe-durable
# harness/generation/repeat.rs `rounds_in_a_row`; docs/harness.md
# H4.8.4). Each law is an open claim about Rp.step, alone or driven over
# a context; PROOF.bend proves them (as Repeat.<law>) with the lemmas of
# proof/repeat/.
#
# The host reads the request's context newest first and gives each
# message as an Rp.Ev: a tool result as the id of its content and error
# flag, a reply with tool calls as the id of its calls (names and
# canonical arguments, as a set), equal values with equal ids; `want` is
# the id of the calls the new reply would make. Ids are free: every law
# holds for every assignment of ids.
#
# R1: the count is 1 and the rounds at the end of the context that repeat,
#     saturated at 2^32 - 1. A round is a reply with tool calls and the
#     results after it (in the context; newer in the walk) up to the next
#     reply. The newest round repeats when its calls are the requested
#     ones; each older round repeats when its calls and its results (in
#     order) are the newest round's. The row ends at the first round that
#     does not repeat, the first user message, the first reply with no
#     tool call, or the context's start; system messages change nothing.
# R2: the walk stops at the message that ends the row: no older message
#     is read.

# Terms
# -----

# the largest count: 2^32 - 1, the host's u32 counter saturates there
def cap_spec() -> Nat:
  4294967295n

def clip.pick(over: Bool, n: Nat, top: Nat) -> Nat:
  match over:
    case True{}:
      top
    case False{}:
      n

# n saturated at top
def clip_at(+n: Nat, +top: Nat) -> Nat:
  clip.pick(Nat.is_lt(top, n), n, top)

# n saturated at 2^32 - 1
def clip(+n: Nat) -> Nat:
  clip_at(n, cap_spec())

# the same ids in the same order
def ids_eq(a: List<&2, Nat>, b: List<&2, Nat>) -> Bool:
  match a b:
    case Nil{} Nil{}:
      True{}
    case Nil{} y <> u:
      False{}
    case x <> t Nil{}:
      False{}
    case x <> t y <> u:
      Bool.and(Nat.is_eq(x, y), ids_eq(t, u))

# a piece of a context: a round (its calls' id and its results' ids,
# oldest first), or the end of the row
type Piece is Data:
  Turn{set: Nat, results: List<&2, Nat>}
  RowEnd{}

# the pieces of a context, newest first, the results read since the last
# reply in acc (oldest first): each reply with calls closes a round of
# them; system messages are dropped; a user message, a reply with no
# call or the context's start halts
def pieces(es: List<&2, Rp.Ev>, acc: List<&2, Nat>) -> List<&2, Piece>:
  match es:
    case Nil{}:
      [RowEnd{}]
    case e <> t:
      match e:
        case Rp.System{}:
          pieces(t, acc)
        case Rp.User{}:
          [RowEnd{}]
        case Rp.Result{r}:
          pieces(t, r <> acc)
        case Rp.Called{s}:
          Turn{s, acc} <> pieces(t, Nil{})
        case Rp.Said{}:
          [RowEnd{}]
        case Rp.End{}:
          [RowEnd{}]

def again.pick(hit: Bool, n: Nat) -> Nat:
  match hit:
    case True{}:
      1n+n
    case False{}:
      0n

# how many rounds in a row at the head of ps have the calls s0 and the
# results rs0
def again(+s0: Nat, +rs0: List<&2, Nat>, ps: List<&2, Piece>) -> Nat:
  match ps:
    case Nil{}:
      0n
    case p <> t:
      match p:
        case Turn{s, rs}:
          again.pick(Bool.and(Nat.is_eq(s, s0), ids_eq(rs, rs0)), again(s0, rs0, t))
        case RowEnd{}:
          0n

# how many rounds repeat at the head of ps: none unless the first has the
# calls want; then it and the rounds after it equal to it
def row(+want: Nat, ps: List<&2, Piece>) -> Nat:
  match ps:
    case Nil{}:
      0n
    case p <> t:
      match p:
        case Turn{+s, +rs}:
          again.pick(Nat.is_eq(s, want), again(s, rs, t))
        case RowEnd{}:
          0n

# R1: the count of a context, newest first, for the calls want
def count_spec(+want: Nat, es: List<&2, Rp.Ev>) -> Nat:
  clip(1n+row(want, pieces(es, Nil{})))

def step_spec.hit(hit: Bool, w: Rp.Walk, +k: Nat) -> Rp.Next:
  match hit:
    case True{}:
      Rp.Goes{w}
    case False{}:
      Rp.Stops{clip(1n+k)}

# a reply with calls s: the newest round repeats when s is the requested
# calls, an older one when s and the pending results are the newest
# round's
def step_spec.called(first: Maybe<&2, Rp.Round>, +want: Nat, +k: Nat, +s: Nat, +pend: List<&2, Nat>) -> Rp.Next:
  match first:
    case None{}:
      step_spec.hit(Nat.is_eq(s, want), Rp.Walk{want, 1n+k, Some{Rp.Round{s, pend}}, Nil{}}, k)
    case Some{r0}:
      match r0:
        case Rp.Round{+s0, +rs0}:
          step_spec.hit(Bool.and(Nat.is_eq(s, s0), ids_eq(pend, rs0)), Rp.Walk{want, 1n+k, Some{Rp.Round{s0, rs0}}, Nil{}}, k)

# R1, R2 per message: a system message keeps the walk; a result joins the
# pending results; a reply with calls goes on, one more round counted,
# the first round kept, no result pending, exactly when its round
# repeats; every other message stops with the count
def step_spec(w: Rp.Walk, e: Rp.Ev) -> Rp.Next:
  match w:
    case Rp.Walk{+want, +k, first, +pend}:
      match e:
        case Rp.System{}:
          Rp.Goes{Rp.Walk{want, k, first, pend}}
        case Rp.User{}:
          Rp.Stops{clip(1n+k)}
        case Rp.Result{r}:
          Rp.Goes{Rp.Walk{want, k, first, r <> pend}}
        case Rp.Called{s}:
          step_spec.called(first, want, k, s, pend)
        case Rp.Said{}:
          Rp.Stops{clip(1n+k)}
        case Rp.End{}:
          Rp.Stops{clip(1n+k)}

# no answer: the context's end never lets the row go on
def drive.last(n: Rp.Next) -> Nat:
  match n:
    case Rp.Goes{w}:
      0n
    case Rp.Stops{c}:
      c

# the count a walk answers after n, fed the messages es newest first
# until it stops, then the context's end
def drive(es: List<&2, Rp.Ev>, n: Rp.Next) -> Nat:
  match es n:
    case _ Rp.Stops{c}:
      c
    case Nil{} Rp.Goes{w}:
      drive.last(Rp.step(w, Rp.End{}))
    case e <> t Rp.Goes{w}:
      drive(t, Rp.step(w, e))

# a step's answer is in range: the row goes on, or a count of 1 to
# 2^32 - 1
def bounded(n: Rp.Next) -> Bool:
  match n:
    case Rp.Goes{w}:
      True{}
    case Rp.Stops{+c}:
      Bool.and(Nat.is_le(1n, c), Nat.is_le(c, cap_spec()))

# Laws
# ----

# LAW repeat_steps: a walk of the requested calls, driven over any context newest first, answers the count of R1: 1 and the rounds that repeat, saturated at 2^32 - 1
# EXCLUDES: a round counted with other calls or other results, results
#   grouped with the wrong reply, a row that goes on past a user message,
#   a reply with no call or a round that does not repeat, a system message
#   that ends the row, a count off by one, a count that wraps
law repeat_steps:
  for +want: Nat
  for es: List<&2, Rp.Ev>
  {drive(es, Rp.Goes{Rp.start(want)}) == count_spec(want, es) : Nat}

# LAW repeat_step_exact: one message moves the walk as R1-R2 say: a system message keeps it, a result joins the pending results, a reply with calls goes on exactly when its round repeats (the newest round's calls are the requested ones, an older round equals the newest), else the message stops the walk with the count
# EXCLUDES: a walk that reads past the message that ends the row, a
#   pending result kept after a round or lost, the newest round replaced
#   by an older one, a count kept in another way
law repeat_step_exact:
  for w: Rp.Walk
  for e: Rp.Ev
  {Rp.step(w, e) == step_spec(w, e) : Rp.Next}

# LAW repeat_user_ends: a user message ends the row: nothing older than it changes the count
# EXCLUDES: a row that goes on past a steer or the user's last turn
law repeat_user_ends:
  for xs: List<&2, Rp.Ev>
  for +w: Rp.Walk
  for ys: List<&2, Rp.Ev>
  {drive(List.append(&2, Rp.Ev, xs, Rp.User{} <> ys), Rp.Goes{w}) == drive(xs, Rp.Goes{w}) : Nat}

# LAW repeat_said_ends: a reply with no tool call ends the row: nothing older than it changes the count
# EXCLUDES: a text answer skipped as if it were no reply
law repeat_said_ends:
  for xs: List<&2, Rp.Ev>
  for +w: Rp.Walk
  for ys: List<&2, Rp.Ev>
  {drive(List.append(&2, Rp.Ev, xs, Rp.Said{} <> ys), Rp.Goes{w}) == drive(xs, Rp.Goes{w}) : Nat}

# LAW repeat_system_ignored: a system message changes nothing: the count is the count without it
# EXCLUDES: a system message that ends the row or splits a round
law repeat_system_ignored:
  for xs: List<&2, Rp.Ev>
  for +w: Rp.Walk
  for ys: List<&2, Rp.Ev>
  {drive(List.append(&2, Rp.Ev, xs, Rp.System{} <> ys), Rp.Goes{w}) == drive(List.append(&2, Rp.Ev, xs, ys), Rp.Goes{w}) : Nat}

# LAW repeat_results_change_ends: an older round with the newest round's calls but other results ends the row at once, with the count so far
# EXCLUDES: a poll of a job that makes progress counted as a repeat
law repeat_results_change_ends:
  for +want: Nat
  for +k: Nat
  for +s: Nat
  for +rs0: List<&2, Nat>
  for +pend: List<&2, Nat>
  for ne: {ids_eq(pend, rs0) == False{} : Bool}
  {Rp.step(Rp.Walk{want, k, Some{Rp.Round{s, rs0}}, pend}, Rp.Called{s}) == Rp.Stops{clip(1n+k)} : Rp.Next}

# LAW repeat_bounded: every count the walk answers is 1 to 2^32 - 1
# EXCLUDES: a count of 0, a count past the host's u32 (a wrapped or
#   refused reply)
law repeat_bounded:
  for w: Rp.Walk
  for e: Rp.Ev
  {bounded(Rp.step(w, e)) == True{} : Bool}

# LAW repeat_example: anchor: the counts of rounds_in_a_row's cases: no context, two repeats (system message between), other calls, changed results, a steer, a text reply (saturation: repeat_steps and repeat_bounded; a closed anchor at 2^32 - 1 is too large for the checker)
# EXCLUDES: a spec that is wrong on the shipped cases
law repeat_example:
  {drive(Nil{}, Rp.Goes{Rp.start(7n)}) == 1n : Nat} &
  {drive([Rp.Result{1n}, Rp.Called{7n}, Rp.System{}, Rp.Result{1n}, Rp.Called{7n}], Rp.Goes{Rp.start(7n)}) == 3n : Nat} &
  {drive([Rp.Result{1n}, Rp.Called{8n}, Rp.Result{1n}, Rp.Called{8n}], Rp.Goes{Rp.start(7n)}) == 1n : Nat} &
  {drive([Rp.Result{1n}, Rp.Called{7n}, Rp.Result{2n}, Rp.Called{7n}], Rp.Goes{Rp.start(7n)}) == 2n : Nat} &
  {drive([Rp.Result{1n}, Rp.Called{7n}, Rp.User{}, Rp.Result{1n}, Rp.Called{7n}], Rp.Goes{Rp.start(7n)}) == 2n : Nat} &
  {drive([Rp.Result{1n}, Rp.Result{2n}, Rp.Called{7n}, Rp.Result{1n}, Rp.Result{2n}, Rp.Called{7n}, Rp.Said{}], Rp.Goes{Rp.start(7n)}) == 3n : Nat}

# LAWS (R3): the stepper of the compiled Bend core (bend/ffi_repeat.bend,
# driven by crates/eukhe-durable generation through
# `eukhe_bend::rules::repeat`). Each law is an open claim about FRp.open
# or FRp.step, stated with spec spellers built only from the wire
# primitives of bend/wire.bend (their round trips: laws/wire.bend).
#
# R3: the open is the requested calls' id (a Nat) and answers an empty
#     reply; a step is a message: tag 0 system, 1 user, 2 a result and its
#     id, 3 a reply with calls and its id, 4 a reply with no call, 5 the
#     context's end; it answers 0 while the row goes on, else 1 and the
#     count. An ended row answers its count to every later step. A
#     malformed open answers the error form "repeat: malformed open" and
#     refuses every step with "repeat: the open was refused"; a malformed
#     message (input left over included) answers "repeat: malformed
#     message" and keeps the walk; never a default.

# Spec spellers
# -------------

# the open: the requested calls' id
def spell_open(want: Nat) -> String:
  Wr.put_nat(want, "")

# a message: its tag, then its id
def spell_ev(e: Rp.Ev, rest: String) -> String:
  match e:
    case Rp.System{}:
      Wr.put_nat(0n, rest)
    case Rp.User{}:
      Wr.put_nat(1n, rest)
    case Rp.Result{r}:
      Wr.put_nat(2n, Wr.put_nat(r, rest))
    case Rp.Called{s}:
      Wr.put_nat(3n, Wr.put_nat(s, rest))
    case Rp.Said{}:
      Wr.put_nat(4n, rest)
    case Rp.End{}:
      Wr.put_nat(5n, rest)

# every id of a message fits the wire
def ev_fits(e: Rp.Ev) -> Bool:
  match e:
    case Rp.System{}:
      True{}
    case Rp.User{}:
      True{}
    case Rp.Result{+r}:
      LawsBase.wire_fits(r)
    case Rp.Called{+s}:
      LawsBase.wire_fits(s)
    case Rp.Said{}:
      True{}
    case Rp.End{}:
      True{}

# the row ended with count c
def spell_stop(c: Nat) -> String:
  Wr.put_nat(1n, Wr.put_nat(c, ""))

# the stepper after a message the model reads, and its reply
def spell_next(n: Rp.Next) -> FRp.St & String:
  match n:
    case Rp.Goes{w}:
      (FRp.Live{w}, Wr.put_nat(0n, ""))
    case Rp.Stops{+c}:
      (FRp.Ended{c}, spell_stop(c))

# the reply of a step or an open
def reply(r: FRp.St & String) -> String:
  match r:
    case (st, out):
      out

# Laws
# ----

# LAW repeat_ffi_open: an open with an id that fits the wire answers a walk of that id that read nothing, and an empty reply
# EXCLUDES: an id misread, a walk that starts with a round or a count
law repeat_ffi_open:
  for +want: Nat
  for fits: {LawsBase.wire_fits(want) == True{} : Bool}
  {FRp.open(spell_open(want)) == (FRp.Live{Rp.start(want)}, "") : FRp.St & String}

# LAW repeat_ffi_open_exact: every open the entry does not refuse is a spelled id that fits the wire
# EXCLUDES: a default walk for a malformed open or one with input left
#   over
law repeat_ffi_open_exact:
  for +s: String
  for ok: {LawsBase.wire_opens_err(reply(FRp.open(s))) == False{} : Bool}
  exs want: Nat
  {s == spell_open(want) : String} & {LawsBase.wire_fits(want) == True{} : Bool}

# LAW repeat_ffi_open_errors: an open the entry refuses opens the refused state with exactly the error form "repeat: malformed open"
# EXCLUDES: another error text, a refused open that keeps a walk
law repeat_ffi_open_errors:
  for +s: String
  for e: {LawsBase.wire_opens_err(reply(FRp.open(s))) == True{} : Bool}
  {FRp.open(s) == (FRp.Shut{}, Wr.err("repeat: malformed open")) : FRp.St & String}

# LAW repeat_ffi_step: on every walk and every spelled message whose id fits the wire, the stepper moves as the model's step and answers it: 0 while the row goes on, else 1 and the count
# EXCLUDES: a message read as another (a tag off by one, a result read as
#   a reply), an id misread, a reply in another spelling, an ended walk
#   kept live
law repeat_ffi_step:
  for +w: Rp.Walk
  for +e: Rp.Ev
  for fits: {ev_fits(e) == True{} : Bool}
  {FRp.step(FRp.Live{w}, spell_ev(e, "")) == spell_next(Rp.step(w, e)) : FRp.St & String}

# LAW repeat_ffi_step_exact: every step the entry answers with a value (not the error form) on a walk is a spelled message whose id fits the wire
# EXCLUDES: a default answer for a malformed message (a tag past 5, a
#   missing id, a Nat of 15 or more digits) or one with input left over
law repeat_ffi_step_exact:
  for +w: Rp.Walk
  for +s: String
  for ok: {LawsBase.wire_opens_err(reply(FRp.step(FRp.Live{w}, s))) == False{} : Bool}
  exs e: Rp.Ev
  {s == spell_ev(e, "") : String} & {ev_fits(e) == True{} : Bool}

# LAW repeat_ffi_step_errors: a step the entry refuses on a walk keeps the walk and answers exactly the error form "repeat: malformed message"
# EXCLUDES: another error text, a malformed message that moves or ends
#   the walk
law repeat_ffi_step_errors:
  for +w: Rp.Walk
  for +s: String
  for e: {LawsBase.wire_opens_err(reply(FRp.step(FRp.Live{w}, s))) == True{} : Bool}
  {FRp.step(FRp.Live{w}, s) == (FRp.Live{w}, Wr.err("repeat: malformed message")) : FRp.St & String}

# LAW repeat_ffi_ended: an ended row stays ended: every later step answers the same count
# EXCLUDES: a walk that restarts or answers another count after it ended
law repeat_ffi_ended:
  for +c: Nat
  for s: String
  {FRp.step(FRp.Ended{c}, s) == (FRp.Ended{c}, spell_stop(c)) : FRp.St & String}

# LAW repeat_ffi_shut: a refused open answers every step with the error form "repeat: the open was refused"
# EXCLUDES: a refused open that answers a count
law repeat_ffi_shut:
  for s: String
  {FRp.step(FRp.Shut{}, s) == (FRp.Shut{}, Wr.err("repeat: the open was refused")) : FRp.St & String}

# the reply r, then the replies of the stepper fed the inputs ins, one
# step each from the state of r
def feed(ins: List<&2, String>, r: FRp.St & String) -> List<&2, String>:
  match ins:
    case Nil{}:
      (st, out) = r
      [out]
    case i <> t:
      (st, out) = r
      out <> feed(t, FRp.step(st, i))

# LAW repeat_ffi_example: anchor: the bytes Rust sends and reads: two repeated rounds, changed results, a steer, a malformed message, a malformed open
# EXCLUDES: another spelling of an open, a message or a reply
law repeat_ffi_example:
  {feed(["2,5,", "3,0,", "2,5,", "3,0,", "5,"], FRp.open("0,")) == ["", "0,", "0,", "0,", "0,", "1,3,"] : List<&2, String>} &
  {feed(["2,5,", "3,0,", "2,6,", "3,0,", "5,"], FRp.open("0,")) == ["", "0,", "0,", "0,", "1,2,", "1,2,"] : List<&2, String>} &
  {feed(["0,", "2,5,", "3,0,", "1,", "3,0,"], FRp.open("0,")) == ["", "0,", "0,", "0,", "1,2,", "1,2,"] : List<&2, String>} &
  {feed(["x", "6,", "3,0", "4,"], FRp.open("0,")) == ["", Wr.err("repeat: malformed message"), Wr.err("repeat: malformed message"), Wr.err("repeat: malformed message"), "1,1,"] : List<&2, String>} &
  {feed(["5,"], FRp.open("0,x")) == [Wr.err("repeat: malformed open"), Wr.err("repeat: the open was refused")] : List<&2, String>}
