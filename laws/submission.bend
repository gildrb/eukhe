# eukhe: the laws of area submission

import Base
import ../bend/submission.bend as Sb
import ../bend/ffi_submission.bend as FSb
import ../bend/wire.bend as Wr
import ./base.bend as LawsBase

# LAWS (R1): one staged change of a submission's lifecycle
# (bend/submission.bend, the port of the session's batch assembly). Each
# law is an open claim about Sb.step; PROOF.bend proves them (as
# Submission.<law>) with the lemmas of proof/submission/.
#
# R1: a settled submission (an input answered or unanswered, a write
#     placed or unanswered) stays as it is, whatever the change.
# R2: placing puts a queued input at the change's entry, and a queued
#     write too (a placed write is settled); placing anything else that is
#     not settled (a placed input) is refused: not queued.
# R3: an answer settles a placed input with the change's answer entry,
#     keeping its user entry; an answer to anything else not settled (a
#     queued input or write) is refused: not a placed input.
# R4: settling unanswered settles any input that is not settled, keeping
#     its user entry when it was placed (none when it was queued), and any
#     queued write.
# Every submission, every change and every entry id is free.

# Terms
# -----

# s is settled: done or unanswered
def settled_spec(s: Sb.Sub) -> Bool:
  match s:
    case Sb.InQueued{}:
      False{}
    case Sb.InPlaced{e}:
      False{}
    case Sb.InAnswered{e, a}:
      True{}
    case Sb.InDropped{m}:
      True{}
    case Sb.WrQueued{}:
      False{}
    case Sb.WrPlaced{e}:
      True{}
    case Sb.WrDropped{}:
      True{}

# placing an unsettled submission at entry e
def place_spec(s: Sb.Sub, e: Nat) -> Sb.Out:
  match s:
    case Sb.InQueued{}:
      Sb.Moves{Sb.InPlaced{e}}
    case Sb.WrQueued{}:
      Sb.Moves{Sb.WrPlaced{e}}
    case Sb.InPlaced{f}:
      Sb.Refused{Sb.NotQueued{}}
    case Sb.InAnswered{f, a}:
      Sb.Refused{Sb.NotQueued{}}
    case Sb.InDropped{m}:
      Sb.Refused{Sb.NotQueued{}}
    case Sb.WrPlaced{f}:
      Sb.Refused{Sb.NotQueued{}}
    case Sb.WrDropped{}:
      Sb.Refused{Sb.NotQueued{}}

# answering an unsettled submission with the answer entry a
def answer_spec(s: Sb.Sub, a: Nat) -> Sb.Out:
  match s:
    case Sb.InPlaced{e}:
      Sb.Moves{Sb.InAnswered{e, a}}
    case Sb.InQueued{}:
      Sb.Refused{Sb.NotPlacedInput{}}
    case Sb.WrQueued{}:
      Sb.Refused{Sb.NotPlacedInput{}}
    case Sb.InAnswered{f, b}:
      Sb.Refused{Sb.NotPlacedInput{}}
    case Sb.InDropped{m}:
      Sb.Refused{Sb.NotPlacedInput{}}
    case Sb.WrPlaced{f}:
      Sb.Refused{Sb.NotPlacedInput{}}
    case Sb.WrDropped{}:
      Sb.Refused{Sb.NotPlacedInput{}}

# the user entry of an input, when it has one
def entry_spec(s: Sb.Sub) -> Maybe<&2, Nat>:
  match s:
    case Sb.InQueued{}:
      None{}
    case Sb.InPlaced{e}:
      Some{e}
    case Sb.InAnswered{e, a}:
      Some{e}
    case Sb.InDropped{m}:
      m
    case Sb.WrQueued{}:
      None{}
    case Sb.WrPlaced{e}:
      Some{e}
    case Sb.WrDropped{}:
      None{}

# s is an input
def input_spec(s: Sb.Sub) -> Bool:
  match s:
    case Sb.InQueued{}:
      True{}
    case Sb.InPlaced{e}:
      True{}
    case Sb.InAnswered{e, a}:
      True{}
    case Sb.InDropped{m}:
      True{}
    case Sb.WrQueued{}:
      False{}
    case Sb.WrPlaced{e}:
      False{}
    case Sb.WrDropped{}:
      False{}

# settling an unsettled submission unanswered: an input keeps its entry
def drop_spec.kind(input: Bool, m: Maybe<&2, Nat>) -> Sb.Out:
  match input:
    case True{}:
      Sb.Moves{Sb.InDropped{m}}
    case False{}:
      Sb.Moves{Sb.WrDropped{}}

def drop_spec(+s: Sb.Sub) -> Sb.Out:
  drop_spec.kind(input_spec(s), entry_spec(s))

def change_spec(+s: Sb.Sub, c: Sb.Change) -> Sb.Out:
  match c:
    case Sb.Place{e}:
      place_spec(s, e)
    case Sb.Answer{a}:
      answer_spec(s, a)
    case Sb.Drop{}:
      drop_spec(s)

def step_spec.settled(b: Bool, +s: Sb.Sub, c: Sb.Change) -> Sb.Out:
  match b:
    case True{}:
      Sb.Stays{}
    case False{}:
      change_spec(s, c)

# the outcome of change c on s: a settled submission stays; else the change
def step_spec(+s: Sb.Sub, c: Sb.Change) -> Sb.Out:
  step_spec.settled(settled_spec(s), s, c)

# how far s is: 0 queued, 1 placed input, 2 settled
def rank_spec(s: Sb.Sub) -> Nat:
  match s:
    case Sb.InQueued{}:
      0n
    case Sb.InPlaced{e}:
      1n
    case Sb.InAnswered{e, a}:
      2n
    case Sb.InDropped{m}:
      2n
    case Sb.WrQueued{}:
      0n
    case Sb.WrPlaced{e}:
      2n
    case Sb.WrDropped{}:
      2n

# an entry s had is the entry n has
def kept_entry(m: Maybe<&2, Nat>, k: Maybe<&2, Nat>) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{e}:
      match k:
        case None{}:
          False{}
        case Some{f}:
          Nat.is_eq(e, f)

# a move of s keeps its type, moves it forward, and keeps a user entry it
# already had
def moves_ok.to(+s: Sb.Sub, +n: Sb.Sub) -> Bool:
  Bool.and(Bool.not(Bool.xor(input_spec(s), input_spec(n))), Bool.and(Nat.is_lt(rank_spec(s), rank_spec(n)), kept_entry(entry_spec(s), entry_spec(n))))

def moves_ok(+s: Sb.Sub, o: Sb.Out) -> Bool:
  match o:
    case Sb.Stays{}:
      True{}
    case Sb.Moves{n}:
      moves_ok.to(s, n)
    case Sb.Refused{y}:
      True{}

# Laws
# ----

# LAW submission_step_exact: a settled submission stays; else placing, answering or settling unanswered gives the outcome of R2-R4
# EXCLUDES: a settled submission reopened or refused, a placed input
#   placed again, an answer to a queued input or a write, a lost or swapped
#   entry or answer id, an unanswered input that loses its user entry,
#   the two refusals swapped
law submission_step_exact:
  for +s: Sb.Sub
  for c: Sb.Change
  {Sb.step(s, c) == step_spec(s, c) : Sb.Out}

# LAW submission_settled_stays: a settled submission stays, whatever the change
# EXCLUDES: a settled record rewritten (an answer changed, an unanswered
#   input answered), a refusal of a change to a settled submission
law submission_settled_stays:
  for +s: Sb.Sub
  for c: Sb.Change
  for done: {settled_spec(s) == True{} : Bool}
  {Sb.step(s, c) == Sb.Stays{} : Sb.Out}

# LAW submission_moves_forward: a move keeps the submission's type, moves it forward (queued, placed, settled), and keeps a user entry it had
# EXCLUDES: an input turned into a write, a submission sent back to
#   queued, a move that stays in place, an entry changed or dropped
law submission_moves_forward:
  for +s: Sb.Sub
  for c: Sb.Change
  {moves_ok(s, Sb.step(s, c)) == True{} : Bool}

# LAW submission_example: anchor: a queued input is placed at entry 7, then answered by 9; a queued write placed is settled; a placed write refuses an answer by staying
# EXCLUDES: a spec that is wrong on the session's sequence
law submission_example:
  {Sb.step(Sb.InQueued{}, Sb.Place{7n}) == Sb.Moves{Sb.InPlaced{7n}} : Sb.Out} &
  {Sb.step(Sb.InPlaced{7n}, Sb.Answer{9n}) == Sb.Moves{Sb.InAnswered{7n, 9n}} : Sb.Out} &
  {Sb.step(Sb.WrQueued{}, Sb.Place{3n}) == Sb.Moves{Sb.WrPlaced{3n}} : Sb.Out} &
  {Sb.step(Sb.WrPlaced{3n}, Sb.Answer{9n}) == Sb.Stays{} : Sb.Out} &
  {Sb.step(Sb.InQueued{}, Sb.Answer{9n}) == Sb.Refused{Sb.NotPlacedInput{}} : Sb.Out} &
  {Sb.step(Sb.InPlaced{7n}, Sb.Drop{}) == Sb.Moves{Sb.InDropped{Some{7n}}} : Sb.Out}

# LAWS (R5): the entry of the compiled Bend core that runs the step
# (bend/ffi_submission.bend, called by crates/eukhe-durable session
# commits through `eukhe_bend::rules::submission`). Each law is an open
# claim about FSb.ffi, stated with spec spellers built only from the wire
# primitives of bend/wire.bend (their round trips: laws/wire.bend).
#
# R5: a request is the submission (tag 0 queued input, 1 placed input and
#     its entry, 2 answered input, its entry and answer, 3 input
#     unanswered before placement, 4 input unanswered and its entry, 5
#     queued write, 6 placed write and its entry, 7 unanswered write), then
#     the change (tag 0 place and the entry, 1 answer and the answer
#     entry, 2 settle unanswered); the reply is the outcome (tag 0 stays,
#     1 moves and the next submission, 2 refused and why: 0 not queued, 1
#     not a placed input). A malformed request answers the error form
#     "submission: malformed request", input left after the request
#     "submission: input left after the request", never a default.

# Spec spellers
# -------------

def spell_sub(s: Sb.Sub, rest: String) -> String:
  match s:
    case Sb.InQueued{}:
      Wr.put_nat(0n, rest)
    case Sb.InPlaced{e}:
      Wr.put_nat(1n, Wr.put_nat(e, rest))
    case Sb.InAnswered{e, a}:
      Wr.put_nat(2n, Wr.put_nat(e, Wr.put_nat(a, rest)))
    case Sb.InDropped{m}:
      match m:
        case None{}:
          Wr.put_nat(3n, rest)
        case Some{e}:
          Wr.put_nat(4n, Wr.put_nat(e, rest))
    case Sb.WrQueued{}:
      Wr.put_nat(5n, rest)
    case Sb.WrPlaced{e}:
      Wr.put_nat(6n, Wr.put_nat(e, rest))
    case Sb.WrDropped{}:
      Wr.put_nat(7n, rest)

def spell_change(c: Sb.Change, rest: String) -> String:
  match c:
    case Sb.Place{e}:
      Wr.put_nat(0n, Wr.put_nat(e, rest))
    case Sb.Answer{a}:
      Wr.put_nat(1n, Wr.put_nat(a, rest))
    case Sb.Drop{}:
      Wr.put_nat(2n, rest)

# the request: the submission, the change, then rest
def spell_req(s: Sb.Sub, c: Sb.Change, rest: String) -> String:
  spell_sub(s, spell_change(c, rest))

def spell_out(o: Sb.Out) -> String:
  match o:
    case Sb.Stays{}:
      Wr.put_nat(0n, "")
    case Sb.Moves{n}:
      Wr.put_nat(1n, spell_sub(n, ""))
    case Sb.Refused{y}:
      match y:
        case Sb.NotQueued{}:
          Wr.put_nat(2n, Wr.put_nat(0n, ""))
        case Sb.NotPlacedInput{}:
          Wr.put_nat(2n, Wr.put_nat(1n, ""))

# the submission of a request
def fst(q: Sb.Sub & Sb.Change) -> Sb.Sub:
  (s, c) = q
  s

# the change of a request
def snd(q: Sb.Sub & Sb.Change) -> Sb.Change:
  (s, c) = q
  c

# every id of s fits the wire
def sub_fits(s: Sb.Sub) -> Bool:
  match s:
    case Sb.InQueued{}:
      True{}
    case Sb.InPlaced{e}:
      LawsBase.wire_fits(e)
    case Sb.InAnswered{e, a}:
      Bool.and(LawsBase.wire_fits(e), LawsBase.wire_fits(a))
    case Sb.InDropped{m}:
      LawsBase.wire_mfits(m)
    case Sb.WrQueued{}:
      True{}
    case Sb.WrPlaced{e}:
      LawsBase.wire_fits(e)
    case Sb.WrDropped{}:
      True{}

def change_fits(c: Sb.Change) -> Bool:
  match c:
    case Sb.Place{e}:
      LawsBase.wire_fits(e)
    case Sb.Answer{a}:
      LawsBase.wire_fits(a)
    case Sb.Drop{}:
      True{}

# Laws
# ----

# LAW submission_ffi_answers: a spelled request whose ids fit the wire answers the spelled outcome of R1-R4
# EXCLUDES: a field misread or swapped (entry and answer), a tag of
#   another submission or change, an outcome in another spelling
law submission_ffi_answers:
  for +s: Sb.Sub
  for +c: Sb.Change
  for sf: {sub_fits(s) == True{} : Bool}
  for cf: {change_fits(c) == True{} : Bool}
  {FSb.ffi(spell_req(s, c, "")) == spell_out(step_spec(s, c)) : String}

# LAW submission_ffi_exact: every input the entry answers with a value (not the error form) is a spelled request
# EXCLUDES: a default outcome for a malformed request (an unknown tag, a
#   missing id) or one with input left over
law submission_ffi_exact:
  for +x: String
  for ok: {LawsBase.wire_opens_err(FSb.ffi(x)) == False{} : Bool}
  exs q: Sb.Sub & Sb.Change
  {x == spell_req(fst(q), snd(q), "") : String}

# LAW submission_ffi_left_over: a request followed by more input answers the left-over error form
# EXCLUDES: the input after the request ignored or read as another change
law submission_ffi_left_over:
  for +s: Sb.Sub
  for +c: Sb.Change
  for +h: Char
  for +t: String
  for sf: {sub_fits(s) == True{} : Bool}
  for cf: {change_fits(c) == True{} : Bool}
  {FSb.ffi(spell_req(s, c, SCon{h, t})) == Wr.err("submission: input left after the request") : String}

# LAW submission_ffi_example: anchor: the exact bytes Rust sends to answer input 7 with 9, and three refusals of malformed requests
# EXCLUDES: another spelling of a request or a reply, a default answer to
#   an unknown tag or a missing change
law submission_ffi_example:
  {FSb.ffi("1,7,1,9,") == "1,2,7,9," : String} &
  {FSb.ffi("0,1,9,") == "2,1," : String} &
  {FSb.ffi("8,2,") == Wr.err("submission: malformed request") : String} &
  {FSb.ffi("0,3,") == Wr.err("submission: malformed request") : String} &
  {FSb.ffi("0,") == Wr.err("submission: malformed request") : String}
