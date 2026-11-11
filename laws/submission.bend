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

# s is queued: an input or a write not yet placed (R2)
def queued_spec(s: Sb.Sub) -> Bool:
  match s:
    case Sb.InQueued{}:
      True{}
    case Sb.InPlaced{e}:
      False{}
    case Sb.InAnswered{e, a}:
      False{}
    case Sb.InDropped{m}:
      False{}
    case Sb.WrQueued{}:
      True{}
    case Sb.WrPlaced{e}:
      False{}
    case Sb.WrDropped{}:
      False{}

# s is an input placed at its user entry and not yet settled (R3)
def placed_input_spec(s: Sb.Sub) -> Bool:
  match s:
    case Sb.InQueued{}:
      False{}
    case Sb.InPlaced{e}:
      True{}
    case Sb.InAnswered{e, a}:
      False{}
    case Sb.InDropped{m}:
      False{}
    case Sb.WrQueued{}:
      False{}
    case Sb.WrPlaced{e}:
      False{}
    case Sb.WrDropped{}:
      False{}

# s is settled unanswered (R4)
def unanswered_spec(s: Sb.Sub) -> Bool:
  match s:
    case Sb.InQueued{}:
      False{}
    case Sb.InPlaced{e}:
      False{}
    case Sb.InAnswered{e, a}:
      False{}
    case Sb.InDropped{m}:
      True{}
    case Sb.WrQueued{}:
      False{}
    case Sb.WrPlaced{e}:
      False{}
    case Sb.WrDropped{}:
      True{}

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

# LAW submission_place (R2): placing a queued input at entry e places it
# at e, and placing a queued write at e settles it written at e, for every e
# EXCLUDES: a placed entry other than the change's, an input placed as a
#   write or a write left placed-but-open, a placing refused
law submission_place:
  for e: Nat
  {Sb.step(Sb.InQueued{}, Sb.Place{e}) == Sb.Moves{Sb.InPlaced{e}} : Sb.Out} & {Sb.step(Sb.WrQueued{}, Sb.Place{e}) == Sb.Moves{Sb.WrPlaced{e}} : Sb.Out}

# LAW submission_place_refused (R2): placing a submission that is neither
# settled nor queued (a placed input) is refused as not queued, at every
# entry
# EXCLUDES: a placed input placed again (moved to another entry), the
#   other refusal reason
law submission_place_refused:
  for +s: Sb.Sub
  for e: Nat
  for open: {settled_spec(s) == False{} : Bool}
  for nq: {queued_spec(s) == False{} : Bool}
  {Sb.step(s, Sb.Place{e}) == Sb.Refused{Sb.NotQueued{}} : Sb.Out}

# LAW submission_answer (R3): answering an input placed at entry e with the
# answer entry a settles it answered at e with a, for every e and a
# EXCLUDES: the user entry lost or swapped with the answer, a placed input
#   answered with a refusal
law submission_answer:
  for e: Nat
  for a: Nat
  {Sb.step(Sb.InPlaced{e}, Sb.Answer{a}) == Sb.Moves{Sb.InAnswered{e, a}} : Sb.Out}

# LAW submission_answer_refused (R3): answering a submission that is
# neither settled nor a placed input (a queued input, a queued write) is
# refused as not a placed input, for every answer entry
# EXCLUDES: an answer to a queued input or a write accepted, the other
#   refusal reason
law submission_answer_refused:
  for +s: Sb.Sub
  for a: Nat
  for open: {settled_spec(s) == False{} : Bool}
  for np: {placed_input_spec(s) == False{} : Bool}
  {Sb.step(s, Sb.Answer{a}) == Sb.Refused{Sb.NotPlacedInput{}} : Sb.Out}

# LAW submission_drop (R4): settling unanswered a submission that is not
# settled moves it to a submission settled unanswered of the same type
# (input or write) with the same user entry (the placed input's entry,
# none for a queued one); type, unanswered and entry fix that submission
# EXCLUDES: a drop refused, an input dropped as a write, a placed input
#   that loses its user entry, a queued input that gains one, a drop
#   recorded as answered
law submission_drop:
  for +s: Sb.Sub
  for open: {settled_spec(s) == False{} : Bool}
  exs n: Sb.Sub
  {Sb.step(s, Sb.Drop{}) == Sb.Moves{n} : Sb.Out} & {unanswered_spec(n) == True{} : Bool} & {input_spec(n) == input_spec(s) : Bool} & {entry_spec(n) == entry_spec(s) : Maybe<&2, Nat>}

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
# EXCLUDES: a step that is wrong on the session's sequence
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

# LAW submission_ffi_answers (R5): a spelled request whose ids fit the
# wire answers the spelled outcome of the step (whose outcomes R1-R4 and
# the laws above pin)
# EXCLUDES: a field misread or swapped (entry and answer), a tag of
#   another submission or change, an outcome in another spelling, an
#   outcome other than the step's
law submission_ffi_answers:
  for +s: Sb.Sub
  for +c: Sb.Change
  for sf: {sub_fits(s) == True{} : Bool}
  for cf: {change_fits(c) == True{} : Bool}
  {FSb.ffi(spell_req(s, c, "")) == spell_out(Sb.step(s, c)) : String}

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

# LAW submission_ffi_bad_submission (R5): input that opens with a
# submission tag past 7 (fitting the wire) answers exactly the malformed
# error form, whatever follows
# EXCLUDES: an unknown submission tag read as a known one (a default
#   submission), another error text
law submission_ffi_bad_submission:
  for +k: Nat
  for +x: String
  for fit: {LawsBase.wire_fits(8n+k) == True{} : Bool}
  {FSb.ffi(Wr.put_nat(8n+k, x)) == Wr.err("submission: malformed request") : String}

# LAW submission_ffi_bad_change (R5): a spelled submission whose ids fit,
# then a change tag past 2 (fitting the wire), answers exactly the
# malformed error form, whatever follows
# EXCLUDES: an unknown change tag read as a known change (a default
#   change), the left-over error text for it
law submission_ffi_bad_change:
  for +s: Sb.Sub
  for +k: Nat
  for +x: String
  for sf: {sub_fits(s) == True{} : Bool}
  for fit: {LawsBase.wire_fits(3n+k) == True{} : Bool}
  {FSb.ffi(spell_sub(s, Wr.put_nat(3n+k, x))) == Wr.err("submission: malformed request") : String}

# LAW submission_ffi_no_change (R5): a spelled submission whose ids fit
# and nothing after it (the change missing) answers exactly the malformed
# error form
# EXCLUDES: a default change for a request cut after its submission
law submission_ffi_no_change:
  for +s: Sb.Sub
  for sf: {sub_fits(s) == True{} : Bool}
  {FSb.ffi(spell_sub(s, "")) == Wr.err("submission: malformed request") : String}

# a request: the submission and the change
type SpecReq is Data:
  SpecReq{sub: Sb.Sub, change: Sb.Change}

# a change with one id: k 0 place, 1 answer
def read_change.one(r: Wr.Dec<Nat>, k: Nat) -> Wr.Dec<Sb.Change>:
  match r:
    case Wr.Got{n, s}:
      match k:
        case 0n:
          Wr.Got{Sb.Place{n}, s}
        case 1n+u:
          Wr.Got{Sb.Answer{n}, s}
    case Wr.Bad{}:
      Wr.Bad{}

# a change: 0 place and the entry, 1 answer and the answer entry, 2 settle
# unanswered
def read_change(r: Wr.Dec<Nat>) -> Wr.Dec<Sb.Change>:
  match r:
    case Wr.Got{t, s}:
      match t:
        case 0n:
          read_change.one(Wr.get_nat(s), 0n)
        case 1n:
          read_change.one(Wr.get_nat(s), 1n)
        case 2n:
          Wr.Got{Sb.Drop{}, s}
        case 3n+u:
          Wr.Bad{}
    case Wr.Bad{}:
      Wr.Bad{}

def read_req.change(x: Sb.Sub, r: Wr.Dec<Sb.Change>) -> Wr.Dec<SpecReq>:
  match r:
    case Wr.Got{c, s}:
      Wr.Got{SpecReq{x, c}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def read_req(r: Wr.Dec<Sb.Sub>) -> Wr.Dec<SpecReq>:
  match r:
    case Wr.Got{x, s}:
      read_req.change(x, read_change(Wr.get_nat(s)))
    case Wr.Bad{}:
      Wr.Bad{}

# a submission with one id: k 0 placed input, 1 input unanswered at its
# entry, 2 placed write
def read_sub.one(r: Wr.Dec<Nat>, k: Nat) -> Wr.Dec<Sb.Sub>:
  match r:
    case Wr.Got{e, s}:
      match k:
        case 0n:
          Wr.Got{Sb.InPlaced{e}, s}
        case 1n:
          Wr.Got{Sb.InDropped{Some{e}}, s}
        case 2n+u:
          Wr.Got{Sb.WrPlaced{e}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def read_sub.answer(e: Nat, r: Wr.Dec<Nat>) -> Wr.Dec<Sb.Sub>:
  match r:
    case Wr.Got{a, s}:
      Wr.Got{Sb.InAnswered{e, a}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def read_sub.two(r: Wr.Dec<Nat>) -> Wr.Dec<Sb.Sub>:
  match r:
    case Wr.Got{e, s}:
      read_sub.answer(e, Wr.get_nat(s))
    case Wr.Bad{}:
      Wr.Bad{}

# a submission: its tag (0 to 7, as R5 lists them), then its ids
def read_sub(r: Wr.Dec<Nat>) -> Wr.Dec<Sb.Sub>:
  match r:
    case Wr.Got{t, s}:
      match t:
        case 0n:
          Wr.Got{Sb.InQueued{}, s}
        case 1n:
          read_sub.one(Wr.get_nat(s), 0n)
        case 2n:
          read_sub.two(Wr.get_nat(s))
        case 3n:
          Wr.Got{Sb.InDropped{None{}}, s}
        case 4n:
          read_sub.one(Wr.get_nat(s), 1n)
        case 5n:
          Wr.Got{Sb.WrQueued{}, s}
        case 6n:
          read_sub.one(Wr.get_nat(s), 2n)
        case 7n:
          Wr.Got{Sb.WrDropped{}, s}
        case 8n+u:
          Wr.Bad{}
    case Wr.Bad{}:
      Wr.Bad{}

# the request s spells and the input after it, or Bad
def read_spec(s: String) -> Wr.Dec<SpecReq>:
  read_req(read_sub(Wr.get_nat(s)))

# LAW submission_ffi_malformed_exact: every input that spells no request (an unknown tag, a missing id or change) answers exactly the error form "submission: malformed request"
# EXCLUDES: another error text for a malformed request (the left-over text,
#   a made-up one), a default outcome
law submission_ffi_malformed_exact:
  for +x: String
  for no: {read_spec(x) == Wr.Bad{} : Wr.Dec<SpecReq>}
  {FSb.ffi(x) == Wr.err("submission: malformed request") : String}
