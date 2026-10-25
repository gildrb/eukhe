# eukhe: the laws of area retry_note

import Base
import ../bend/retry_note.bend as Rn
import ../bend/ffi_retry_note.bend as FRn
import ../bend/wire.bend as Wr
import ./base.bend as LawsBase

# LAWS (R1): the note at the end of a retry's request
# (bend/retry_note.bend, the port of eukhe-durable
# harness/generation/note.rs `RetryNote::text`). Each law is an open claim
# about Rn.text; PROOF.bend proves them (as RetryNote.<law>) with the
# lemmas of proof/retry_note/.
#
# R1: the note opens with "Harness note, attempt <attempt>: " and then
#     says what went wrong and what to do instead, one text per cause:
#     - a repeated cycle of one line names that line (already quoted by
#       the host); a cycle of any other count names the count and its last
#       line;
#     - no answer;
#     - the output limit while still reasoning: "the output limit" when
#       the provider reported no limit (0 tokens), else "the <tokens>-token
#       output limit"; then "Length note <row> of <cap>.";
#     - tool calls leaked as text: the markup and the reason; then "Leak
#       note <row> of <cap>.";
#     - repeated calls: the rounds, then each call as "`<tool>` with
#       `<args>`", the calls in order joined by "; "; then "Redirect note
#       <row> of <cap>.";
#     - a stall: the idle deadline in whole seconds (milliseconds divided
#       by 1000, rounded down).
#     Every attempt, count, text and list of calls is free.

# Terms
# -----

# the limit a length note names: none reported (0), or the reported one
def limit_spec.pick(none: Bool, tokens: Nat) -> String:
  match none:
    case True{}:
      "the output limit"
    case False{}:
      String.concat(["the ", Nat.show(tokens), "-token output limit"])

def limit_spec(+tokens: Nat) -> String:
  limit_spec.pick(Nat.is_eq(tokens, 0n), tokens)

# one repeated call, as the note shows it
def call_spec(c: Rn.Call) -> String:
  match c:
    case Rn.Call{t, a}:
      String.concat(["`", t, "` with `", a, "`"])

# the shown calls, in order
def shown_spec(cs: List<&2, Rn.Call>) -> List<&2, String>:
  match cs:
    case Nil{}:
      Nil{}
    case c <> r:
      call_spec(c) <> shown_spec(r)

# the note of the retry of `attempt` after a reply that repeated a cycle of
# `period` lines ending with the quoted `line`
def repeated_spec.pick(one: Bool, a: Nat, period: Nat, line: String) -> String:
  match one:
    case True{}:
      String.concat(["Harness note, attempt ", Nat.show(a), ": your previous reply repeated the line ", line, " until it was cut. Give the answer again; never list the same item twice."])
    case False{}:
      String.concat(["Harness note, attempt ", Nat.show(a), ": your previous reply repeated a cycle of ", Nat.show(period), " lines, ending with the line ", line, ", until it was cut. Give the answer again; never repeat the same lines."])

def repeated_spec(a: Nat, +period: Nat, line: String) -> String:
  repeated_spec.pick(Nat.is_eq(period, 1n), a, period, line)

# the note of the retry of `attempt` for cause c (the format strings of
# note.rs, one per cause)
def note_spec(a: Nat, c: Rn.Cause) -> String:
  match c:
    case Rn.Repeated{p, l}:
      repeated_spec(a, p, l)
    case Rn.NoAnswer{}:
      String.concat(["Harness note, attempt ", Nat.show(a), ": your previous reply gave no text and no tool call. Give the answer again, as text or as a tool call."])
    case Rn.Length{t, r, k}:
      String.concat(["Harness note, attempt ", Nat.show(a), ": your previous reply hit ", limit_spec(t), " while it was still reasoning. It gave no text and no tool call, so the harness discarded it with every tool call that it planned. If you plan the whole task again in your reasoning, you hit the same limit. Reason only about the next step, then call its tool. For a large answer (a file, a document, a long text), write a minimal working version first, then extend it with more edits in later turns. Length note ", Nat.show(r), " of ", Nat.show(k), "."])
    case Rn.Leaked{m, why, r, k}:
      String.concat(["Harness note, attempt ", Nat.show(a), ": your previous reply wrote a tool call as ", m, " markup in its text, and the harness could not read it (", why, "). No tool ran. Make the call again through the tool-calling interface, with its arguments as one JSON object that agrees with the schema of the tool. Do not write a tool call as text. If you need no tool, give the answer as plain text. Leak note ", Nat.show(r), " of ", Nat.show(k), "."])
    case Rn.Redirect{cs, n, r, k}:
      String.concat(["Harness note, attempt ", Nat.show(a), ": you made the same tool calls ", Nat.show(n), " times in a row, and they gave the same results each time: ", String.join(shown_spec(cs), "; "), ". The harness did not run them again. Do not make these calls with these arguments again in this turn. Use different arguments, use a different tool, or give your answer with what you found. Redirect note ", Nat.show(r), " of ", Nat.show(k), "."])
    case Rn.Stalled{ms}:
      String.concat(["Harness note, attempt ", Nat.show(a), ": your previous reply produced no output for ", Nat.show(Nat.div(ms, 1000n)), " s, so the harness cut it. Reason briefly, then act: give the answer or call the tool of the next step."])

# Laws
# ----

# LAW retry_note_exact: the note of every attempt and cause is the text of R1: the opening with the attempt, then the cause's text with its counts, its quoted line or markup and reason, its calls joined by "; ", or its whole seconds
# EXCLUDES: another attempt, a cycle text for one line or a line text for
#   a cycle, a limit named when none was reported (or none named when one
#   was), a row and a cap swapped, calls dropped, reordered, joined by
#   another separator or with one after the last, milliseconds shown as
#   seconds or rounded up, any changed word
law retry_note_exact:
  for a: Nat
  for c: Rn.Cause
  {Rn.text(a, c) == note_spec(a, c) : String}

# LAW retry_note_example: anchor: the notes note.rs writes for a repeated line, a cycle, no answer, an unreported limit, a stall of 2.5 s, and two repeated calls
# EXCLUDES: a spec that is wrong on the shipped texts
law retry_note_example:
  {Rn.text(2n, Rn.Repeated{1n, "\"- a\""}) == "Harness note, attempt 2: your previous reply repeated the line \"- a\" until it was cut. Give the answer again; never list the same item twice." : String} &
  {Rn.text(3n, Rn.Repeated{4n, "\"x\""}) == "Harness note, attempt 3: your previous reply repeated a cycle of 4 lines, ending with the line \"x\", until it was cut. Give the answer again; never repeat the same lines." : String} &
  {Rn.text(2n, Rn.NoAnswer{}) == "Harness note, attempt 2: your previous reply gave no text and no tool call. Give the answer again, as text or as a tool call." : String} &
  {Rn.text(2n, Rn.Stalled{2500n}) == "Harness note, attempt 2: your previous reply produced no output for 2 s, so the harness cut it. Reason briefly, then act: give the answer or call the tool of the next step." : String} &
  {Rn.text(5n, Rn.Redirect{[Rn.Call{"read", "{\"path\":\"a\"}"}, Rn.Call{"ls", "{}"}], 3n, 1n, 2n}) == "Harness note, attempt 5: you made the same tool calls 3 times in a row, and they gave the same results each time: `read` with `{\"path\":\"a\"}`; `ls` with `{}`. The harness did not run them again. Do not make these calls with these arguments again in this turn. Use different arguments, use a different tool, or give your answer with what you found. Redirect note 1 of 2." : String}

# LAW retry_note_limit_example: anchor: a length note names the reported limit, or the output limit when none was reported
# EXCLUDES: "the 0-token output limit"; a limit dropped
law retry_note_limit_example:
  {Rn.text(2n, Rn.Length{0n, 1n, 3n}) == "Harness note, attempt 2: your previous reply hit the output limit while it was still reasoning. It gave no text and no tool call, so the harness discarded it with every tool call that it planned. If you plan the whole task again in your reasoning, you hit the same limit. Reason only about the next step, then call its tool. For a large answer (a file, a document, a long text), write a minimal working version first, then extend it with more edits in later turns. Length note 1 of 3." : String} &
  {Rn.text(4n, Rn.Length{8192n, 3n, 3n}) == "Harness note, attempt 4: your previous reply hit the 8192-token output limit while it was still reasoning. It gave no text and no tool call, so the harness discarded it with every tool call that it planned. If you plan the whole task again in your reasoning, you hit the same limit. Reason only about the next step, then call its tool. For a large answer (a file, a document, a long text), write a minimal working version first, then extend it with more edits in later turns. Length note 3 of 3." : String} &
  {Rn.text(2n, Rn.Leaked{"DSML", "no closing tag", 2n, 2n}) == "Harness note, attempt 2: your previous reply wrote a tool call as DSML markup in its text, and the harness could not read it (no closing tag). No tool ran. Make the call again through the tool-calling interface, with its arguments as one JSON object that agrees with the schema of the tool. Do not write a tool call as text. If you need no tool, give the answer as plain text. Leak note 2 of 2." : String}

# LAWS (R2): the entry of the compiled Bend core that writes the note
# (bend/ffi_retry_note.bend, called by crates/eukhe-durable generation
# through `eukhe_bend::rules::retry_note`). Each law is an open claim about
# FRn.ffi, stated with spec spellers built only from the wire primitives of
# bend/wire.bend (their round trips: laws/wire.bend).
#
# R2: a request is the attempt (a Nat), then the cause: its tag (0
#     repeated, 1 no answer, 2 length, 3 leaked, 4 redirect, 5 stalled),
#     then its fields in the order of Rn.Cause (a list of calls is its
#     count, then each call's tool and arguments). The reply is the note's
#     text (a String). A malformed request answers the error form
#     "retry_note: malformed request", input left after the request
#     "retry_note: input left after the request", never a default.

# Spec spellers
# -------------

# one call: its tool, then its arguments
def spell_call(c: Rn.Call, rest: String) -> String:
  match c:
    case Rn.Call{t, a}:
      Wr.put_str(t, Wr.put_str(a, rest))

# a cause: its tag, then its fields
def spell_cause(c: Rn.Cause, rest: String) -> String:
  match c:
    case Rn.Repeated{p, l}:
      Wr.put_nat(0n, Wr.put_nat(p, Wr.put_str(l, rest)))
    case Rn.NoAnswer{}:
      Wr.put_nat(1n, rest)
    case Rn.Length{t, r, k}:
      Wr.put_nat(2n, Wr.put_nat(t, Wr.put_nat(r, Wr.put_nat(k, rest))))
    case Rn.Leaked{m, why, r, k}:
      Wr.put_nat(3n, Wr.put_str(m, Wr.put_str(why, Wr.put_nat(r, Wr.put_nat(k, rest)))))
    case Rn.Redirect{cs, n, r, k}:
      Wr.put_nat(4n, Wr.put_list(~Rn.Call, ~spell_call, cs, Wr.put_nat(n, Wr.put_nat(r, Wr.put_nat(k, rest)))))
    case Rn.Stalled{ms}:
      Wr.put_nat(5n, Wr.put_nat(ms, rest))

# the request: the attempt, the cause, then rest
def spell_req(q: FRn.Req, rest: String) -> String:
  match q:
    case FRn.Req{a, c}:
      Wr.put_nat(a, spell_cause(c, rest))

# every text of the calls fits the wire
def calls_fit(cs: List<&2, Rn.Call>) -> Bool:
  match cs:
    case Nil{}:
      True{}
    case c <> r:
      match c:
        case Rn.Call{+t, +a}:
          Bool.and(Bool.and(LawsBase.wire_fits(String.length(t)), LawsBase.wire_fits(String.length(a))), calls_fit(r))

# every number, text and count of c fits the wire
def cause_fits(c: Rn.Cause) -> Bool:
  match c:
    case Rn.Repeated{+p, +l}:
      Bool.and(LawsBase.wire_fits(p), LawsBase.wire_fits(String.length(l)))
    case Rn.NoAnswer{}:
      True{}
    case Rn.Length{+t, +r, +k}:
      Bool.and(LawsBase.wire_fits(t), Bool.and(LawsBase.wire_fits(r), LawsBase.wire_fits(k)))
    case Rn.Leaked{+m, +why, +r, +k}:
      Bool.and(Bool.and(LawsBase.wire_fits(String.length(m)), LawsBase.wire_fits(String.length(why))), Bool.and(LawsBase.wire_fits(r), LawsBase.wire_fits(k)))
    case Rn.Redirect{+cs, +n, +r, +k}:
      Bool.and(Bool.and(LawsBase.wire_fits(List.length(&2, Rn.Call, cs)), calls_fit(cs)), Bool.and(LawsBase.wire_fits(n), Bool.and(LawsBase.wire_fits(r), LawsBase.wire_fits(k))))
    case Rn.Stalled{+ms}:
      LawsBase.wire_fits(ms)

# every number, text and count of the request fits the wire
def req_fits(q: FRn.Req) -> Bool:
  match q:
    case FRn.Req{+a, c}:
      Bool.and(LawsBase.wire_fits(a), cause_fits(c))

# the note a request asks for
def req_note(q: FRn.Req) -> String:
  match q:
    case FRn.Req{a, c}:
      note_spec(a, c)

# a request with more input after it: the request, then a char and the rest
type LeftOver is Data:
  LeftOver{req: FRn.Req, head: Char, tail: String}

# the request of a left-over input
def left_req(w: LeftOver) -> FRn.Req:
  match w:
    case LeftOver{q, h, t}:
      q

def spell_left_over(w: LeftOver) -> String:
  match w:
    case LeftOver{q, h, t}:
      spell_req(q, SCon{h, t})

# Laws
# ----

# LAW retry_note_ffi_answers: a spelled request that fits the wire answers the spelled note of R1
# EXCLUDES: a field misread or swapped (row and cap, markup and reason, a
#   call's tool and arguments), a cause of another tag, a call lost or
#   added, a reply in another spelling
law retry_note_ffi_answers:
  for +q: FRn.Req
  for fit: {req_fits(q) == True{} : Bool}
  {FRn.ffi(spell_req(q, "")) == Wr.put_str(req_note(q), "") : String}

# LAW retry_note_ffi_exact: every input the entry answers with a value (not the error form) is a spelled request whose numbers, texts and counts fit the wire
# EXCLUDES: a default note for a malformed request (an unknown tag, a
#   missing field, a short list), one with input left over, or one with a
#   Nat of 15 or more digits (an attempt, period, count, row, cap or text
#   length past the wire)
law retry_note_ffi_exact:
  for +s: String
  for ok: {LawsBase.wire_opens_err(FRn.ffi(s)) == False{} : Bool}
  exs q: FRn.Req
  {s == spell_req(q, "") : String} & {req_fits(q) == True{} : Bool}

# LAW retry_note_ffi_left_over: a request that fits the wire, followed by more input, answers the left-over error form
# EXCLUDES: the input after the request ignored or read as part of it
law retry_note_ffi_left_over:
  for +q: FRn.Req
  for +h: Char
  for +t: String
  for fit: {req_fits(q) == True{} : Bool}
  {FRn.ffi(spell_req(q, SCon{h, t})) == Wr.err("retry_note: input left after the request") : String}

# LAW retry_note_ffi_left_over_exact: the entry answers the left-over error form only for a spelled request that fits the wire, followed by more input
# EXCLUDES: the left-over text for a malformed request (an over-long Nat
#   included)
law retry_note_ffi_left_over_exact:
  for +s: String
  for e: {FRn.ffi(s) == Wr.err("retry_note: input left after the request") : String}
  exs w: LeftOver
  {s == spell_left_over(w) : String} & {req_fits(left_req(w)) == True{} : Bool}

# LAW retry_note_ffi_errors: every error the entry answers is the malformed or the left-over error form; with retry_note_ffi_exact and retry_note_ffi_left_over_exact, every input that spells no request answers exactly "retry_note: malformed request"
# EXCLUDES: another error text (a made-up one, the text of another entry)
law retry_note_ffi_errors:
  for +s: String
  for e: {LawsBase.wire_opens_err(FRn.ffi(s)) == True{} : Bool}
  {Bool.or(LawsBase.text_same(FRn.ffi(s), Wr.err("retry_note: malformed request")), LawsBase.text_same(FRn.ffi(s), Wr.err("retry_note: input left after the request"))) == True{} : Bool}

# LAW retry_note_ffi_example: anchor: the exact bytes Rust sends for a stall and for two repeated calls, and three refusals
# EXCLUDES: another spelling of a request or of a reply, a default note
#   for an unknown tag or a short list
law retry_note_ffi_example:
  {FRn.ffi("2,5,2500,") == Wr.put_str("Harness note, attempt 2: your previous reply produced no output for 2 s, so the harness cut it. Reason briefly, then act: give the answer or call the tool of the next step.", "") : String} &
  {FRn.ffi("5,4,2,4,read2,{}2,ls2,{}3,1,2,") == Wr.put_str("Harness note, attempt 5: you made the same tool calls 3 times in a row, and they gave the same results each time: `read` with `{}`; `ls` with `{}`. The harness did not run them again. Do not make these calls with these arguments again in this turn. Use different arguments, use a different tool, or give your answer with what you found. Redirect note 1 of 2.", "") : String} &
  {FRn.ffi("2,6,") == Wr.err("retry_note: malformed request") : String} &
  {FRn.ffi("5,4,2,4,read2,{}3,1,2,") == Wr.err("retry_note: malformed request") : String} &
  {FRn.ffi("2,1,x") == Wr.err("retry_note: input left after the request") : String}
