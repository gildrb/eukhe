# eukhe: the laws of area gateway_answer

import Base
import ../bend/gateway_answer.bend as Ga
import ../bend/ffi_gateway_answer.bend as FGa
import ../bend/wire.bend as Wr
import ./base.bend as LawsBase

# (D1) What a settled session event tells the Signal peer
# -------------------------------------------------------
# bend/gateway_answer.bend, run as the compiled core by
# bend/ffi_gateway_answer.bend (crates/eukhe-gateway answer.rs, called by
# gateway.rs for every event of the bound session). Every input is free:
# any event, any texts, any error.
#
# R1: a run that ends with no assistant message answers the failure
#     "the turn ended before the model answered. Send /status to see the
#     model"; one with an assistant message answers nothing.
# R2: an assistant message that stopped (stop or length) answers its text
#     blocks joined by a blank line ("\n\n"), unless that text is empty or
#     only whitespace (Rust `char::is_whitespace`): then nothing.
# R3: an assistant message that failed answers its error on one line; one
#     that was aborted answers a stop; a tool-use step answers nothing.
# R4: a turn end with no assistant message and an error answers that error
#     on one line; any other turn end answers nothing; every other event
#     answers nothing.
# R5: one line: the words of the reason (Rust `split_whitespace`) joined
#     by single spaces; a missing, empty or whitespace-only reason is
#     "the model request failed".
# R6: the entry answers each request Rust writes (every length within the
#     wire) with the answer of R1-R5, reads exactly the request and nothing
#     after it, and answers any other input with the exact error form
#     `E gateway_answer: malformed request`.

# Spec helpers
# ------------

# R2, R5: Rust's whitespace (`char::is_whitespace`: the Unicode
# White_Space property, 25 code points), by code point
def ga_ws() -> List<&2, U32>:
  [9, 10, 11, 12, 13, 32, 133, 160, 5760, 8192, 8193, 8194, 8195, 8196, 8197, 8198, 8199, 8200, 8201, 8202, 8232, 8233, 8239, 8287, 12288]

def ga_ws_in(+x: U32, xs: List<&2, U32>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case y <> rest:
      Bool.or(U32.is_eq(x, y), ga_ws_in(x, rest))

def ga_white(c: Char) -> Bool:
  ga_ws_in(Char.to_u32(c), ga_ws())

# R2: the text holds no char but whitespace
def ga_empty(s: String) -> Bool:
  match s:
    case SNil{}:
      True{}
    case SCon{c, t}:
      Bool.and(ga_white(c), ga_empty(t))

# R5: s holds no whitespace char
def ga_dense(s: String) -> Bool:
  match s:
    case SNil{}:
      True{}
    case SCon{c, t}:
      Bool.and(Bool.not(ga_white(c)), ga_dense(t))

# R5: a word: one char or more, none of them whitespace
def ga_word(s: String) -> Bool:
  match s:
    case SNil{}:
      False{}
    case SCon{c, t}:
      ga_dense(SCon{c, t})

# s is not empty
def ga_filled(s: String) -> Bool:
  match s:
    case SNil{}:
      False{}
    case SCon{c, t}:
      True{}

# R5 (and gateway_commands R1): a text written as its whitespace runs and
# the words between them
type GaText is Data:
  # the whitespace after the last word
  GaEnd{gap: String}
  # whitespace, then a word, then the rest of the text
  GaWord{gap: String, word: String, more: GaText}

# the text t writes
def ga_spell(t: GaText) -> String:
  match t:
    case GaEnd{g}:
      g
    case GaWord{g, w, m}:
      String.append(g, String.append(w, ga_spell(m)))

# the words of t, in order
def ga_words_of(t: GaText) -> List<&2, String>:
  match t:
    case GaEnd{g}:
      Nil{}
    case GaWord{g, w, m}:
      w <> ga_words_of(m)

# t holds a word
def ga_has_word(t: GaText) -> Bool:
  match t:
    case GaEnd{g}:
      False{}
    case GaWord{g, w, m}:
      True{}

# the gap before a word: whitespace only, and not empty after a word
# (first: no word before it)
def ga_gap(first: Bool, +g: String) -> Bool:
  match first:
    case True{}:
      ga_empty(g)
    case False{}:
      Bool.and(ga_empty(g), ga_filled(g))

# t is well formed: its gaps as ga_gap says, its words words, its last
# gap whitespace only (empty allowed). Every string is the spelling of one
# well formed text, whose words are its `split_whitespace` words.
def ga_well(t: GaText, first: Bool) -> Bool:
  match t:
    case GaEnd{g}:
      ga_empty(g)
    case GaWord{g, w, m}:
      Bool.and(ga_gap(first, g), Bool.and(ga_word(w), ga_well(m, False{})))

# R2: an assistant message that stopped (on stop or on length)
def ga_settled(s: Ga.Stop) -> Bool:
  match s:
    case Ga.SStop{}:
      True{}
    case Ga.SLength{}:
      True{}
    case Ga.SError{}:
      False{}
    case Ga.SAborted{}:
      False{}
    case Ga.SToolUse{}:
      False{}

# R5: a reason that names nothing: missing, empty or whitespace only
def ga_no_reason(m: Maybe<&2, String>) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{r}:
      ga_empty(r)

# R6: the spelling of a request and of its reply

def ga_w_stop(s: Ga.Stop) -> Nat:
  match s:
    case Ga.SStop{}:
      0n
    case Ga.SLength{}:
      1n
    case Ga.SError{}:
      2n
    case Ga.SAborted{}:
      3n
    case Ga.SToolUse{}:
      4n

def ga_w_maybe(m: Maybe<&2, String>, rest: String) -> String:
  match m:
    case None{}:
      Wr.put_nat(0n, rest)
    case Some{x}:
      Wr.put_nat(1n, Wr.put_str(x, rest))

def ga_w_req(ev: Ga.Ev, rest: String) -> String:
  match ev:
    case Ga.EAgentEnd{a}:
      Wr.put_nat(0n, Wr.put_bool(a, rest))
    case Ga.EAssistant{s, ts, e}:
      Wr.put_nat(1n, Wr.put_nat(ga_w_stop(s), Wr.put_list(~String, ~Wr.put_str, ts, ga_w_maybe(e, rest))))
    case Ga.ETurnEnd{a, e}:
      Wr.put_nat(2n, Wr.put_bool(a, ga_w_maybe(e, rest)))
    case Ga.EOther{}:
      Wr.put_nat(3n, rest)

def ga_w_reply(a: Ga.Answer) -> String:
  match a:
    case Ga.ANone{}:
      Wr.put_nat(0n, "")
    case Ga.AText{t}:
      Wr.put_nat(1n, Wr.put_str(t, ""))
    case Ga.AFailed{t}:
      Wr.put_nat(2n, Wr.put_str(t, ""))
    case Ga.AStopped{}:
      Wr.put_nat(3n, "")

def ga_fit_strs(xs: List<&2, String>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case x <> t:
      Bool.and(LawsBase.wire_fits(String.length(x)), ga_fit_strs(t))

def ga_fit_maybe(m: Maybe<&2, String>) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{x}:
      LawsBase.wire_fits(String.length(x))

# every number and length of the request fits the wire
def ga_fit(ev: Ga.Ev) -> Bool:
  match ev:
    case Ga.EAgentEnd{a}:
      True{}
    case Ga.EAssistant{s, +ts, e}:
      Bool.and(LawsBase.wire_fits(List.length(&2, String, ts)), Bool.and(ga_fit_strs(ts), ga_fit_maybe(e)))
    case Ga.ETurnEnd{a, e}:
      ga_fit_maybe(e)
    case Ga.EOther{}:
      True{}

# Laws: the answers
# -----------------

# LAW gateway_answer_run_end (R1): of the two run ends (the whole domain),
# the one with no assistant message answers the failure "the turn ended
# before the model answered. Send /status to see the model", the one with
# an assistant message answers nothing
# EXCLUDES: a silent phone after a run with no model, a second reply after
#   a run that answered, another failure text
law gateway_answer_run_end:
  {[Ga.answer(Ga.EAgentEnd{False{}}), Ga.answer(Ga.EAgentEnd{True{}})] == [Ga.AFailed{"the turn ended before the model answered. Send /status to see the model"}, Ga.ANone{}] : List<&2, Ga.Answer>}

# LAW gateway_answer_text (R2): an assistant message that stopped (stop or
# length), with every text blocks ts and every error, whose blocks joined
# by a blank line (Base String.join with "\n\n") hold a char that is no
# whitespace, answers exactly that joined text
# EXCLUDES: blocks joined otherwise, dropped, reordered or trimmed; a text
#   lost on length; the error sent instead of the text
law gateway_answer_text:
  for +s: Ga.Stop
  for +ts: List<&2, String>
  for e: Maybe<&2, String>
  for st: {ga_settled(s) == True{} : Bool}
  for full: {ga_empty(String.join(ts, "\n\n")) == False{} : Bool}
  {Ga.answer(Ga.EAssistant{s, ts, e}) == Ga.AText{String.join(ts, "\n\n")} : Ga.Answer}

# LAW gateway_answer_blank (R2): an assistant message that stopped (stop or
# length), with every error, whose blocks joined by a blank line are empty
# or whitespace only, answers nothing
# EXCLUDES: a blank or whitespace-only text sent, a whitespace test that
#   misses a Unicode space
law gateway_answer_blank:
  for +s: Ga.Stop
  for +ts: List<&2, String>
  for e: Maybe<&2, String>
  for st: {ga_settled(s) == True{} : Bool}
  for blank: {ga_empty(String.join(ts, "\n\n")) == True{} : Bool}
  {Ga.answer(Ga.EAssistant{s, ts, e}) == Ga.ANone{} : Ga.Answer}

# LAW gateway_answer_failed_line (R3, R5): a failed assistant message, with
# every text blocks, whose error is any text with at least one word (t: its
# whitespace runs and words, well formed) answers the failure of those
# words joined by single spaces (Base String.join with " ")
# EXCLUDES: an error on several lines or with its spacing kept, words
#   split at ASCII spaces only, a word dropped or reordered, the text
#   blocks sent instead of the error
law gateway_answer_failed_line:
  for ts: List<&2, String>
  for +t: GaText
  for +well: {ga_well(t, True{}) == True{} : Bool}
  for some: {ga_has_word(t) == True{} : Bool}
  {Ga.answer(Ga.EAssistant{Ga.SError{}, ts, Some{ga_spell(t)}}) == Ga.AFailed{String.join(ga_words_of(t), " ")} : Ga.Answer}

# LAW gateway_answer_failed_blank (R3, R5): a failed assistant message,
# with every text blocks, whose error is missing, empty or whitespace only
# answers the failure "the model request failed"
# EXCLUDES: a blank error sent as is, a failure answered with nothing
law gateway_answer_failed_blank:
  for ts: List<&2, String>
  for +e: Maybe<&2, String>
  for none: {ga_no_reason(e) == True{} : Bool}
  {Ga.answer(Ga.EAssistant{Ga.SError{}, ts, e}) == Ga.AFailed{"the model request failed"} : Ga.Answer}

# LAW gateway_answer_aborted (R3): an aborted assistant message, with every
# text blocks and every error, answers a stop
# EXCLUDES: a stop taken for a failure or sent as text
law gateway_answer_aborted:
  for ts: List<&2, String>
  for e: Maybe<&2, String>
  {Ga.answer(Ga.EAssistant{Ga.SAborted{}, ts, e}) == Ga.AStopped{} : Ga.Answer}

# LAW gateway_answer_tool_use (R3): a tool-use step, with every text blocks
# and every error, answers nothing
# EXCLUDES: the text before a tool call sent to the phone
law gateway_answer_tool_use:
  for ts: List<&2, String>
  for e: Maybe<&2, String>
  {Ga.answer(Ga.EAssistant{Ga.SToolUse{}, ts, e}) == Ga.ANone{} : Ga.Answer}

# LAW gateway_answer_turn_failed (R4, R5): a turn end with no assistant
# message and an error r answers what a failed assistant message with
# error r answers (its line: gateway_answer_failed_line, _failed_blank),
# for every r
# EXCLUDES: a turn error kept on several lines, a blank turn error sent as
#   is, a faulted turn answered with nothing
law gateway_answer_turn_failed:
  for +r: String
  {Ga.answer(Ga.ETurnEnd{False{}, Some{r}}) == Ga.answer(Ga.EAssistant{Ga.SError{}, [], Some{r}}) : Ga.Answer}

# LAW gateway_answer_quiet (R4): a turn end that carries its assistant
# message (every error), a turn end with neither message nor error, and
# every other event answer nothing
# EXCLUDES: a second reply for a turn that carries its message, a reply to
#   a quiet turn or to another event
law gateway_answer_quiet:
  for e: Maybe<&2, String>
  {[Ga.answer(Ga.ETurnEnd{True{}, e}), Ga.answer(Ga.ETurnEnd{False{}, None{}}), Ga.answer(Ga.EOther{})] == [Ga.ANone{}, Ga.ANone{}, Ga.ANone{}] : List<&2, Ga.Answer>}

# LAW gateway_answer_example (R1-R5): anchor: the two reasons of Rust's
# answer test (crates/eukhe-gateway/src/answer/tests.rs: the cloudflare
# key error and the faulted turn "worker\ncrashed") and ten more events: a
# run with no assistant message and one with, the turn end that carries its
# message, texts joined, a whitespace-only text, a blank error, an abort, a
# tool-use step, a quiet turn, another event
# EXCLUDES: a code that drifts from these vectors
law gateway_answer_example:
  {[Ga.answer(Ga.EAgentEnd{False{}}), Ga.answer(Ga.EAgentEnd{True{}}), Ga.answer(Ga.ETurnEnd{False{}, Some{"worker\ncrashed"}}), Ga.answer(Ga.EAssistant{Ga.SError{}, [], Some{"No API key for provider: cloudflare-ai-gateway"}}), Ga.answer(Ga.ETurnEnd{True{}, None{}}), Ga.answer(Ga.EAssistant{Ga.SStop{}, ["a", " b  c "], None{}}), Ga.answer(Ga.EAssistant{Ga.SLength{}, [" ", "\n"], None{}}), Ga.answer(Ga.EAssistant{Ga.SError{}, [], Some{" \t"}}), Ga.answer(Ga.EAssistant{Ga.SAborted{}, ["x"], None{}}), Ga.answer(Ga.EAssistant{Ga.SToolUse{}, ["x"], None{}}), Ga.answer(Ga.ETurnEnd{False{}, None{}}), Ga.answer(Ga.EOther{})] == [Ga.AFailed{"the turn ended before the model answered. Send /status to see the model"}, Ga.ANone{}, Ga.AFailed{"worker crashed"}, Ga.AFailed{"No API key for provider: cloudflare-ai-gateway"}, Ga.ANone{}, Ga.AText{"a\n\n b  c "}, Ga.ANone{}, Ga.AFailed{"the model request failed"}, Ga.AStopped{}, Ga.ANone{}, Ga.ANone{}, Ga.ANone{}] : List<&2, Ga.Answer>}

# Laws: the entry (R6)
# --------------------

# LAW gateway_answer_entry_answers (R6): the entry answers every request
# Rust spells, every length within the wire, with the spelled answer of
# the model Ga.answer (pinned by the laws of R1-R5 above)
# EXCLUDES: a field misread, swapped or dropped; a stop tag read as
#   another; a default
law gateway_answer_entry_answers:
  for +ev: Ga.Ev
  for h: {ga_fit(ev) == True{} : Bool}
  {FGa.ffi(ga_w_req(ev, "")) == ga_w_reply(Ga.answer(ev)) : String}

# LAW gateway_answer_entry_reads (R6): the entry's decoder reads a spelled
# request back whole and leaves the input after it untouched
# EXCLUDES: a decoder that eats or skips input after the request
law gateway_answer_entry_reads:
  for +ev: Ga.Ev
  for +rest: String
  for h: {ga_fit(ev) == True{} : Bool}
  {FGa.get_req(ga_w_req(ev, rest)) == Wr.Got{ev, rest} : Wr.Dec<Ga.Ev>}

# LAW gateway_answer_entry_exact (R6): every input the entry does not
# answer with the error form is a spelled request that fits the wire
# EXCLUDES: an answer made on input that is no request (an unknown tag, a
#   malformed field, input left over)
law gateway_answer_entry_exact:
  for +s: String
  for ok: {LawsBase.wire_opens_err(FGa.ffi(s)) == False{} : Bool}
  exs ev: Ga.Ev
  {s == ga_w_req(ev, "") : String} & {ga_fit(ev) == True{} : Bool}

# LAW gateway_answer_entry_refuses (R6): every error the entry answers is
# exactly `E gateway_answer: malformed request`
# EXCLUDES: an error text that varies with the input, a second error form
law gateway_answer_entry_refuses:
  for +s: String
  for bad: {LawsBase.wire_opens_err(FGa.ffi(s)) == True{} : Bool}
  {FGa.ffi(s) == Wr.err("gateway_answer: malformed request") : String}

# LAW gateway_answer_entry_example (R6): anchor: the wire strings Rust
# sends and the replies it reads; an unknown tag, a stop tag past the
# last and input left over
# EXCLUDES: tags in another order, a field order other than Rust's
law gateway_answer_entry_example:
  {[FGa.ffi("0,F"), FGa.ffi("1,0,2,1,a1,b0,"), FGa.ffi("1,2,0,1,3,x\ny"), FGa.ffi("1,3,0,0,"), FGa.ffi("2,T0,"), FGa.ffi("3,"), FGa.ffi("4,"), FGa.ffi("1,5,0,0,"), FGa.ffi("3,x")] == [Wr.put_nat(2n, Wr.put_str("the turn ended before the model answered. Send /status to see the model", "")), "1,4,a\n\nb", "2,3,x y", "3,", "0,", "0,", Wr.err("gateway_answer: malformed request"), Wr.err("gateway_answer: malformed request"), Wr.err("gateway_answer: malformed request")] : List<&2, String>}
