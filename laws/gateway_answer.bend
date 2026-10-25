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

# R2, R5: Rust's whitespace, by code point
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

# a word starts s
def ga_opens(s: String) -> Bool:
  match s:
    case SNil{}:
      False{}
    case SCon{c, t}:
      Bool.not(ga_white(c))

def ga_onto(c: Char, ws: List<&2, String>) -> List<&2, String>:
  match ws:
    case Nil{}:
      [SCon{c, SNil{}}]
    case w <> rest:
      SCon{c, w} <> rest

def ga_split.at(white: Bool, more: Bool, c: Char, ws: List<&2, String>) -> List<&2, String>:
  match white more:
    case True{} True{}:
      ws
    case True{} False{}:
      ws
    case False{} True{}:
      ga_onto(c, ws)
    case False{} False{}:
      SCon{c, SNil{}} <> ws

# R5: the words of s (Rust `split_whitespace`): a char that is no
# whitespace joins the word that follows it, if one starts right after it
def ga_split(s: String) -> List<&2, String>:
  match s:
    case SNil{}:
      Nil{}
    case SCon{+c, +t}:
      ga_split.at(ga_white(c), ga_opens(t), c, ga_split(t))

def ga_glue.more(+sep: String, ws: List<&2, String>) -> String:
  match ws:
    case Nil{}:
      SNil{}
    case w <> rest:
      String.append(sep, String.append(w, ga_glue.more(sep, rest)))

# ws joined by sep (Rust `join`)
def ga_glue(+sep: String, ws: List<&2, String>) -> String:
  match ws:
    case Nil{}:
      SNil{}
    case w <> rest:
      String.append(w, ga_glue.more(sep, rest))

def ga_line.pick(+s: String, blank: Bool) -> String:
  match blank:
    case True{}:
      "the model request failed"
    case False{}:
      ga_glue(" ", ga_split(s))

# R5
def ga_line(m: Maybe<&2, String>) -> String:
  match m:
    case None{}:
      "the model request failed"
    case Some{+s}:
      ga_line.pick(s, ga_empty(s))

def ga_text.pick(+t: String, blank: Bool) -> Ga.Answer:
  match blank:
    case True{}:
      Ga.ANone{}
    case False{}:
      Ga.AText{t}

# R2
def ga_text(ts: List<&2, String>) -> Ga.Answer:
  +t = ga_glue("\n\n", ts)
  ga_text.pick(t, ga_empty(t))

# R1-R4: the answer of an event
def ga_answer(ev: Ga.Ev) -> Ga.Answer:
  match ev:
    case Ga.EAgentEnd{a}:
      match a:
        case True{}:
          Ga.ANone{}
        case False{}:
          Ga.AFailed{"the turn ended before the model answered. Send /status to see the model"}
    case Ga.EAssistant{s, ts, e}:
      match s:
        case Ga.SStop{}:
          ga_text(ts)
        case Ga.SLength{}:
          ga_text(ts)
        case Ga.SError{}:
          Ga.AFailed{ga_line(e)}
        case Ga.SAborted{}:
          Ga.AStopped{}
        case Ga.SToolUse{}:
          Ga.ANone{}
    case Ga.ETurnEnd{a, e}:
      match a:
        case True{}:
          Ga.ANone{}
        case False{}:
          match e:
            case None{}:
              Ga.ANone{}
            case Some{r}:
              Ga.AFailed{ga_line(Some{r})}
    case Ga.EOther{}:
      Ga.ANone{}

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

# LAW gateway_answer_spec (R1-R5): the answer of every event is the spec's
# EXCLUDES: a silent phone after a run with no model, a blank text sent,
#   text blocks joined otherwise or dropped, a thinking block sent, an
#   error on several lines or with its spacing kept, a blank error sent as
#   is, a second reply for a turn that carries its message, a stop taken
#   for a failure
law gateway_answer_spec:
  for ev: Ga.Ev
  {Ga.answer(ev) == ga_answer(ev) : Ga.Answer}

# LAW gateway_answer_example (R1-R5): anchor: Rust's vectors: a run with
# no assistant message, a faulted turn, a failed request and the turn end
# that carries it; texts joined, a whitespace-only text, a blank error, an
# abort, a tool-use step
# EXCLUDES: a spec that drifts from the Rust it replaced
law gateway_answer_example:
  {[Ga.answer(Ga.EAgentEnd{False{}}), Ga.answer(Ga.EAgentEnd{True{}}), Ga.answer(Ga.ETurnEnd{False{}, Some{"worker\ncrashed"}}), Ga.answer(Ga.EAssistant{Ga.SError{}, [], Some{"No API key for provider: cloudflare-ai-gateway"}}), Ga.answer(Ga.ETurnEnd{True{}, None{}}), Ga.answer(Ga.EAssistant{Ga.SStop{}, ["a", " b  c "], None{}}), Ga.answer(Ga.EAssistant{Ga.SLength{}, [" ", "\n"], None{}}), Ga.answer(Ga.EAssistant{Ga.SError{}, [], Some{" \t"}}), Ga.answer(Ga.EAssistant{Ga.SAborted{}, ["x"], None{}}), Ga.answer(Ga.EAssistant{Ga.SToolUse{}, ["x"], None{}}), Ga.answer(Ga.ETurnEnd{False{}, None{}}), Ga.answer(Ga.EOther{})] == [Ga.AFailed{"the turn ended before the model answered. Send /status to see the model"}, Ga.ANone{}, Ga.AFailed{"worker crashed"}, Ga.AFailed{"No API key for provider: cloudflare-ai-gateway"}, Ga.ANone{}, Ga.AText{"a\n\n b  c "}, Ga.ANone{}, Ga.AFailed{"the model request failed"}, Ga.AStopped{}, Ga.ANone{}, Ga.ANone{}, Ga.ANone{}] : List<&2, Ga.Answer>}

# Laws: the entry (R6)
# --------------------

# LAW gateway_answer_entry_answers (R6): the entry answers every request
# Rust spells, every length within the wire, with the spelled answer of
# the spec
# EXCLUDES: a field misread, swapped or dropped; a stop tag read as
#   another; a default
law gateway_answer_entry_answers:
  for +ev: Ga.Ev
  for h: {ga_fit(ev) == True{} : Bool}
  {FGa.ffi(ga_w_req(ev, "")) == ga_w_reply(ga_answer(ev)) : String}

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
