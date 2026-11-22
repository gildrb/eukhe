# eukhe: the laws of area gateway_report

import Base
import ../bend/gateway_answer.bend as Ga
import ../bend/gateway_report.bend as Gr
import ../bend/ffi_gateway_report.bend as FGr
import ../bend/wire.bend as Wr
import ./base.bend as LawsBase
import ./gateway_answer.bend as GatewayAnswer

# (D1) What the Signal peer hears of a run
# ----------------------------------------
# bend/gateway_report.bend, run as the compiled core by
# bend/ffi_gateway_report.bend (crates/eukhe-gateway report.rs, called by
# gateway.rs for every event of the bound session with the answer
# gateway_answer names). The phone hears one report when a run ends and
# nothing while it runs. Every input is free: anything held, any answer,
# any end.
#
# R1: a stop goes at once, at every event; nothing is held after it.
# R2: an event that ends no run sends nothing; a text or a failure becomes
#     what the gateway holds, nothing keeps what it held.
# R3: a run end while work the run started still runs sends nothing and
#     holds the run's last answer: the end's own answer when it is a text
#     or a failure, else what was held.
# R4: a run end with nothing running holds nothing and sends the run's
#     last answer as the report; a run whose last answer is nothing
#     reports nothing.
# R5: the report carries what the run last found left of its task: a
#     text gets "\n\nLeft: " and the words of the left text joined by
#     single spaces (Rust `split_whitespace`); a failure gets "\nLeft: "
#     and the same words. A missing, empty or whitespace-only left text
#     adds nothing.
# R6: the entry answers each request Rust writes (every length within the
#     wire) with the step of R1-R5, reads exactly the request and nothing
#     after it, and answers any other input with the exact error form
#     `E gateway_report: malformed request`.

# Spec helpers
# ------------

# R2, R3: an answer the gateway keeps: a text or a failure
def gr_kept(a: Ga.Answer) -> Bool:
  match a:
    case Ga.ANone{}:
      False{}
    case Ga.AText{t}:
      True{}
    case Ga.AFailed{t}:
      True{}
    case Ga.AStopped{}:
      False{}

# R3, R4: an answer that is no stop
def gr_no_stop(a: Ga.Answer) -> Bool:
  match a:
    case Ga.ANone{}:
      True{}
    case Ga.AText{t}:
      True{}
    case Ga.AFailed{t}:
      True{}
    case Ga.AStopped{}:
      False{}

# R3, R4: the run's last answer, after the gateway held h and the end
# answered a (no stop)
def gr_last(h: Ga.Answer, a: Ga.Answer) -> Ga.Answer:
  match a:
    case Ga.ANone{}:
      h
    case Ga.AText{t}:
      Ga.AText{t}
    case Ga.AFailed{t}:
      Ga.AFailed{t}
    case Ga.AStopped{}:
      Ga.AStopped{}

# R6: the spelling of a request and of its reply

def gr_w_answer(a: Ga.Answer, rest: String) -> String:
  match a:
    case Ga.ANone{}:
      Wr.put_nat(0n, rest)
    case Ga.AText{t}:
      Wr.put_nat(1n, Wr.put_str(t, rest))
    case Ga.AFailed{t}:
      Wr.put_nat(2n, Wr.put_str(t, rest))
    case Ga.AStopped{}:
      Wr.put_nat(3n, rest)

def gr_w_end(e: Gr.End, rest: String) -> String:
  match e:
    case Gr.ENone{}:
      Wr.put_nat(0n, rest)
    case Gr.ERun{w, l}:
      Wr.put_nat(1n, Wr.put_bool(w, GatewayAnswer.ga_w_maybe(l, rest)))

def gr_w_req(q: FGr.Req, rest: String) -> String:
  match q:
    case FGr.Req{h, a, e}:
      gr_w_answer(h, gr_w_answer(a, gr_w_end(e, rest)))

def gr_w_reply(o: Gr.Out) -> String:
  match o:
    case Gr.Out{h, s}:
      gr_w_answer(h, gr_w_answer(s, ""))

def gr_fit_answer(a: Ga.Answer) -> Bool:
  match a:
    case Ga.ANone{}:
      True{}
    case Ga.AText{t}:
      LawsBase.wire_fits(String.length(t))
    case Ga.AFailed{t}:
      LawsBase.wire_fits(String.length(t))
    case Ga.AStopped{}:
      True{}

def gr_fit_end(e: Gr.End) -> Bool:
  match e:
    case Gr.ENone{}:
      True{}
    case Gr.ERun{w, l}:
      GatewayAnswer.ga_fit_maybe(l)

# every length of the request fits the wire
def gr_fit(q: FGr.Req) -> Bool:
  match q:
    case FGr.Req{h, a, e}:
      Bool.and(gr_fit_answer(h), Bool.and(gr_fit_answer(a), gr_fit_end(e)))

# R6: the step of a request
def gr_step(q: FGr.Req) -> Gr.Out:
  match q:
    case FGr.Req{h, a, e}:
      Gr.step(h, a, e)

# Laws: the steps
# ---------------

# LAW gateway_report_stop (R1): a stop, with anything held and at every
# end (none, a run end with or without work running, any left text), is
# sent at once, and nothing is held after it
# EXCLUDES: a stop held until the run ends, a stop that keeps an older
#   text for a later report
law gateway_report_stop:
  for h: Ga.Answer
  for e: Gr.End
  {Gr.step(h, Ga.AStopped{}, e) == Gr.Out{Ga.ANone{}, Ga.AStopped{}} : Gr.Out}

# LAW gateway_report_holds (R2): an event that ends no run and answers a
# text or a failure a, with anything held, sends nothing and holds a
# EXCLUDES: a mid-run text or failure sent to the phone, an older answer
#   kept over a newer one
law gateway_report_holds:
  for h: Ga.Answer
  for +a: Ga.Answer
  for k: {gr_kept(a) == True{} : Bool}
  {Gr.step(h, a, Gr.ENone{}) == Gr.Out{a, Ga.ANone{}} : Gr.Out}

# LAW gateway_report_keeps (R2): an event that ends no run and answers
# nothing keeps what the gateway held, and sends nothing
# EXCLUDES: a held answer dropped by a quiet event, a held answer sent
#   before the run ends
law gateway_report_keeps:
  for +h: Ga.Answer
  {Gr.step(h, Ga.ANone{}, Gr.ENone{}) == Gr.Out{h, Ga.ANone{}} : Gr.Out}

# LAW gateway_report_waits (R3): a run end while work still runs, with
# anything held, an end answer a that is a text, a failure or nothing, and
# any left text, sends nothing and holds the run's last answer (a when it
# is a text or a failure, else what was held)
# EXCLUDES: a report (or "waiting on ...") sent while work the run started
#   still runs, the run's answer lost while it waits
law gateway_report_waits:
  for +h: Ga.Answer
  for +a: Ga.Answer
  for l: Maybe<&2, String>
  for ns: {gr_no_stop(a) == True{} : Bool}
  {Gr.step(h, a, Gr.ERun{True{}, l}) == Gr.Out{gr_last(h, a), Ga.ANone{}} : Gr.Out}

# LAW gateway_report_reports (R4, R5): a run end with nothing running,
# anything held, an end answer a that is a text, a failure or nothing, and
# a missing or blank left text, holds nothing and sends the run's last
# answer as it is
# EXCLUDES: a run end that keeps its report, a report of an older answer
#   than the run's last, a report that adds an empty "Left:" line
law gateway_report_reports:
  for +h: Ga.Answer
  for +a: Ga.Answer
  for +l: Maybe<&2, String>
  for ns: {gr_no_stop(a) == True{} : Bool}
  for none: {GatewayAnswer.ga_no_reason(l) == True{} : Bool}
  {Gr.step(h, a, Gr.ERun{False{}, l}) == Gr.Out{Ga.ANone{}, gr_last(h, a)} : Gr.Out}

# LAW gateway_report_text_left (R4, R5): a run end with nothing running
# whose last answer is the text t, with a left text that has a word (g:
# its whitespace runs and words, well formed), sends t, "\n\nLeft: " and
# the words of g joined by single spaces, and holds nothing
# EXCLUDES: what is left dropped, kept on several lines or with its
#   spacing, put before the text or without its label
law gateway_report_text_left:
  for +h: Ga.Answer
  for +a: Ga.Answer
  for +t: String
  for +g: GatewayAnswer.GaText
  for last: {gr_last(h, a) == Ga.AText{t} : Ga.Answer}
  for well: {GatewayAnswer.ga_well(g, True{}) == True{} : Bool}
  for some: {GatewayAnswer.ga_has_word(g) == True{} : Bool}
  {Gr.step(h, a, Gr.ERun{False{}, Some{GatewayAnswer.ga_spell(g)}}) == Gr.Out{Ga.ANone{}, Ga.AText{String.append(t, String.append("\n\nLeft: ", String.join(GatewayAnswer.ga_words_of(g), " ")))}} : Gr.Out}

# LAW gateway_report_failed_left (R4, R5): a run end with nothing running
# whose last answer is the failure r, with a left text that has a word,
# sends r, "\nLeft: " and the words of the left text joined by single
# spaces, and holds nothing
# EXCLUDES: what is left dropped from a failure, a failure that loses its
#   reason to what is left
law gateway_report_failed_left:
  for +h: Ga.Answer
  for +a: Ga.Answer
  for +r: String
  for +g: GatewayAnswer.GaText
  for last: {gr_last(h, a) == Ga.AFailed{r} : Ga.Answer}
  for well: {GatewayAnswer.ga_well(g, True{}) == True{} : Bool}
  for some: {GatewayAnswer.ga_has_word(g) == True{} : Bool}
  {Gr.step(h, a, Gr.ERun{False{}, Some{GatewayAnswer.ga_spell(g)}}) == Gr.Out{Ga.ANone{}, Ga.AFailed{String.append(r, String.append("\nLeft: ", String.join(GatewayAnswer.ga_words_of(g), " ")))}} : Gr.Out}

# LAW gateway_report_silent (R4): a run end with nothing running whose
# last answer is nothing (or a held stop), with every left text, sends
# nothing (the stop: the stop alone) and holds nothing
# EXCLUDES: a report of only what is left, a "Left:" line on a stop
law gateway_report_silent:
  for l: Maybe<&2, String>
  for l2: Maybe<&2, String>
  {[Gr.step(Ga.ANone{}, Ga.ANone{}, Gr.ERun{False{}, l}), Gr.step(Ga.AStopped{}, Ga.ANone{}, Gr.ERun{False{}, l2})] == [Gr.Out{Ga.ANone{}, Ga.ANone{}}, Gr.Out{Ga.ANone{}, Ga.AStopped{}}] : List<&2, Gr.Out>}

# LAW gateway_report_example (R1-R5): anchor: a run as the gateway sees it
# (a text held, a failure that replaces it, a quiet event, a run end while
# a job runs, the wake's text, the final run end with what is left), a
# stop, a blank left text and a whitespace-only one
# EXCLUDES: a code that drifts from these vectors
law gateway_report_example:
  {[Gr.step(Ga.ANone{}, Ga.AText{"Started the build."}, Gr.ENone{}), Gr.step(Ga.AText{"Started the build."}, Ga.AFailed{"overloaded"}, Gr.ENone{}), Gr.step(Ga.AFailed{"overloaded"}, Ga.ANone{}, Gr.ENone{}), Gr.step(Ga.AFailed{"overloaded"}, Ga.ANone{}, Gr.ERun{True{}, None{}}), Gr.step(Ga.AFailed{"overloaded"}, Ga.AText{"Built and pushed."}, Gr.ENone{}), Gr.step(Ga.AText{"Built and pushed."}, Ga.ANone{}, Gr.ERun{False{}, Some{" the\n release  notes "}}), Gr.step(Ga.AText{"x"}, Ga.AStopped{}, Gr.ERun{True{}, None{}}), Gr.step(Ga.AFailed{"down"}, Ga.ANone{}, Gr.ERun{False{}, Some{" \t"}}), Gr.step(Ga.AFailed{"down"}, Ga.ANone{}, Gr.ERun{False{}, Some{"docs"}})] == [Gr.Out{Ga.AText{"Started the build."}, Ga.ANone{}}, Gr.Out{Ga.AFailed{"overloaded"}, Ga.ANone{}}, Gr.Out{Ga.AFailed{"overloaded"}, Ga.ANone{}}, Gr.Out{Ga.AFailed{"overloaded"}, Ga.ANone{}}, Gr.Out{Ga.AText{"Built and pushed."}, Ga.ANone{}}, Gr.Out{Ga.ANone{}, Ga.AText{"Built and pushed.\n\nLeft: the release notes"}}, Gr.Out{Ga.ANone{}, Ga.AStopped{}}, Gr.Out{Ga.ANone{}, Ga.AFailed{"down"}}, Gr.Out{Ga.ANone{}, Ga.AFailed{"down\nLeft: docs"}}] : List<&2, Gr.Out>}

# Laws: the entry (R6)
# --------------------

# LAW gateway_report_entry_answers (R6): the entry answers every request
# Rust spells, every length within the wire, with the spelled step of the
# model Gr.step (pinned by the laws of R1-R5 above)
# EXCLUDES: a field misread, swapped or dropped; held and sent swapped in
#   the reply; a default
law gateway_report_entry_answers:
  for +q: FGr.Req
  for h: {gr_fit(q) == True{} : Bool}
  {FGr.ffi(gr_w_req(q, "")) == gr_w_reply(gr_step(q)) : String}

# LAW gateway_report_entry_reads (R6): the entry's decoder reads a spelled
# request back whole and leaves the input after it untouched
# EXCLUDES: a decoder that eats or skips input after the request
law gateway_report_entry_reads:
  for +q: FGr.Req
  for +rest: String
  for h: {gr_fit(q) == True{} : Bool}
  {FGr.get_req(gr_w_req(q, rest)) == Wr.Got{q, rest} : Wr.Dec<FGr.Req>}

# LAW gateway_report_entry_exact (R6): every input the entry does not
# answer with the error form is a spelled request that fits the wire
# EXCLUDES: an answer made on input that is no request (an unknown tag, a
#   malformed field, input left over)
law gateway_report_entry_exact:
  for +s: String
  for ok: {LawsBase.wire_opens_err(FGr.ffi(s)) == False{} : Bool}
  exs q: FGr.Req
  {s == gr_w_req(q, "") : String} & {gr_fit(q) == True{} : Bool}

# LAW gateway_report_entry_refuses (R6): every error the entry answers is
# exactly `E gateway_report: malformed request`
# EXCLUDES: an error text that varies with the input, a second error form
law gateway_report_entry_refuses:
  for +s: String
  for bad: {LawsBase.wire_opens_err(FGr.ffi(s)) == True{} : Bool}
  {FGr.ffi(s) == Wr.err("gateway_report: malformed request") : String}

# LAW gateway_report_entry_example (R6): anchor: the wire strings Rust
# sends and the replies it reads; an unknown answer tag, an unknown end
# tag and input left over
# EXCLUDES: tags in another order, a field order other than Rust's
law gateway_report_entry_example:
  {[FGr.ffi("0,1,2,hi0,"), FGr.ffi("1,2,hi0,1,T0,"), FGr.ffi("1,2,hi0,1,F1,4,todo"), FGr.ffi("2,4,down3,0,"), FGr.ffi("4,0,0,"), FGr.ffi("0,0,2,"), FGr.ffi("0,0,0,x")] == ["1,2,hi0,", "1,2,hi0,", "0,1,14,hi\n\nLeft: todo", "0,3,", Wr.err("gateway_report: malformed request"), Wr.err("gateway_report: malformed request"), Wr.err("gateway_report: malformed request")] : List<&2, String>}
