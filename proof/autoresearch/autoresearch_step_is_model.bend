# eukhe: the proof of LAW autoresearch_step_is_model

import Base
import ../../bend/ffi_autoresearch.bend as FAr
import ../../bend/autoresearch/state.bend as ArS
import ../../laws/autoresearch/entry.bend as AutoresearchEntry
import ./base/entry.bend as LAE
import ./autoresearch_entry_answers.bend as PAnswers

def ae.join(+x: String, +xs: List<&2, String>, +ys: List<&2, String>, -f1: FAr.St, -f2: FAr.St, ih: {xs == ys : List<&2, String>} & {f1 == f2 : FAr.St}) -> {x <> xs == x <> ys : List<&2, String>} & {f1 == f2 : FAr.St}:
  (i1, i2) = ih
  (Equal.cong(List<&2, String>, List<&2, String>, k => x <> k, xs, ys, i1), i2)

# from any live state, the stepper answers qs as the model does and ends
# where the model's steps fold to
def ae.model(qs: List<&2, FAr.Q>, +s: ArS.St, fits: {AutoresearchEntry.ar_all_fit(qs) == True{} : Bool}) -> {AutoresearchEntry.ar_replies(qs, FAr.Live{s}) == AutoresearchEntry.ar_spec(qs, s) : List<&2, String>} & {AutoresearchEntry.ar_feed(qs, FAr.Live{s}) == FAr.Live{AutoresearchEntry.ar_fold(qs, s)} : FAr.St}:
  match qs:
    case Nil{}:
      ({==}, {==})
    case +q <> +rest:
      +f = fits
      +a = AutoresearchEntry.autoresearch_entry_answers(s, q, LAE.ae.l(AutoresearchEntry.ar_fits(q), AutoresearchEntry.ar_all_fit(rest), f))
      %Equal.sym(FAr.St & String, FAr.step(FAr.Live{s}, AutoresearchEntry.ar_w_req(q)), (FAr.Live{AutoresearchEntry.ar_next(s, q)}, AutoresearchEntry.ar_reply(s, q)), a) : {AutoresearchEntry.ar_reply_of(_) <> AutoresearchEntry.ar_replies(rest, AutoresearchEntry.ar_state(_)) == AutoresearchEntry.ar_reply(s, q) <> AutoresearchEntry.ar_spec(rest, AutoresearchEntry.ar_next(s, q)) : List<&2, String>} & {AutoresearchEntry.ar_feed(rest, AutoresearchEntry.ar_state(_)) == FAr.Live{AutoresearchEntry.ar_fold(rest, AutoresearchEntry.ar_next(s, q))} : FAr.St}
      ae.join(AutoresearchEntry.ar_reply(s, q), AutoresearchEntry.ar_replies(rest, FAr.Live{AutoresearchEntry.ar_next(s, q)}), AutoresearchEntry.ar_spec(rest, AutoresearchEntry.ar_next(s, q)), AutoresearchEntry.ar_feed(rest, FAr.Live{AutoresearchEntry.ar_next(s, q)}), FAr.Live{AutoresearchEntry.ar_fold(rest, AutoresearchEntry.ar_next(s, q))}, ae.model(rest, AutoresearchEntry.ar_next(s, q), LAE.ae.r(AutoresearchEntry.ar_fits(q), AutoresearchEntry.ar_all_fit(rest), f)))

def AutoresearchEntry.autoresearch_step_is_model(qs, fits):
  ae.model(qs, ArS.St.empty(), fits)
