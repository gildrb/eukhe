# eukhe: lemmas shared by the proofs of area gateway_report: a missing or
# blank left text adds nothing to a report; a left text with a word adds
# its words on one line after the separator; a run end with nothing
# running sends the report of the run's last answer

import Base
import ../../bend/gateway_answer.bend as Ga
import ../../bend/gateway_report.bend as Gr
import ../../laws/gateway_answer.bend as GatewayAnswer
import ../../laws/gateway_report.bend as GatewayReport
import ../gateway_answer/base.bend as LA

# a text answer
def grb.is_text(a: Ga.Answer) -> Bool:
  match a:
    case Ga.ANone{}:
      False{}
    case Ga.AText{t}:
      True{}
    case Ga.AFailed{t}:
      False{}
    case Ga.AStopped{}:
      False{}

# a failure answer
def grb.is_failed(a: Ga.Answer) -> Bool:
  match a:
    case Ga.ANone{}:
      False{}
    case Ga.AText{t}:
      False{}
    case Ga.AFailed{t}:
      True{}
    case Ga.AStopped{}:
      False{}

# a missing or blank left text adds nothing
def grb.left_plain(+t: String, +sep: String, l: Maybe<&2, String>, none: {GatewayAnswer.ga_no_reason(l) == True{} : Bool}) -> {Gr.left(t, sep, l) == t : String}:
  match l:
    case None{}:
      {==}
    case Some{+s}:
      +hb = Equal.trans(Bool, Ga.blank(s), GatewayAnswer.ga_empty(s), True{}, LA.gab.blank(s), none)
      %Equal.sym(Bool, Ga.blank(s), True{}, hb) : {Gr.left.of(t, sep, s, _) == t : String}
      {==}

# a report with a missing or blank left text is the answer as it is
def grb.report_plain(k: Ga.Answer, +l: Maybe<&2, String>, +none: {GatewayAnswer.ga_no_reason(l) == True{} : Bool}) -> {Gr.report(k, l) == k : Ga.Answer}:
  match k:
    case Ga.ANone{}:
      {==}
    case Ga.AText{+t}:
      Equal.cong(String, Ga.Answer, z => Ga.AText{z}, Gr.left(t, "\n\n", l), t, grb.left_plain(t, "\n\n", l, none))
    case Ga.AFailed{+t}:
      Equal.cong(String, Ga.Answer, z => Ga.AFailed{z}, Gr.left(t, "\n", l), t, grb.left_plain(t, "\n", l, none))
    case Ga.AStopped{}:
      {==}

# a left text with a word: after sep, "Left: " and its words joined by
# single spaces
def grb.line(+t: String, +sep: String, +g: GatewayAnswer.GaText, +well: {GatewayAnswer.ga_well(g, True{}) == True{} : Bool}, some: {GatewayAnswer.ga_has_word(g) == True{} : Bool}) -> {Gr.left(t, sep, Some{GatewayAnswer.ga_spell(g)}) == String.append(t, String.append(sep, String.append("Left: ", String.join(GatewayAnswer.ga_words_of(g), " ")))) : String}:
  +s = GatewayAnswer.ga_spell(g)
  +ws = GatewayAnswer.ga_words_of(g)
  %Equal.sym(Bool, Ga.blank(s), False{}, LA.gab.spell_full(g, True{}, well, some)) : {Gr.left.of(t, sep, s, _) == String.append(t, String.append(sep, String.append("Left: ", String.join(ws, " ")))) : String}
  %Equal.sym(List<&2, String>, Ga.words(s), ws, LA.gab.spelled(g, True{}, well)) : {String.append(t, String.append(sep, String.append("Left: ", Ga.join(" ", _)))) == String.append(t, String.append(sep, String.append("Left: ", String.join(ws, " ")))) : String}
  Equal.cong(String, String, z => String.append(t, String.append(sep, String.append("Left: ", z))), Ga.join(" ", ws), String.join(ws, " "), LA.gab.join(" ", ws))

# a run end with nothing running, after an answer that is no stop, sends
# the report of the run's last answer and holds nothing
def grb.last_end(+h: Ga.Answer, +a: Ga.Answer, +l: Maybe<&2, String>, ns: {GatewayReport.gr_no_stop(a) == True{} : Bool}) -> {Gr.step(h, a, Gr.ERun{False{}, l}) == Gr.Out{Ga.ANone{}, Gr.report(GatewayReport.gr_last(h, a), l)} : Gr.Out}:
  match a:
    case Ga.ANone{}:
      {==}
    case Ga.AText{t}:
      {==}
    case Ga.AFailed{t}:
      {==}
    case Ga.AStopped{}:
      LA.gab.absurd({Gr.step(h, Ga.AStopped{}, Gr.ERun{False{}, l}) == Gr.Out{Ga.ANone{}, Gr.report(GatewayReport.gr_last(h, Ga.AStopped{}), l)} : Gr.Out}, ns)
