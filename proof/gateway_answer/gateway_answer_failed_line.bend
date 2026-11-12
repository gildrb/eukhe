# eukhe: the proof of LAW gateway_answer_failed_line
#
# PROOF: a well formed text with a word is not blank for the code (gab.spell_full); its code words are its words (gab.spelled), joined as Base's join does (gab.join).

import Base
import ../../bend/gateway_answer.bend as Ga
import ../../laws/gateway_answer.bend as GatewayAnswer
import ./base.bend as LA

def GatewayAnswer.gateway_answer_failed_line(ts, t, well, some):
  +s = GatewayAnswer.ga_spell(t)
  +ws = GatewayAnswer.ga_words_of(t)
  %Equal.sym(Bool, Ga.blank(s), False{}, LA.gab.spell_full(t, True{}, well, some)) : {Ga.AFailed{Ga.reason.of(s, _)} == Ga.AFailed{String.join(ws, " ")} : Ga.Answer}
  %Equal.sym(List<&2, String>, Ga.words(s), ws, LA.gab.spelled(t, True{}, well)) : {Ga.AFailed{Ga.join(" ", _)} == Ga.AFailed{String.join(ws, " ")} : Ga.Answer}
  Equal.cong(String, Ga.Answer, z => Ga.AFailed{z}, Ga.join(" ", ws), String.join(ws, " "), LA.gab.join(" ", ws))
