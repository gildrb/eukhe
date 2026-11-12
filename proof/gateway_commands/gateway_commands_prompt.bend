# eukhe: the proof of LAW gateway_commands_prompt
#
# PROOF: the code's words of the text are its words (gab.spelled); with no words, a first word that is not `/` (code: slash), or a name the code's name test refuses (gcb.shaped), the code answers a prompt.

import Base
import ../../bend/gateway_commands.bend as Gc
import ../../bend/gateway_answer.bend as Ga
import ../../bend/slash_suggest.bend as Ss
import ../../laws/gateway_answer.bend as GatewayAnswer
import ../../laws/gateway_commands.bend as GatewayCommands
import ../gateway_answer/base.bend as LGa
import ./base.bend as LA

def gcp.slash(b: Bool, +n: String, args: List<&2, String>, sess: List<&2, String>, h: {Bool.and(b, GatewayCommands.gc_name(n)) == False{} : Bool}) -> {Gc.slash(b, n, args, sess) == Gc.OPrompt{} : Gc.Out}:
  match b:
    case False{}:
      {==}
    case True{}:
      +hs = Equal.trans(Bool, Gc.shaped(n), GatewayCommands.gc_name(n), False{}, LA.gcb.shaped(n), h)
      %Equal.sym(Bool, Gc.shaped(n), False{}, hs) : {Gc.named(_, n, args, sess) == Gc.OPrompt{} : Gc.Out}
      {==}

def gcp.first(w: String, args: List<&2, String>, sess: List<&2, String>, h: {GatewayCommands.gc_slash(w) == False{} : Bool}) -> {Gc.first(w, args, sess) == Gc.OPrompt{} : Gc.Out}:
  match w:
    case SNil{}:
      {==}
    case SCon{+c, +n}:
      gcp.slash(Char.is_eq(c, '/'), n, args, sess, h)

def gcp.words(ws: List<&2, String>, sess: List<&2, String>, h: {GatewayCommands.gc_slash_first(ws) == False{} : Bool}) -> {Gc.parse.words(ws, sess) == Gc.OPrompt{} : Gc.Out}:
  match ws:
    case Nil{}:
      {==}
    case w <> args:
      gcp.first(w, args, sess, h)

def GatewayCommands.gateway_commands_prompt(t, sess, well, first):
  %Equal.sym(List<&2, String>, Ga.words(GatewayAnswer.ga_spell(t)), GatewayAnswer.ga_words_of(t), LGa.gab.spelled(t, True{}, well)) : {Gc.parse.words(_, sess) == Gc.OPrompt{} : Gc.Out}
  gcp.words(GatewayAnswer.ga_words_of(t), sess, first)
