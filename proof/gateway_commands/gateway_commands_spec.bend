# eukhe: the proof of LAW gateway_commands_spec
#
# PROOF: the code's words are the spec's (gab.words); then each stage of
# the parse is the spec's, case by case on the Bool or the list it
# matches: the name test (gcb.shaped), the session test (gcb.member), the
# index of the name (gcb.find), the command (gcb.command), the usage line
# (gcb.pick) and the answer to a name alone (gcb.suggest).

import Base
import ../../bend/gateway_commands.bend as Gc
import ../../bend/gateway_answer.bend as Ga
import ../../laws/gateway_answer.bend as GatewayAnswer
import ../../laws/gateway_commands.bend as GatewayCommands
import ../gateway_answer/base.bend as LGa
import ./base.bend as LA

def gcs.exact(m: Maybe<&2, Gc.Cmd>, +i: Nat) -> {Gc.exact(m, i) == GatewayCommands.gc_exact(m, i) : Gc.Out}:
  match m:
    case None{}:
      %LA.gcb.pick(Gc.lines(Gc.specs(), []), i) : {Gc.exact(None{}, i) == Gc.OAnswer{String.append("Usage: ", _)} : Gc.Out}
      {==}
    case Some{c}:
      {==}

def gcs.unknown(+n: String, args: List<&2, String>) -> {Gc.unknown(n, args) == GatewayCommands.gc_unknown(n, args) : Gc.Out}:
  match args:
    case Nil{}:
      %LA.gcb.suggest(n) : {Gc.OAnswer{Gc.suggest(n)} == Gc.OAnswer{_} : Gc.Out}
      {==}
    case a <> t:
      {==}

def gcs.known(+n: String, +args: List<&2, String>, m: Maybe<&2, Nat>) -> {Gc.known(n, args, m) == GatewayCommands.gc_found(n, args, m) : Gc.Out}:
  match m:
    case None{}:
      gcs.unknown(n, args)
    case Some{+i}:
      %LA.gcb.command(i, args) : {Gc.exact(Gc.command(i, args), i) == GatewayCommands.gc_exact(_, i) : Gc.Out}
      gcs.exact(Gc.command(i, args), i)

def gcs.session(b: Bool, +n: String, args: List<&2, String>) -> {Gc.session(b, n, args) == GatewayCommands.gc_decide(b, n, args) : Gc.Out}:
  match b:
    case True{}:
      {==}
    case False{}:
      %LA.gcb.find(n, Gc.names(Gc.specs()), 0n) : {Gc.known(n, args, Gc.find(n, Gc.names(Gc.specs()), 0n)) == GatewayCommands.gc_found(n, args, _) : Gc.Out}
      gcs.known(n, args, Gc.find(n, Gc.names(Gc.specs()), 0n))

def gcs.named(b: Bool, +name: String, args: List<&2, String>, +sess: List<&2, String>) -> {Gc.named(b, name, args, sess) == GatewayCommands.gc_word.at(b, name, args, sess) : Gc.Out}:
  match b:
    case True{}:
      +n = String.to_lower(name)
      %LA.gcb.member(n, sess) : {Gc.session(Gc.member(n, sess), n, args) == GatewayCommands.gc_decide(_, n, args) : Gc.Out}
      gcs.session(Gc.member(n, sess), n, args)
    case False{}:
      {==}

def gcs.slash(b: Bool, +name: String, args: List<&2, String>, sess: List<&2, String>) -> {Gc.slash(b, name, args, sess) == GatewayCommands.gc_word.at(Bool.and(b, GatewayCommands.gc_name(name)), name, args, sess) : Gc.Out}:
  match b:
    case True{}:
      %LA.gcb.shaped(name) : {Gc.named(Gc.shaped(name), name, args, sess) == GatewayCommands.gc_word.at(_, name, args, sess) : Gc.Out}
      gcs.named(Gc.shaped(name), name, args, sess)
    case False{}:
      {==}

def gcs.first(w: String, args: List<&2, String>, sess: List<&2, String>) -> {Gc.first(w, args, sess) == GatewayCommands.gc_word(w, args, sess) : Gc.Out}:
  match w:
    case SNil{}:
      {==}
    case SCon{+c, +name}:
      gcs.slash(Char.is_eq(c, '/'), name, args, sess)

def gcs.words(ws: List<&2, String>, sess: List<&2, String>) -> {Gc.parse.words(ws, sess) == GatewayCommands.gc_parse.at(ws, sess) : Gc.Out}:
  match ws:
    case Nil{}:
      {==}
    case w <> args:
      gcs.first(w, args, sess)

def GatewayCommands.gateway_commands_spec(text, sess):
  %LGa.gab.words(text) : {Gc.parse.words(Ga.words(text), sess) == GatewayCommands.gc_parse.at(_, sess) : Gc.Out}
  gcs.words(Ga.words(text), sess)
