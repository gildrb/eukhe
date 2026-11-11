# eukhe: lemmas shared by the proofs of area gateway_commands: the code's
# name test, session test, text at an index, starting commands, listing
# and help text are the laws' (by induction on the text or the list, the
# command table by computation); the route of a spelled text to the code's
# decision on its first word (the words by gab.spelled)

import Base
import ../../bend/gateway_commands.bend as Gc
import ../../bend/gateway_answer.bend as Ga
import ../../bend/slash_suggest.bend as Ss
import ../../laws/gateway_answer.bend as GatewayAnswer
import ../../laws/gateway_commands.bend as GatewayCommands
import ../gateway_answer/base.bend as LGa

# Logic
# -----

def gcb.or_l(a: Bool, -b: Bool, h: {Bool.or(a, b) == False{} : Bool}) -> {a == False{} : Bool}:
  match a:
    case True{}:
      h
    case False{}:
      {==}

def gcb.IfT(b: Bool, G: Type) -> Type:
  match b:
    case True{}:
      Unit
    case False{}:
      G

def gcb.or_r(a: Bool, -b: Bool, h: {Bool.or(a, b) == False{} : Bool}) -> {b == False{} : Bool}:
  match a:
    case True{}:
      %h : gcb.IfT(_, {b == False{} : Bool})
      Unit{}
    case False{}:
      h

def gcb.IfT.absurd(-G: Type, h: {True{} == False{} : Bool}) -> G:
  %h : gcb.IfT(_, G)
  Unit{}

# Names
# -----

def gcb.char(c: Char) -> {Gc.name_char(c) == GatewayCommands.gc_char(c) : Bool}:
  match c:
    case Chr{x}:
      {==}

# the code's name test is the spec's
def gcb.shaped(s: String) -> {Gc.shaped(s) == GatewayCommands.gc_name(s) : Bool}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      %gcb.char(c) : {Bool.and(Gc.name_char(c), Gc.shaped(t)) == Bool.and(_, GatewayCommands.gc_name(t)) : Bool}
      %gcb.shaped(t) : {Bool.and(Gc.name_char(c), Gc.shaped(t)) == Bool.and(Gc.name_char(c), _) : Bool}
      {==}

# the code's session test is the spec's
def gcb.member(+n: String, xs: List<&2, String>) -> {Gc.member(n, xs) == GatewayCommands.gc_in(n, xs) : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +t:
      %gcb.member(n, t) : {Bool.or(String.eq(n, x), Gc.member(n, t)) == Bool.or(String.eq(n, x), _) : Bool}
      {==}

# a name in no list is found nowhere in it
def gcb.find_none(+n: String, xs: List<&2, String>, +i: Nat, +h: {GatewayCommands.gc_in(n, xs) == False{} : Bool}) -> {Gc.find(n, xs, i) == None{} : Maybe<&2, Nat>}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +t:
      +he = gcb.or_l(String.eq(n, x), GatewayCommands.gc_in(n, t), h)
      %Equal.sym(Bool, String.eq(n, x), False{}, he) : {Gc.find.at(_, i, Gc.find(n, t, 1n+i)) == None{} : Maybe<&2, Nat>}
      gcb.find_none(n, t, 1n+i, gcb.or_r(String.eq(n, x), GatewayCommands.gc_in(n, t), h))

# Texts
# -----

# the code's text at an index is the spec's
def gcb.pick(xs: List<&2, String>, i: Nat) -> {Gc.pick(xs, i) == GatewayCommands.gc_at(xs, i) : String}:
  match xs:
    case Nil{}:
      {==}
    case x <> t:
      match i:
        case 0n:
          {==}
        case 1n+p:
          gcb.pick(t, p)

def gcb.keep(b: Bool, l: String, rest: List<&2, String>) -> {Gc.starting.at(b, l, rest) == GatewayCommands.gc_keep(b, l, rest) : List<&2, String>}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# the code's starting commands are the spec's, over the table's names and
# lines
def gcb.starting(+n: String, ss: List<&2, Gc.Spec>) -> {Gc.starting(n, ss) == GatewayCommands.gc_starting(n, Gc.names(ss), Gc.lines(ss, [])) : List<&2, String>}:
  match ss:
    case Nil{}:
      {==}
    case s <> +rest:
      match s:
        case Gc.Spec{+m, +u, +d}:
          %gcb.starting(n, rest) : {Gc.starting.at(String.starts_with(m, n), Gc.line(Gc.Spec{m, u, d}), Gc.starting(n, rest)) == GatewayCommands.gc_keep(String.starts_with(m, n), Gc.line(Gc.Spec{m, u, d}), _) : List<&2, String>}
          gcb.keep(String.starts_with(m, n), Gc.line(Gc.Spec{m, u, d}), Gc.starting(n, rest))

# the joined listing after its first line is the spec's
def gcb.listing(ls: List<&2, String>) -> {Ga.join.rest("\n", List.append(&2, String, ls, ["Send one of these. Send / for all commands."])) == String.append("\n", GatewayCommands.gc_listing(ls)) : String}:
  match ls:
    case Nil{}:
      {==}
    case +x <> +t:
      %gcb.listing(t) : {String.append("\n", String.append(x, Ga.join.rest("\n", List.append(&2, String, t, ["Send one of these. Send / for all commands."])))) == String.append("\n", String.append(x, _)) : String}
      {==}

# the code's help text is the spec's
def gcb.help() -> {Gc.help() == GatewayCommands.gc_help() : String}:
  {==}

# Route
# -----

# a well formed text whose words are `/`, a name of command chars and args
# goes to the code's session test on the lowercased name
def gcb.route(+t: GatewayAnswer.GaText, +sess: List<&2, String>, +name: String, +args: List<&2, String>, +well: {GatewayAnswer.ga_well(t, True{}) == True{} : Bool}, ws: {GatewayAnswer.ga_words_of(t) == SCon{'/', name} <> args : List<&2, String>}, nm: {GatewayCommands.gc_name(name) == True{} : Bool}) -> {Gc.parse(GatewayAnswer.ga_spell(t), sess) == Gc.session(Gc.member(String.to_lower(name), sess), String.to_lower(name), args) : Gc.Out}:
  +L = String.to_lower(name)
  +R = Gc.session(Gc.member(L, sess), L, args)
  %Equal.sym(List<&2, String>, Ga.words(GatewayAnswer.ga_spell(t)), GatewayAnswer.ga_words_of(t), LGa.gab.spelled(t, True{}, well)) : {Gc.parse.words(_, sess) == R : Gc.Out}
  %Equal.sym(List<&2, String>, GatewayAnswer.ga_words_of(t), SCon{'/', name} <> args, ws) : {Gc.parse.words(_, sess) == R : Gc.Out}
  +hs = Equal.trans(Bool, Gc.shaped(name), GatewayCommands.gc_name(name), True{}, gcb.shaped(name), nm)
  %Equal.sym(Bool, Gc.shaped(name), True{}, hs) : {Gc.named(_, name, args, sess) == R : Gc.Out}
  {==}

# the same name, no session command: the code's command lookup
def gcb.known(+t: GatewayAnswer.GaText, +sess: List<&2, String>, +name: String, +args: List<&2, String>, +well: {GatewayAnswer.ga_well(t, True{}) == True{} : Bool}, ws: {GatewayAnswer.ga_words_of(t) == SCon{'/', name} <> args : List<&2, String>}, nm: {GatewayCommands.gc_name(name) == True{} : Bool}, own: {GatewayCommands.gc_in(String.to_lower(name), sess) == False{} : Bool}) -> {Gc.parse(GatewayAnswer.ga_spell(t), sess) == Gc.known(String.to_lower(name), args, Gc.find(String.to_lower(name), Gc.names(Gc.specs()), 0n)) : Gc.Out}:
  +L = String.to_lower(name)
  +hm = Equal.trans(Bool, Gc.member(L, sess), GatewayCommands.gc_in(L, sess), False{}, gcb.member(L, sess), own)
  %hm : {Gc.parse(GatewayAnswer.ga_spell(t), sess) == Gc.session(_, L, args) : Gc.Out}
  gcb.route(t, sess, name, args, well, ws, nm)

# the same name, no command either: the code's answer to an unknown name
def gcb.unknown(+t: GatewayAnswer.GaText, +sess: List<&2, String>, +name: String, +args: List<&2, String>, +well: {GatewayAnswer.ga_well(t, True{}) == True{} : Bool}, ws: {GatewayAnswer.ga_words_of(t) == SCon{'/', name} <> args : List<&2, String>}, nm: {GatewayCommands.gc_name(name) == True{} : Bool}, own: {GatewayCommands.gc_in(String.to_lower(name), sess) == False{} : Bool}, none: {GatewayCommands.gc_in(String.to_lower(name), GatewayCommands.gc_names()) == False{} : Bool}) -> {Gc.parse(GatewayAnswer.ga_spell(t), sess) == Gc.unknown(String.to_lower(name), args) : Gc.Out}:
  +L = String.to_lower(name)
  +hf = gcb.find_none(L, Gc.names(Gc.specs()), 0n, none)
  %hf : {Gc.parse(GatewayAnswer.ga_spell(t), sess) == Gc.known(L, args, _) : Gc.Out}
  gcb.known(t, sess, name, args, well, ws, nm, own)
