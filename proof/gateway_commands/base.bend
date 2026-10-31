# eukhe: lemmas shared by the proofs of area gateway_commands: each helper
# of bend/gateway_commands.bend answers what its spec helper of
# laws/gateway_commands.bend answers, on every input (by induction on the
# text or the list for the scans, case by case for the choices; the
# command table of the code is the spec's names and lines by computation)

import Base
import ../../bend/gateway_commands.bend as Gc
import ../../bend/gateway_answer.bend as Ga
import ../../bend/slash_suggest.bend as Ss
import ../../laws/gateway_commands.bend as GatewayCommands
import ../../laws/slash_suggest.bend as SlashSuggest
import ../slash_suggest/slash_suggest_spec.bend as PSlashSuggestSpec

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

def gcb.find_at(b: Bool, i: Nat, later: Maybe<&2, Nat>) -> {Gc.find.at(b, i, later) == GatewayCommands.gc_index.at(b, i, later) : Maybe<&2, Nat>}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# the code's index of a name is the spec's
def gcb.find(+n: String, xs: List<&2, String>, +i: Nat) -> {Gc.find(n, xs, i) == GatewayCommands.gc_index(n, xs, i) : Maybe<&2, Nat>}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +t:
      %gcb.find(n, t, 1n+i) : {Gc.find.at(String.eq(n, x), i, Gc.find(n, t, 1n+i)) == GatewayCommands.gc_index.at(String.eq(n, x), i, _) : Maybe<&2, Nat>}
      gcb.find_at(String.eq(n, x), i, Gc.find(n, t, 1n+i))

# Commands
# --------

def gcb.bare(i: Nat) -> {Gc.command(i, []) == GatewayCommands.gc_command(i, []) : Maybe<&2, Gc.Cmd>}:
  match i:
    case 0n:
      {==}
    case 1n:
      {==}
    case 2n:
      {==}
    case 3n:
      {==}
    case 4n:
      {==}
    case 5n:
      {==}
    case 6n:
      {==}
    case 7n:
      {==}
    case 8n:
      {==}
    case 9n:
      {==}
    case 10n+u:
      {==}

def gcb.one(i: Nat, +a: String) -> {Gc.command(i, [a]) == GatewayCommands.gc_command(i, [a]) : Maybe<&2, Gc.Cmd>}:
  match i:
    case 0n:
      {==}
    case 1n:
      {==}
    case 2n:
      {==}
    case 3n:
      {==}
    case 4n:
      {==}
    case 5n:
      {==}
    case 6n:
      {==}
    case 7n:
      {==}
    case 8n:
      {==}
    case 9n:
      {==}
    case 10n+u:
      {==}

def gcb.more(i: Nat, +a: String, +b: String, +u: List<&2, String>) -> {Gc.command(i, a <> b <> u) == GatewayCommands.gc_command(i, a <> b <> u) : Maybe<&2, Gc.Cmd>}:
  match i:
    case 0n:
      {==}
    case 1n:
      {==}
    case 2n:
      {==}
    case 3n:
      {==}
    case 4n:
      {==}
    case 5n:
      {==}
    case 6n:
      {==}
    case 7n:
      {==}
    case 8n:
      {==}
    case 9n:
      {==}
    case 10n+v:
      {==}

# the code's command of an index and arguments is the spec's
def gcb.command(+i: Nat, args: List<&2, String>) -> {Gc.command(i, args) == GatewayCommands.gc_command(i, args) : Maybe<&2, Gc.Cmd>}:
  match args:
    case Nil{}:
      gcb.bare(i)
    case a <> t:
      match t:
        case Nil{}:
          gcb.one(i, a)
        case b <> u:
          gcb.more(i, a, b, u)

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

def gcb.far(+n: String, m: Maybe<&2, Nat>) -> {Gc.suggest.far(n, m) == GatewayCommands.gc_far(n, m) : String}:
  match m:
    case None{}:
      {==}
    case Some{+j}:
      %gcb.pick(Gc.names(Gc.specs()), j) : {Gc.suggest.far(n, Some{j}) == String.append("No command /", String.append(n, String.append(". Did you mean /", String.append(_, "?\nNot sent to the agent. Send / for all commands.")))) : String}
      {==}

def gcb.near(+n: String, ls: List<&2, String>) -> {Gc.suggest.near(n, ls) == GatewayCommands.gc_listed(n, ls) : String}:
  match ls:
    case Nil{}:
      %SlashSuggest.slash_suggest_spec(n, Gc.names(Gc.specs())) : {Gc.suggest.far(n, Ss.suggest(n, Gc.names(Gc.specs()))) == GatewayCommands.gc_far(n, _) : String}
      gcb.far(n, Ss.suggest(n, Gc.names(Gc.specs())))
    case +l <> +t:
      %gcb.listing(t) : {String.append(l, Ga.join.rest("\n", List.append(&2, String, t, ["Send one of these. Send / for all commands."]))) == String.append(l, _) : String}
      {==}

# the code's answer to a name alone is the spec's
def gcb.suggest(n: String) -> {Gc.suggest(n) == GatewayCommands.gc_suggest(n) : String}:
  match n:
    case SNil{}:
      gcb.help()
    case SCon{+c, +t}:
      %gcb.starting(SCon{c, t}, Gc.specs()) : {Gc.suggest.near(SCon{c, t}, Gc.starting(SCon{c, t}, Gc.specs())) == GatewayCommands.gc_listed(SCon{c, t}, _) : String}
      gcb.near(SCon{c, t}, Gc.starting(SCon{c, t}, Gc.specs()))
