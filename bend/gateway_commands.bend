# gateway_commands: what one phone text message means to the Signal
# gateway (Rust: crates/eukhe-gateway commands.rs, called by gateway.rs for
# every text message without images): a phone command, an answer the
# gateway sends back itself, or a prompt for the agent.
#
# - The first word (Rust `split_whitespace`) must be `/` and a name of
#   ASCII letters, digits, `-` or `_` (empty allowed); else a prompt.
# - The name is read lowercased (ASCII). A session command name (the list
#   Rust sends) is a prompt: the session runs it.
# - A command name with exactly its arguments (`/use` one, the others
#   none) is that command; with other arguments, its usage line.
# - Another name alone answers suggestions: a lone `/` the command list,
#   the commands the name starts, else the closest command, else the
#   command list; another name with more words is a prompt.
# Pure: no IO, no @unsafe.

import Base
import ./gateway_answer.bend as Ga
import ./slash_suggest.bend as Ss

# A phone command, in Rust's PhoneCommand order
type Cmd is Data:
  CHelp{}
  CSessions{}
  # `/use N`, with N as written
  CUse{arg: String}
  CLatest{}
  CNew{}
  CStop{}
  CStatus{}
  CMemory{}

# What one text message means
type Out is Data:
  OCommand{cmd: Cmd}
  # the gateway answers this text; the agent never sees the message
  OAnswer{text: String}
  OPrompt{}

# A command's name, its usage and what it does
type Spec is Data:
  Spec{name: String, usage: String, about: String}

# The commands, in PhoneCommand order
def specs() -> List<&2, Spec>:
  [Spec{"help", "/help", "Show the commands."}, Spec{"sessions", "/sessions", "Show the newest sessions."}, Spec{"use", "/use N", "Send messages to session N."}, Spec{"latest", "/latest", "Send messages to the newest session."}, Spec{"new", "/new", "Start a new session."}, Spec{"stop", "/stop", "Stop the current turn."}, Spec{"status", "/status", "Show the session state."}, Spec{"memory", "/memory", "Show the chat memory state."}]

# Text
# ----

# `<usage> - <description>`
def line(s: Spec) -> String:
  match s:
    case Spec{n, u, d}:
      String.append(u, String.append(" - ", d))

# the lines of ss, then the texts of tail
def lines(ss: List<&2, Spec>, tail: List<&2, String>) -> List<&2, String>:
  match ss:
    case Nil{}:
      tail
    case s <> rest:
      line(s) <> lines(rest, tail)

def names(ss: List<&2, Spec>) -> List<&2, String>:
  match ss:
    case Nil{}:
      Nil{}
    case s <> rest:
      match s:
        case Spec{n, u, d}:
          n <> names(rest)

# the text at index i of xs ("" past its end: never asked)
def pick(xs: List<&2, String>, i: Nat) -> String:
  match xs:
    case Nil{}:
      ""
    case x <> rest:
      match i:
        case 0n:
          x
        case 1n+p:
          pick(rest, p)

# The `/help` text
def help() -> String:
  Ga.join("\n", "Commands:" <> lines(specs(), ["Other text goes to the agent."]))

# Suggestions
# -----------

def starting.at(b: Bool, l: String, rest: List<&2, String>) -> List<&2, String>:
  match b:
    case True{}:
      l <> rest
    case False{}:
      rest

# the lines of the commands whose name starts with n
def starting(+n: String, ss: List<&2, Spec>) -> List<&2, String>:
  match ss:
    case Nil{}:
      Nil{}
    case s <> rest:
      match s:
        case Spec{+m, u, d}:
          starting.at(String.starts_with(m, n), line(Spec{m, u, d}), starting(n, rest))

def suggest.far(+n: String, m: Maybe<&2, Nat>) -> String:
  match m:
    case None{}:
      String.append("No command /", String.append(n, String.append(". Not sent to the agent.\n", help())))
    case Some{j}:
      String.append("No command /", String.append(n, String.append(". Did you mean /", String.append(pick(names(specs()), j), "?\nNot sent to the agent. Send / for all commands."))))

def suggest.near(+n: String, ls: List<&2, String>) -> String:
  match ls:
    case Nil{}:
      suggest.far(n, Ss.suggest(n, names(specs())))
    case l <> rest:
      Ga.join("\n", l <> List.append(&2, String, rest, ["Send one of these. Send / for all commands."]))

# the answer to `/<n>` alone when n names no command
def suggest(n: String) -> String:
  match n:
    case SNil{}:
      help()
    case SCon{+c, +t}:
      suggest.near(SCon{c, t}, starting(SCon{c, t}, specs()))

# Parse
# -----

def none(args: List<&2, String>, c: Cmd) -> Maybe<&2, Cmd>:
  match args:
    case Nil{}:
      Some{c}
    case a <> rest:
      None{}

def one(args: List<&2, String>) -> Maybe<&2, Cmd>:
  match args:
    case Nil{}:
      None{}
    case a <> rest:
      match rest:
        case Nil{}:
          Some{CUse{a}}
        case b <> more:
          None{}

# the command at index i of specs() given args, when they are its own
def command(i: Nat, args: List<&2, String>) -> Maybe<&2, Cmd>:
  match i:
    case 0n:
      none(args, CHelp{})
    case 1n:
      none(args, CSessions{})
    case 2n:
      one(args)
    case 3n:
      none(args, CLatest{})
    case 4n:
      none(args, CNew{})
    case 5n:
      none(args, CStop{})
    case 6n:
      none(args, CStatus{})
    case 7n:
      none(args, CMemory{})
    case 8n+u:
      None{}

def find.at(b: Bool, i: Nat, later: Maybe<&2, Nat>) -> Maybe<&2, Nat>:
  match b:
    case True{}:
      Some{i}
    case False{}:
      later

# the index of n in ns, counted from i
def find(+n: String, ns: List<&2, String>, +i: Nat) -> Maybe<&2, Nat>:
  match ns:
    case Nil{}:
      None{}
    case m <> rest:
      find.at(String.eq(n, m), i, find(n, rest, 1n+i))

def exact(m: Maybe<&2, Cmd>, i: Nat) -> Out:
  match m:
    case None{}:
      OAnswer{String.append("Usage: ", pick(lines(specs(), []), i))}
    case Some{c}:
      OCommand{c}

def unknown(+n: String, args: List<&2, String>) -> Out:
  match args:
    case Nil{}:
      OAnswer{suggest(n)}
    case a <> rest:
      OPrompt{}

def known(+n: String, args: List<&2, String>, m: Maybe<&2, Nat>) -> Out:
  match m:
    case None{}:
      unknown(n, args)
    case Some{+i}:
      exact(command(i, args), i)

def member(+n: String, xs: List<&2, String>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case x <> rest:
      Bool.or(String.eq(n, x), member(n, rest))

def session(b: Bool, +n: String, args: List<&2, String>) -> Out:
  match b:
    case True{}:
      OPrompt{}
    case False{}:
      known(n, args, find(n, names(specs()), 0n))

# c may be in a command name
def name_char(+c: Char) -> Bool:
  Bool.or(Char.is_digit(c), Bool.or(Char.is_alpha(c), Bool.or(Char.is_eq(c, '-'), Char.is_eq(c, '_'))))

def shaped(s: String) -> Bool:
  match s:
    case SNil{}:
      True{}
    case SCon{c, t}:
      Bool.and(name_char(c), shaped(t))

def lower(+n: String, args: List<&2, String>, sess: List<&2, String>) -> Out:
  session(member(n, sess), n, args)

def named(b: Bool, +name: String, args: List<&2, String>, sess: List<&2, String>) -> Out:
  match b:
    case True{}:
      lower(String.to_lower(name), args, sess)
    case False{}:
      OPrompt{}

def slash(b: Bool, +name: String, args: List<&2, String>, sess: List<&2, String>) -> Out:
  match b:
    case True{}:
      named(shaped(name), name, args, sess)
    case False{}:
      OPrompt{}

def first(w: String, args: List<&2, String>, sess: List<&2, String>) -> Out:
  match w:
    case SNil{}:
      OPrompt{}
    case SCon{c, +name}:
      slash(Char.is_eq(c, '/'), name, args, sess)

def parse.words(ws: List<&2, String>, sess: List<&2, String>) -> Out:
  match ws:
    case Nil{}:
      OPrompt{}
    case w <> args:
      first(w, args, sess)

# what the text means, given the session command names
def parse(text: String, sess: List<&2, String>) -> Out:
  parse.words(Ga.words(text), sess)
