# eukhe: the laws of area gateway_commands

import Base
import ../bend/gateway_commands.bend as Gc
import ../bend/ffi_gateway_commands.bend as FGc
import ../bend/wire.bend as Wr
import ./base.bend as LawsBase
import ./gateway_answer.bend as GatewayAnswer
import ../bend/slash_suggest.bend as Ss
import ./doc_commit.bend as DocCommit

# (D1) What one phone text message means to the Signal gateway
# ------------------------------------------------------------
# bend/gateway_commands.bend, run as the compiled core by
# bend/ffi_gateway_commands.bend (crates/eukhe-gateway commands.rs, called
# by gateway.rs for every text message without images). Every input is
# free: any text, any list of session command names.
#
# R1: the words of the text are Rust's `split_whitespace` words (split at
#     the Unicode White_Space chars, none empty). The laws state it by
#     writing every text as its whitespace runs and words
#     (GatewayAnswer.GaText, well formed: GatewayAnswer.ga_well): every
#     string is the spelling of one such text.
# R2: no words, or a first word that is not `/` then a name of ASCII
#     letters, digits, `-` and `_` only (the empty name too), is a prompt.
# R3: the name is read with its ASCII letters lowercased; a name among the
#     session command names Rust sends is a prompt (the session runs it).
# R4: the commands, in order: help, sessions, use, latest, new, stop,
#     status, memory, model, reasoning. `/use` takes exactly one argument
#     (kept as written), `/reasoning` none or one (kept as written),
#     `/model` none, one, or the two `all` and N: one argument `all` is the
#     all-roles listing, another one argument a switch (kept as written),
#     `all` then N sets the all-roles model (N kept as written); the others
#     none; a command name with exactly its arguments is that command.
# R5: a command name with other arguments answers
#     `Usage: <usage> - <description>` (its line of gc_lines).
# R6: another name followed by more words is a prompt. Alone it answers:
#     for the empty name (a lone `/`), the help text; else, when command
#     names start with it, their lines in order, each on its own line,
#     then `Send one of these. Send / for all commands.`; else, when the
#     slash_suggest suggestion over the 10 names picks one,
#     `No command /<name>. Did you mean /<closest>?` and on a second line
#     `Not sent to the agent. Send / for all commands.`; else
#     `No command /<name>. Not sent to the agent.` and on the next lines
#     the help text.
# R7: the help text: `Commands:`, each command's line, then
#     `Other text goes to the agent.`, one per line.
# R8: the entry answers each request Rust writes (the text and the session
#     names, every length within the wire) with the meaning of R1-R7 (a
#     command by its tag, `/use` with its argument, `/model`, `/model all`
#     and `/reasoning` with their optional argument; an answer with its
#     text; a prompt), reads exactly the request and nothing after it, and
#     answers any other input with the exact error form
#     `E gateway_commands: malformed request`.


# Spec helpers
# ------------

# R4: the command names, in order
def gc_names() -> List<&2, String>:
  ["help", "sessions", "use", "latest", "new", "stop", "status", "memory", "model", "reasoning"]

# R5: the command lines, in the same order
def gc_lines() -> List<&2, String>:
  ["/help - Show the commands.", "/sessions - Show the newest sessions.", "/use N - Send messages to session N.", "/latest - Send messages to the newest session.", "/new - Start a new session.", "/stop - Stop the current turn.", "/status - Show the session state.", "/memory - Show the chat memory state.", "/model [all] [N] - Show the models; N switches to one; all N uses it for every role.", "/reasoning [level] - Show the thinking level; a level sets it."]

# R7
def gc_help() -> String:
  "Commands:\n/help - Show the commands.\n/sessions - Show the newest sessions.\n/use N - Send messages to session N.\n/latest - Send messages to the newest session.\n/new - Start a new session.\n/stop - Stop the current turn.\n/status - Show the session state.\n/memory - Show the chat memory state.\n/model [all] [N] - Show the models; N switches to one; all N uses it for every role.\n/reasoning [level] - Show the thinking level; a level sets it.\nOther text goes to the agent."

# the text at index i of xs; "" past the end
def gc_at(xs: List<&2, String>, i: Nat) -> String:
  match xs:
    case Nil{}:
      ""
    case x <> t:
      match i:
        case 0n:
          x
        case 1n+p:
          gc_at(t, p)

# R2: a char of a command name: ASCII digit, letter, '-' or '_'
def gc_char(c: Char) -> Bool:
  match c:
    case Chr{+x}:
      Bool.or(Bool.and(U32.is_ge(x, 48), U32.is_le(x, 57)), Bool.or(Bool.or(Bool.and(U32.is_ge(x, 65), U32.is_le(x, 90)), Bool.and(U32.is_ge(x, 97), U32.is_le(x, 122))), Bool.or(U32.is_eq(x, 45), U32.is_eq(x, 95))))

# R2: every char of s is one of a command name
def gc_name(s: String) -> Bool:
  match s:
    case SNil{}:
      True{}
    case SCon{c, t}:
      Bool.and(gc_char(c), gc_name(t))

# R3: n is one of xs
def gc_in(+n: String, xs: List<&2, String>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case x <> t:
      Bool.or(String.eq(n, x), gc_in(n, t))

def gc_keep(b: Bool, l: String, rest: List<&2, String>) -> List<&2, String>:
  match b:
    case True{}:
      l <> rest
    case False{}:
      rest

# R6: the lines ls of the names ns that start with n
def gc_starting(+n: String, ns: List<&2, String>, ls: List<&2, String>) -> List<&2, String>:
  match ns:
    case Nil{}:
      Nil{}
    case x <> t:
      match ls:
        case Nil{}:
          Nil{}
        case l <> u:
          gc_keep(String.starts_with(x, n), l, gc_starting(n, t, u))

# R6: each line, then the closing line, one per line
def gc_listing(ls: List<&2, String>) -> String:
  match ls:
    case Nil{}:
      "Send one of these. Send / for all commands."
    case l <> t:
      String.append(l, String.append("\n", gc_listing(t)))

# R2: w is `/` then a name of command chars
def gc_slash(w: String) -> Bool:
  match w:
    case SNil{}:
      False{}
    case SCon{c, n}:
      Bool.and(Char.is_eq(c, '/'), gc_name(n))

# R2: the first of the words ws is `/` then a name of command chars
def gc_slash_first(ws: List<&2, String>) -> Bool:
  match ws:
    case Nil{}:
      False{}
    case w <> rest:
      gc_slash(w)

# R4: the commands that take no argument, k = 0..6: their index in
# gc_names / gc_lines and the command
def gc_plain_has(k: Nat) -> Bool:
  match k:
    case 0n:
      True{}
    case 1n:
      True{}
    case 2n:
      True{}
    case 3n:
      True{}
    case 4n:
      True{}
    case 5n:
      True{}
    case 6n:
      True{}
    case 7n+u:
      False{}

def gc_plain_at(k: Nat) -> Nat:
  match k:
    case 0n:
      0n
    case 1n:
      1n
    case 2n:
      3n
    case 3n:
      4n
    case 4n:
      5n
    case 5n:
      6n
    case 6n:
      7n
    case 7n+u:
      0n

def gc_plain_cmd(k: Nat) -> Gc.Cmd:
  match k:
    case 0n:
      Gc.CHelp{}
    case 1n:
      Gc.CSessions{}
    case 2n:
      Gc.CLatest{}
    case 3n:
      Gc.CNew{}
    case 4n:
      Gc.CStop{}
    case 5n:
      Gc.CStatus{}
    case 6n:
      Gc.CMemory{}
    case 7n+u:
      Gc.CHelp{}

# R4: an optional argument as words
def gc_opt(m: Maybe<&2, String>) -> List<&2, String>:
  match m:
    case None{}:
      Nil{}
    case Some{a}:
      [a]

# R8: the spelling of a request and of its reply

def gc_w_req(q: FGc.Req, rest: String) -> String:
  match q:
    case FGc.QParse{t, ns}:
      Wr.put_str(t, Wr.put_list(~String, ~Wr.put_str, ns, rest))

# an optional argument: 0 without, 1 then the argument with one
def gc_w_arg(m: Maybe<&2, String>) -> String:
  match m:
    case None{}:
      Wr.put_nat(0n, "")
    case Some{a}:
      Wr.put_nat(1n, Wr.put_str(a, ""))

def gc_w_cmd(c: Gc.Cmd) -> String:
  match c:
    case Gc.CHelp{}:
      Wr.put_nat(0n, "")
    case Gc.CSessions{}:
      Wr.put_nat(1n, "")
    case Gc.CUse{a}:
      Wr.put_nat(2n, Wr.put_str(a, ""))
    case Gc.CLatest{}:
      Wr.put_nat(3n, "")
    case Gc.CNew{}:
      Wr.put_nat(4n, "")
    case Gc.CStop{}:
      Wr.put_nat(5n, "")
    case Gc.CStatus{}:
      Wr.put_nat(6n, "")
    case Gc.CMemory{}:
      Wr.put_nat(7n, "")
    case Gc.CModel{m}:
      Wr.put_nat(8n, gc_w_arg(m))
    case Gc.CReasoning{m}:
      Wr.put_nat(9n, gc_w_arg(m))
    case Gc.CModelAll{m}:
      Wr.put_nat(10n, gc_w_arg(m))

def gc_w_out(o: Gc.Out) -> String:
  match o:
    case Gc.OCommand{c}:
      Wr.put_nat(0n, gc_w_cmd(c))
    case Gc.OAnswer{t}:
      Wr.put_nat(1n, Wr.put_str(t, ""))
    case Gc.OPrompt{}:
      Wr.put_nat(2n, "")

def gc_w_reply(q: FGc.Req) -> String:
  match q:
    case FGc.QParse{t, ns}:
      gc_w_out(Gc.parse(t, ns))

# every number and length of the request fits the wire
def gc_fit_req(q: FGc.Req) -> Bool:
  match q:
    case FGc.QParse{t, +ns}:
      Bool.and(LawsBase.wire_fits(String.length(t)), Bool.and(LawsBase.wire_fits(List.length(&2, String, ns)), DocCommit.sp_fit_strs(ns)))

# Laws: the meaning of a message
# ------------------------------

# LAW gateway_commands_prompt (R1, R2): every text (written as its
# whitespace runs and words) with no words, or whose first word is not `/`
# then a name of ASCII letters, digits, `-` and `_`, is a prompt, for
# every list of session command names
# EXCLUDES: a path or a sentence taken for a command, a name with other
#   chars accepted, words split at ASCII spaces only
law gateway_commands_prompt:
  for +t: GatewayAnswer.GaText
  for +sess: List<&2, String>
  for +well: {GatewayAnswer.ga_well(t, True{}) == True{} : Bool}
  for first: {gc_slash_first(GatewayAnswer.ga_words_of(t)) == False{} : Bool}
  {Gc.parse(GatewayAnswer.ga_spell(t), sess) == Gc.OPrompt{} : Gc.Out}

# LAW gateway_commands_session (R3): `/` then a name whose ASCII-lowercased
# form is among the session command names is a prompt, with every words
# after it
# EXCLUDES: a session command answered by the gateway, a case-sensitive
#   session name
law gateway_commands_session:
  for +t: GatewayAnswer.GaText
  for +sess: List<&2, String>
  for +name: String
  for +args: List<&2, String>
  for +well: {GatewayAnswer.ga_well(t, True{}) == True{} : Bool}
  for ws: {GatewayAnswer.ga_words_of(t) == SCon{'/', name} <> args : List<&2, String>}
  for nm: {gc_name(name) == True{} : Bool}
  for ses: {gc_in(String.to_lower(name), sess) == True{} : Bool}
  {Gc.parse(GatewayAnswer.ga_spell(t), sess) == Gc.OPrompt{} : Gc.Out}

# LAW gateway_commands_plain (R3, R4): `/` then a name whose
# ASCII-lowercased form is the k-th command that takes no argument (help,
# sessions, latest, new, stop, status, memory) and no session command, with
# no other word, is that command
# EXCLUDES: a case-sensitive name, a command taken for another, a session
#   name preferred to no session name
law gateway_commands_plain:
  for +t: GatewayAnswer.GaText
  for +sess: List<&2, String>
  for +name: String
  for +k: Nat
  for +well: {GatewayAnswer.ga_well(t, True{}) == True{} : Bool}
  for ws: {GatewayAnswer.ga_words_of(t) == [SCon{'/', name}] : List<&2, String>}
  for nm: {gc_name(name) == True{} : Bool}
  for few: {gc_plain_has(k) == True{} : Bool}
  for cmd: {String.to_lower(name) == gc_at(gc_names(), gc_plain_at(k)) : String}
  for own: {gc_in(String.to_lower(name), sess) == False{} : Bool}
  {Gc.parse(GatewayAnswer.ga_spell(t), sess) == Gc.OCommand{gc_plain_cmd(k)} : Gc.Out}

# LAW gateway_commands_plain_usage (R3, R5): the same command name with
# one word or more after it answers `Usage: ` and its line
# EXCLUDES: an argument count ignored, a usage line of another command,
#   the message sent to the agent
law gateway_commands_plain_usage:
  for +t: GatewayAnswer.GaText
  for +sess: List<&2, String>
  for +name: String
  for +k: Nat
  for +a: String
  for +more: List<&2, String>
  for +well: {GatewayAnswer.ga_well(t, True{}) == True{} : Bool}
  for ws: {GatewayAnswer.ga_words_of(t) == SCon{'/', name} <> (a <> more) : List<&2, String>}
  for nm: {gc_name(name) == True{} : Bool}
  for few: {gc_plain_has(k) == True{} : Bool}
  for cmd: {String.to_lower(name) == gc_at(gc_names(), gc_plain_at(k)) : String}
  for own: {gc_in(String.to_lower(name), sess) == False{} : Bool}
  {Gc.parse(GatewayAnswer.ga_spell(t), sess) == Gc.OAnswer{String.append("Usage: ", gc_at(gc_lines(), gc_plain_at(k)))} : Gc.Out}

# LAW gateway_commands_use (R4): `/use` (any ASCII case, no session
# command) with exactly one word a after it is `/use` with a as written
# EXCLUDES: `/use` losing or changing its argument
law gateway_commands_use:
  for +t: GatewayAnswer.GaText
  for +sess: List<&2, String>
  for +name: String
  for +a: String
  for +well: {GatewayAnswer.ga_well(t, True{}) == True{} : Bool}
  for ws: {GatewayAnswer.ga_words_of(t) == [SCon{'/', name}, a] : List<&2, String>}
  for nm: {gc_name(name) == True{} : Bool}
  for cmd: {String.to_lower(name) == "use" : String}
  for own: {gc_in(String.to_lower(name), sess) == False{} : Bool}
  {Gc.parse(GatewayAnswer.ga_spell(t), sess) == Gc.OCommand{Gc.CUse{a}} : Gc.Out}

# LAW gateway_commands_use_usage (R5): `/use` with no word or two or more
# after it answers its usage line
# EXCLUDES: `/use` without its argument taken as a command, extra words
#   dropped
law gateway_commands_use_usage:
  for +t: GatewayAnswer.GaText
  for +sess: List<&2, String>
  for +name: String
  for +args: List<&2, String>
  for +well: {GatewayAnswer.ga_well(t, True{}) == True{} : Bool}
  for ws: {GatewayAnswer.ga_words_of(t) == SCon{'/', name} <> args : List<&2, String>}
  for nm: {gc_name(name) == True{} : Bool}
  for cmd: {String.to_lower(name) == "use" : String}
  for own: {gc_in(String.to_lower(name), sess) == False{} : Bool}
  for count: {Nat.is_eq(List.length(&2, String, args), 1n) == False{} : Bool}
  {Gc.parse(GatewayAnswer.ga_spell(t), sess) == Gc.OAnswer{String.append("Usage: ", gc_at(gc_lines(), 2n))} : Gc.Out}

# LAW gateway_commands_model_list (R4): `/model` (any ASCII case, no session
# command) alone lists the models
# EXCLUDES: `/model` inventing an argument
law gateway_commands_model_list:
  for +t: GatewayAnswer.GaText
  for +sess: List<&2, String>
  for +name: String
  for +well: {GatewayAnswer.ga_well(t, True{}) == True{} : Bool}
  for ws: {GatewayAnswer.ga_words_of(t) == [SCon{'/', name}] : List<&2, String>}
  for nm: {gc_name(name) == True{} : Bool}
  for cmd: {String.to_lower(name) == "model" : String}
  for own: {gc_in(String.to_lower(name), sess) == False{} : Bool}
  {Gc.parse(GatewayAnswer.ga_spell(t), sess) == Gc.OCommand{Gc.CModel{None{}}} : Gc.Out}

# LAW gateway_commands_model_switch (R4): `/model` with exactly one word a
# after it, a not `all` as written, switches to a as written
# EXCLUDES: `/model N` losing N, a switch to a model named `all`
law gateway_commands_model_switch:
  for +t: GatewayAnswer.GaText
  for +sess: List<&2, String>
  for +name: String
  for +a: String
  for +well: {GatewayAnswer.ga_well(t, True{}) == True{} : Bool}
  for ws: {GatewayAnswer.ga_words_of(t) == [SCon{'/', name}, a] : List<&2, String>}
  for nm: {gc_name(name) == True{} : Bool}
  for cmd: {String.to_lower(name) == "model" : String}
  for own: {gc_in(String.to_lower(name), sess) == False{} : Bool}
  for other: {String.eq(a, "all") == False{} : Bool}
  {Gc.parse(GatewayAnswer.ga_spell(t), sess) == Gc.OCommand{Gc.CModel{Some{a}}} : Gc.Out}

# LAW gateway_commands_model_all (R4): `/model all` (the word `all` as
# written) lists the models for the all-roles model
# EXCLUDES: `/model all` taken for a switch to a model named `all`
law gateway_commands_model_all:
  for +t: GatewayAnswer.GaText
  for +sess: List<&2, String>
  for +name: String
  for +well: {GatewayAnswer.ga_well(t, True{}) == True{} : Bool}
  for ws: {GatewayAnswer.ga_words_of(t) == [SCon{'/', name}, "all"] : List<&2, String>}
  for nm: {gc_name(name) == True{} : Bool}
  for cmd: {String.to_lower(name) == "model" : String}
  for own: {gc_in(String.to_lower(name), sess) == False{} : Bool}
  {Gc.parse(GatewayAnswer.ga_spell(t), sess) == Gc.OCommand{Gc.CModelAll{None{}}} : Gc.Out}

# LAW gateway_commands_model_all_set (R4): `/model all n` sets n, as
# written, as the model of every role
# EXCLUDES: `/model all N` losing N or taken as a switch
law gateway_commands_model_all_set:
  for +t: GatewayAnswer.GaText
  for +sess: List<&2, String>
  for +name: String
  for +n: String
  for +well: {GatewayAnswer.ga_well(t, True{}) == True{} : Bool}
  for ws: {GatewayAnswer.ga_words_of(t) == [SCon{'/', name}, "all", n] : List<&2, String>}
  for nm: {gc_name(name) == True{} : Bool}
  for cmd: {String.to_lower(name) == "model" : String}
  for own: {gc_in(String.to_lower(name), sess) == False{} : Bool}
  {Gc.parse(GatewayAnswer.ga_spell(t), sess) == Gc.OCommand{Gc.CModelAll{Some{n}}} : Gc.Out}

# LAW gateway_commands_model_usage_pair (R5): `/model a b` with a not `all`
# as written answers the usage line of `/model`
# EXCLUDES: two arguments taken for a switch, `ALL` taken for `all`
law gateway_commands_model_usage_pair:
  for +t: GatewayAnswer.GaText
  for +sess: List<&2, String>
  for +name: String
  for +a: String
  for +b: String
  for +well: {GatewayAnswer.ga_well(t, True{}) == True{} : Bool}
  for ws: {GatewayAnswer.ga_words_of(t) == [SCon{'/', name}, a, b] : List<&2, String>}
  for nm: {gc_name(name) == True{} : Bool}
  for cmd: {String.to_lower(name) == "model" : String}
  for own: {gc_in(String.to_lower(name), sess) == False{} : Bool}
  for other: {String.eq(a, "all") == False{} : Bool}
  {Gc.parse(GatewayAnswer.ga_spell(t), sess) == Gc.OAnswer{String.append("Usage: ", gc_at(gc_lines(), 8n))} : Gc.Out}

# LAW gateway_commands_model_usage_long (R5): `/model` with three words or
# more after it answers its usage line
# EXCLUDES: extra words after `/model all N` dropped
law gateway_commands_model_usage_long:
  for +t: GatewayAnswer.GaText
  for +sess: List<&2, String>
  for +name: String
  for +a: String
  for +b: String
  for +c: String
  for +more: List<&2, String>
  for +well: {GatewayAnswer.ga_well(t, True{}) == True{} : Bool}
  for ws: {GatewayAnswer.ga_words_of(t) == SCon{'/', name} <> (a <> (b <> (c <> more))) : List<&2, String>}
  for nm: {gc_name(name) == True{} : Bool}
  for cmd: {String.to_lower(name) == "model" : String}
  for own: {gc_in(String.to_lower(name), sess) == False{} : Bool}
  {Gc.parse(GatewayAnswer.ga_spell(t), sess) == Gc.OAnswer{String.append("Usage: ", gc_at(gc_lines(), 8n))} : Gc.Out}

# LAW gateway_commands_reasoning (R4): `/reasoning` (any ASCII case, no
# session command) with no word after it shows the level, with one word
# sets it as written
# EXCLUDES: `/reasoning` losing or inventing its argument
law gateway_commands_reasoning:
  for +t: GatewayAnswer.GaText
  for +sess: List<&2, String>
  for +name: String
  for +m: Maybe<&2, String>
  for +well: {GatewayAnswer.ga_well(t, True{}) == True{} : Bool}
  for ws: {GatewayAnswer.ga_words_of(t) == SCon{'/', name} <> gc_opt(m) : List<&2, String>}
  for nm: {gc_name(name) == True{} : Bool}
  for cmd: {String.to_lower(name) == "reasoning" : String}
  for own: {gc_in(String.to_lower(name), sess) == False{} : Bool}
  {Gc.parse(GatewayAnswer.ga_spell(t), sess) == Gc.OCommand{Gc.CReasoning{m}} : Gc.Out}

# LAW gateway_commands_reasoning_usage (R5): `/reasoning` with two words or
# more after it answers its usage line
# EXCLUDES: extra words dropped
law gateway_commands_reasoning_usage:
  for +t: GatewayAnswer.GaText
  for +sess: List<&2, String>
  for +name: String
  for +a: String
  for +b: String
  for +more: List<&2, String>
  for +well: {GatewayAnswer.ga_well(t, True{}) == True{} : Bool}
  for ws: {GatewayAnswer.ga_words_of(t) == SCon{'/', name} <> (a <> (b <> more)) : List<&2, String>}
  for nm: {gc_name(name) == True{} : Bool}
  for cmd: {String.to_lower(name) == "reasoning" : String}
  for own: {gc_in(String.to_lower(name), sess) == False{} : Bool}
  {Gc.parse(GatewayAnswer.ga_spell(t), sess) == Gc.OAnswer{String.append("Usage: ", gc_at(gc_lines(), 9n))} : Gc.Out}

# LAW gateway_commands_lone_slash (R6, R7): a lone `/` (the empty name not a
# session command) answers the help text
# EXCLUDES: a missing or partial help text, a lone `/` sent to the agent
law gateway_commands_lone_slash:
  for +t: GatewayAnswer.GaText
  for +sess: List<&2, String>
  for +well: {GatewayAnswer.ga_well(t, True{}) == True{} : Bool}
  for ws: {GatewayAnswer.ga_words_of(t) == [SCon{'/', SNil{}}] : List<&2, String>}
  for own: {gc_in("", sess) == False{} : Bool}
  {Gc.parse(GatewayAnswer.ga_spell(t), sess) == Gc.OAnswer{gc_help()} : Gc.Out}

# LAW gateway_commands_listing (R6): `/` then a nonempty name that is no
# command and no session command, alone, when command names start with
# its ASCII-lowercased form, answers their lines in order, each on its own
# line, then `Send one of these. Send / for all commands.`
# EXCLUDES: a listing out of order or missing a starting command, a
#   case-sensitive prefix
law gateway_commands_listing:
  for +t: GatewayAnswer.GaText
  for +sess: List<&2, String>
  for +c: Char
  for +n: String
  for +l: String
  for +ls: List<&2, String>
  for +well: {GatewayAnswer.ga_well(t, True{}) == True{} : Bool}
  for ws: {GatewayAnswer.ga_words_of(t) == [SCon{'/', SCon{c, n}}] : List<&2, String>}
  for nm: {gc_name(SCon{c, n}) == True{} : Bool}
  for own: {gc_in(String.to_lower(SCon{c, n}), sess) == False{} : Bool}
  for none: {gc_in(String.to_lower(SCon{c, n}), gc_names()) == False{} : Bool}
  for pre: {gc_starting(String.to_lower(SCon{c, n}), gc_names(), gc_lines()) == l <> ls : List<&2, String>}
  {Gc.parse(GatewayAnswer.ga_spell(t), sess) == Gc.OAnswer{gc_listing(l <> ls)} : Gc.Out}

# LAW gateway_commands_near (R6): the same name, when no command name
# starts with it and the slash_suggest suggestion over the 10 names picks
# the j-th, answers `No command /<name>. Did you mean /<j-th name>?` and
# `Not sent to the agent. Send / for all commands.` on a second line
# EXCLUDES: a near miss named past the slash_suggest pick, a near miss sent
#   to the agent
law gateway_commands_near:
  for +t: GatewayAnswer.GaText
  for +sess: List<&2, String>
  for +c: Char
  for +n: String
  for +j: Nat
  for +well: {GatewayAnswer.ga_well(t, True{}) == True{} : Bool}
  for ws: {GatewayAnswer.ga_words_of(t) == [SCon{'/', SCon{c, n}}] : List<&2, String>}
  for nm: {gc_name(SCon{c, n}) == True{} : Bool}
  for own: {gc_in(String.to_lower(SCon{c, n}), sess) == False{} : Bool}
  for none: {gc_in(String.to_lower(SCon{c, n}), gc_names()) == False{} : Bool}
  for pre: {gc_starting(String.to_lower(SCon{c, n}), gc_names(), gc_lines()) == Nil{} : List<&2, String>}
  for sug: {Ss.suggest(String.to_lower(SCon{c, n}), gc_names()) == Some{j} : Maybe<&2, Nat>}
  {Gc.parse(GatewayAnswer.ga_spell(t), sess) == Gc.OAnswer{String.concat(["No command /", String.to_lower(SCon{c, n}), ". Did you mean /", gc_at(gc_names(), j), "?\nNot sent to the agent. Send / for all commands."])} : Gc.Out}

# LAW gateway_commands_far (R6, R7): the same name, when no command name
# starts with it and slash_suggest picks none, answers `No command
# /<name>. Not sent to the agent.` and the help text on the next lines
# EXCLUDES: a missing help text after a far miss
law gateway_commands_far:
  for +t: GatewayAnswer.GaText
  for +sess: List<&2, String>
  for +c: Char
  for +n: String
  for +well: {GatewayAnswer.ga_well(t, True{}) == True{} : Bool}
  for ws: {GatewayAnswer.ga_words_of(t) == [SCon{'/', SCon{c, n}}] : List<&2, String>}
  for nm: {gc_name(SCon{c, n}) == True{} : Bool}
  for own: {gc_in(String.to_lower(SCon{c, n}), sess) == False{} : Bool}
  for none: {gc_in(String.to_lower(SCon{c, n}), gc_names()) == False{} : Bool}
  for pre: {gc_starting(String.to_lower(SCon{c, n}), gc_names(), gc_lines()) == Nil{} : List<&2, String>}
  for sug: {Ss.suggest(String.to_lower(SCon{c, n}), gc_names()) == None{} : Maybe<&2, Nat>}
  {Gc.parse(GatewayAnswer.ga_spell(t), sess) == Gc.OAnswer{String.concat(["No command /", String.to_lower(SCon{c, n}), ". Not sent to the agent.\n", gc_help()])} : Gc.Out}

# LAW gateway_commands_unknown_words (R6): `/` then a name that is no
# command and no session command, followed by one word or more, is a
# prompt
# EXCLUDES: an unknown name with more words answered by the gateway
law gateway_commands_unknown_words:
  for +t: GatewayAnswer.GaText
  for +sess: List<&2, String>
  for +name: String
  for +a: String
  for +more: List<&2, String>
  for +well: {GatewayAnswer.ga_well(t, True{}) == True{} : Bool}
  for ws: {GatewayAnswer.ga_words_of(t) == SCon{'/', name} <> (a <> more) : List<&2, String>}
  for nm: {gc_name(name) == True{} : Bool}
  for own: {gc_in(String.to_lower(name), sess) == False{} : Bool}
  for none: {gc_in(String.to_lower(name), gc_names()) == False{} : Bool}
  {Gc.parse(GatewayAnswer.ga_spell(t), sess) == Gc.OPrompt{} : Gc.Out}

# LAW gateway_commands_example (R1-R7): anchor: the vectors of Rust's tests
# the_core_parses_phone_messages and
# model_and_reasoning_parse_with_and_without_arguments
# (crates/eukhe-gateway/src/commands.rs), with Rust's session command names
# (eukhe-types SESSION_SLASH_COMMAND_NAMES)
# EXCLUDES: a code that drifts from the Rust test vectors
law gateway_commands_example:
  {[Gc.parse("/help", ["compact", "refine", "goal", "autonomous", "remind", "force", "dynamic-workflow", "autoresearch"]), Gc.parse("/dynamic-workflow --size large review the repo", ["compact", "refine", "goal", "autonomous", "remind", "force", "dynamic-workflow", "autoresearch"]), Gc.parse("/compact", ["compact", "refine", "goal", "autonomous", "remind", "force", "dynamic-workflow", "autoresearch"]), Gc.parse("/use 3", ["compact", "refine", "goal", "autonomous", "remind", "force", "dynamic-workflow", "autoresearch"]), Gc.parse("/hlep", ["compact", "refine", "goal", "autonomous", "remind", "force", "dynamic-workflow", "autoresearch"]), Gc.parse("/model", ["compact", "refine", "goal", "autonomous", "remind", "force", "dynamic-workflow", "autoresearch"]), Gc.parse("/model 2", ["compact", "refine", "goal", "autonomous", "remind", "force", "dynamic-workflow", "autoresearch"]), Gc.parse("/reasoning", ["compact", "refine", "goal", "autonomous", "remind", "force", "dynamic-workflow", "autoresearch"]), Gc.parse("/reasoning high", ["compact", "refine", "goal", "autonomous", "remind", "force", "dynamic-workflow", "autoresearch"]), Gc.parse("/model 2 3", ["compact", "refine", "goal", "autonomous", "remind", "force", "dynamic-workflow", "autoresearch"]), Gc.parse("/reasoning low extra", ["compact", "refine", "goal", "autonomous", "remind", "force", "dynamic-workflow", "autoresearch"]), Gc.parse("/model all", ["compact", "refine", "goal", "autonomous", "remind", "force", "dynamic-workflow", "autoresearch"]), Gc.parse("/model all 3", ["compact", "refine", "goal", "autonomous", "remind", "force", "dynamic-workflow", "autoresearch"]), Gc.parse("/model all 3 4", ["compact", "refine", "goal", "autonomous", "remind", "force", "dynamic-workflow", "autoresearch"])] == [Gc.OCommand{Gc.CHelp{}}, Gc.OPrompt{}, Gc.OPrompt{}, Gc.OCommand{Gc.CUse{"3"}}, Gc.OAnswer{"No command /hlep. Did you mean /help?\nNot sent to the agent. Send / for all commands."}, Gc.OCommand{Gc.CModel{None{}}}, Gc.OCommand{Gc.CModel{Some{"2"}}}, Gc.OCommand{Gc.CReasoning{None{}}}, Gc.OCommand{Gc.CReasoning{Some{"high"}}}, Gc.OAnswer{"Usage: /model [all] [N] - Show the models; N switches to one; all N uses it for every role."}, Gc.OAnswer{"Usage: /reasoning [level] - Show the thinking level; a level sets it."}, Gc.OCommand{Gc.CModelAll{None{}}}, Gc.OCommand{Gc.CModelAll{Some{"3"}}}, Gc.OAnswer{"Usage: /model [all] [N] - Show the models; N switches to one; all N uses it for every role."}] : List<&2, Gc.Out>}

# LAW gateway_commands_more_example (R1-R7): anchor, in no Rust test: a
# lone `/`, a prefix, `/use` alone, a path, an unknown name with words, an
# uppercase name, a far miss, a blank text, a prefix of three commands,
# extra spaces, `/stop` with a word, an uppercase `/Reasoning`, the prefix
# `/m` of memory and model, `/model ALL 3` (only the word `all` as written)
# EXCLUDES: a code that drifts from these vectors
law gateway_commands_more_example:
  {[Gc.parse("/", []), Gc.parse("/he", []), Gc.parse("/use", []), Gc.parse("/tmp/x", []), Gc.parse("/xyz more words", []), Gc.parse("/HELP", []), Gc.parse("/xyz", []), Gc.parse(" \n", []), Gc.parse("/s", []), Gc.parse(" /use  a ", []), Gc.parse("/stop x", []), Gc.parse("/Reasoning", []), Gc.parse("/m", []), Gc.parse("/model ALL 3", [])] == [Gc.OAnswer{gc_help()}, Gc.OAnswer{"/help - Show the commands.\nSend one of these. Send / for all commands."}, Gc.OAnswer{"Usage: /use N - Send messages to session N."}, Gc.OPrompt{}, Gc.OPrompt{}, Gc.OCommand{Gc.CHelp{}}, Gc.OAnswer{String.append("No command /xyz. Not sent to the agent.\n", gc_help())}, Gc.OPrompt{}, Gc.OAnswer{"/sessions - Show the newest sessions.\n/stop - Stop the current turn.\n/status - Show the session state.\nSend one of these. Send / for all commands."}, Gc.OCommand{Gc.CUse{"a"}}, Gc.OAnswer{"Usage: /stop - Stop the current turn."}, Gc.OCommand{Gc.CReasoning{None{}}}, Gc.OAnswer{"/memory - Show the chat memory state.\n/model [all] [N] - Show the models; N switches to one; all N uses it for every role.\nSend one of these. Send / for all commands."}, Gc.OAnswer{"Usage: /model [all] [N] - Show the models; N switches to one; all N uses it for every role."}] : List<&2, Gc.Out>}

# Laws: the entry (R8)
# --------------------

# LAW gateway_commands_entry_answers (R8): the entry answers every request
# Rust spells, every length within the wire, with the spelled meaning of
# the model Gc.parse (pinned by the laws of R1-R7 above)
# EXCLUDES: the text and the session names swapped, a session name
#   dropped, command tags in another order, `/use` without its argument,
#   `/model all` spelled as `/model`, an answer spelled as a prompt, a
#   default
law gateway_commands_entry_answers:
  for +q: FGc.Req
  for h: {gc_fit_req(q) == True{} : Bool}
  {FGc.ffi(gc_w_req(q, "")) == gc_w_reply(q) : String}

# LAW gateway_commands_entry_reads (R8): the entry's decoder reads a
# spelled request back whole and leaves the input after it untouched
# EXCLUDES: a decoder that eats or skips input after the request
law gateway_commands_entry_reads:
  for +q: FGc.Req
  for +rest: String
  for h: {gc_fit_req(q) == True{} : Bool}
  {FGc.get_req(gc_w_req(q, rest)) == Wr.Got{q, rest} : Wr.Dec<FGc.Req>}

# LAW gateway_commands_entry_exact (R8): every input the entry does not
# answer with the error form is a spelled request that fits the wire
# EXCLUDES: a meaning given to input that is no request (a malformed
#   field, input left over)
law gateway_commands_entry_exact:
  for +s: String
  for ok: {LawsBase.wire_opens_err(FGc.ffi(s)) == False{} : Bool}
  exs r: FGc.Req
  {s == gc_w_req(r, "") : String} & {gc_fit_req(r) == True{} : Bool}

# LAW gateway_commands_entry_refuses (R8): every error the entry answers
# is exactly `E gateway_commands: malformed request`
# EXCLUDES: an error text that varies with the input, a second error form
law gateway_commands_entry_refuses:
  for +s: String
  for bad: {LawsBase.wire_opens_err(FGc.ffi(s)) == True{} : Bool}
  {FGc.ffi(s) == Wr.err("gateway_commands: malformed request") : String}

# LAW gateway_commands_entry_example (R8): anchor: the wire strings Rust
# sends and the replies it reads: a command, `/use` with its argument, a
# usage answer, a session command, a prompt; input left over and a
# malformed request; `/model` without and with its argument, `/reasoning`
# with its argument, a `/model` usage answer; `/model all` without and
# with its argument
# EXCLUDES: a field order other than Rust's, another reply spelling
law gateway_commands_entry_example:
  {[FGc.ffi("5,/help0,"), FGc.ffi("6,/use 30,"), FGc.ffi("4,/use0,"), FGc.ffi("8,/compact1,7,compact"), FGc.ffi("2,hi0,"), FGc.ffi("5,/help0,x"), FGc.ffi("x"), FGc.ffi("6,/model0,"), FGc.ffi("8,/model 20,"), FGc.ffi("15,/reasoning high0,"), FGc.ffi("10,/model 2 30,"), FGc.ffi("10,/model all0,"), FGc.ffi("12,/model all 30,")] == ["0,0,", "0,2,1,3", "1,43,Usage: /use N - Send messages to session N.", "2,", "2,", Wr.err("gateway_commands: malformed request"), Wr.err("gateway_commands: malformed request"), "0,8,0,", "0,8,1,1,2", "0,9,1,4,high", "1,91,Usage: /model [all] [N] - Show the models; N switches to one; all N uses it for every role.", "0,10,0,", "0,10,1,1,3"] : List<&2, String>}

