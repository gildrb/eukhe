# eukhe: the laws of area gateway_commands

import Base
import ../bend/gateway_commands.bend as Gc
import ../bend/ffi_gateway_commands.bend as FGc
import ../bend/wire.bend as Wr
import ./base.bend as LawsBase
import ./gateway_answer.bend as GatewayAnswer
import ./slash_suggest.bend as SlashSuggest
import ./doc_commit.bend as DocCommit

# (D1) What one phone text message means to the Signal gateway
# ------------------------------------------------------------
# bend/gateway_commands.bend, run as the compiled core by
# bend/ffi_gateway_commands.bend (crates/eukhe-gateway commands.rs, called
# by gateway.rs for every text message without images). Every input is
# free: any text, any list of session command names.
#
# R1: the words of the text are Rust's `split_whitespace` words (split at
#     the Unicode White_Space chars, none empty).
# R2: no words, or a first word that is not `/` then a name of ASCII
#     letters, digits, `-` and `_` only (the empty name too), is a prompt.
# R3: the name is read with its ASCII letters lowercased; a name among the
#     session command names Rust sends is a prompt (the session runs it).
# R4: the commands, in order: help, sessions, use, latest, new, stop,
#     status, memory. `/use` takes exactly one argument (kept as written),
#     the others none; a command name with exactly its arguments is that
#     command.
# R5: a command name with other arguments answers
#     `Usage: <usage> - <description>` (its line of gc_lines).
# R6: another name followed by more words is a prompt. Alone it answers:
#     for the empty name (a lone `/`), the help text; else, when command
#     names start with it, their lines in order, each on its own line,
#     then `Send one of these. Send / for all commands.`; else, when the
#     slash_suggest suggestion over the 8 names picks one,
#     `No command /<name>. Did you mean /<closest>?` and on a second line
#     `Not sent to the agent. Send / for all commands.`; else
#     `No command /<name>. Not sent to the agent.` and on the next lines
#     the help text.
# R7: the help text: `Commands:`, each command's line, then
#     `Other text goes to the agent.`, one per line.
# R8: the entry answers each request Rust writes (the text and the session
#     names, every length within the wire) with the meaning of R1-R7 (a
#     command by its tag, `/use` with its argument; an answer with its
#     text; a prompt), reads exactly the request and nothing after it, and
#     answers any other input with the exact error form
#     `E gateway_commands: malformed request`.

# Spec helpers
# ------------

# R4: the command names, in order
def gc_names() -> List<&2, String>:
  ["help", "sessions", "use", "latest", "new", "stop", "status", "memory"]

# R5: the command lines, in the same order
def gc_lines() -> List<&2, String>:
  ["/help - Show the commands.", "/sessions - Show the newest sessions.", "/use N - Send messages to session N.", "/latest - Send messages to the newest session.", "/new - Start a new session.", "/stop - Stop the current turn.", "/status - Show the session state.", "/memory - Show the chat memory state."]

# R7
def gc_help() -> String:
  "Commands:\n/help - Show the commands.\n/sessions - Show the newest sessions.\n/use N - Send messages to session N.\n/latest - Send messages to the newest session.\n/new - Start a new session.\n/stop - Stop the current turn.\n/status - Show the session state.\n/memory - Show the chat memory state.\nOther text goes to the agent."

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

def gc_index.at(here: Bool, i: Nat, later: Maybe<&2, Nat>) -> Maybe<&2, Nat>:
  match here:
    case True{}:
      Some{i}
    case False{}:
      later

# R4: the index of the first of xs equal to n, counted from i
def gc_index(+n: String, xs: List<&2, String>, +i: Nat) -> Maybe<&2, Nat>:
  match xs:
    case Nil{}:
      None{}
    case x <> t:
      gc_index.at(String.eq(n, x), i, gc_index(n, t, 1n+i))

# R4: the command at index i without arguments
def gc_bare(i: Nat) -> Maybe<&2, Gc.Cmd>:
  match i:
    case 0n:
      Some{Gc.CHelp{}}
    case 1n:
      Some{Gc.CSessions{}}
    case 2n:
      None{}
    case 3n:
      Some{Gc.CLatest{}}
    case 4n:
      Some{Gc.CNew{}}
    case 5n:
      Some{Gc.CStop{}}
    case 6n:
      Some{Gc.CStatus{}}
    case 7n:
      Some{Gc.CMemory{}}
    case 8n+u:
      None{}

# R4: the command at index i with the one argument a
def gc_one(i: Nat, a: String) -> Maybe<&2, Gc.Cmd>:
  match i:
    case 0n:
      None{}
    case 1n:
      None{}
    case 2n:
      Some{Gc.CUse{a}}
    case 3n+u:
      None{}

# R4: the command at index i given args, when they are its own
def gc_command(i: Nat, args: List<&2, String>) -> Maybe<&2, Gc.Cmd>:
  match args:
    case Nil{}:
      gc_bare(i)
    case a <> t:
      match t:
        case Nil{}:
          gc_one(i, a)
        case b <> u:
          None{}

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

# R6: no command starts with n
def gc_far(+n: String, m: Maybe<&2, Nat>) -> String:
  match m:
    case None{}:
      String.concat(["No command /", n, ". Not sent to the agent.\n", gc_help()])
    case Some{j}:
      String.concat(["No command /", n, ". Did you mean /", gc_at(gc_names(), j), "?\nNot sent to the agent. Send / for all commands."])

def gc_listed(+n: String, ls: List<&2, String>) -> String:
  match ls:
    case Nil{}:
      gc_far(n, SlashSuggest.sp_suggest(n, gc_names()))
    case l <> t:
      gc_listing(l <> t)

# R6: the answer to the name n alone
def gc_suggest(n: String) -> String:
  match n:
    case SNil{}:
      gc_help()
    case SCon{+c, +t}:
      gc_listed(SCon{c, t}, gc_starting(SCon{c, t}, gc_names(), gc_lines()))

def gc_unknown(+n: String, args: List<&2, String>) -> Gc.Out:
  match args:
    case Nil{}:
      Gc.OAnswer{gc_suggest(n)}
    case a <> t:
      Gc.OPrompt{}

# R5
def gc_exact(m: Maybe<&2, Gc.Cmd>, i: Nat) -> Gc.Out:
  match m:
    case None{}:
      Gc.OAnswer{String.append("Usage: ", gc_at(gc_lines(), i))}
    case Some{c}:
      Gc.OCommand{c}

def gc_found(+n: String, args: List<&2, String>, m: Maybe<&2, Nat>) -> Gc.Out:
  match m:
    case None{}:
      gc_unknown(n, args)
    case Some{+i}:
      gc_exact(gc_command(i, args), i)

# R3: a session command or not
def gc_decide(session: Bool, +n: String, args: List<&2, String>) -> Gc.Out:
  match session:
    case True{}:
      Gc.OPrompt{}
    case False{}:
      gc_found(n, args, gc_index(n, gc_names(), 0n))

def gc_word.at(cmd: Bool, +name: String, args: List<&2, String>, sess: List<&2, String>) -> Gc.Out:
  match cmd:
    case True{}:
      +n = String.to_lower(name)
      gc_decide(gc_in(n, sess), n, args)
    case False{}:
      Gc.OPrompt{}

# R2: the first word w
def gc_word(w: String, args: List<&2, String>, sess: List<&2, String>) -> Gc.Out:
  match w:
    case SNil{}:
      Gc.OPrompt{}
    case SCon{c, +name}:
      gc_word.at(Bool.and(Char.is_eq(c, '/'), gc_name(name)), name, args, sess)

def gc_parse.at(ws: List<&2, String>, sess: List<&2, String>) -> Gc.Out:
  match ws:
    case Nil{}:
      Gc.OPrompt{}
    case w <> args:
      gc_word(w, args, sess)

# R1-R7: what text means, given the session command names sess
def gc_parse(text: String, sess: List<&2, String>) -> Gc.Out:
  gc_parse.at(GatewayAnswer.ga_split(text), sess)

# R8: the spelling of a request and of its reply

def gc_w_req(q: FGc.Req, rest: String) -> String:
  match q:
    case FGc.QParse{t, ns}:
      Wr.put_str(t, Wr.put_list(~String, ~Wr.put_str, ns, rest))

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
      gc_w_out(gc_parse(t, ns))

# every number and length of the request fits the wire
def gc_fit_req(q: FGc.Req) -> Bool:
  match q:
    case FGc.QParse{t, +ns}:
      Bool.and(LawsBase.wire_fits(String.length(t)), Bool.and(LawsBase.wire_fits(List.length(&2, String, ns)), DocCommit.sp_fit_strs(ns)))

# Laws: the meaning of a message
# ------------------------------

# LAW gateway_commands_spec (R1-R7): what every text means, given every
# list of session command names, is the spec's
# EXCLUDES: words split at ASCII spaces only, a path or a sentence taken
#   for a command, a name with other chars accepted, a case-sensitive
#   name, a session command answered by the gateway, an argument count
#   ignored or checked for the wrong command, `/use` losing its argument,
#   a usage line of another command, an unknown name with more words
#   answered, a listing out of order or missing a starting command, a near
#   miss named past the slash_suggest limit, a missing help text after a
#   far miss
law gateway_commands_spec:
  for +text: String
  for +sess: List<&2, String>
  {Gc.parse(text, sess) == gc_parse(text, sess) : Gc.Out}

# LAW gateway_commands_example (R1-R7): anchor: Rust's vectors, short: a
# command, a lone `/`, a prefix, a near miss, `/use 3`, `/use` alone, a
# path, an unknown name with words, a session command, an uppercase name,
# a far miss, a blank text, a prefix of three commands, extra spaces
# EXCLUDES: a spec that drifts from the Rust it replaced
law gateway_commands_example:
  {[Gc.parse("/help", []), Gc.parse("/", []), Gc.parse("/he", []), Gc.parse("/hlep", []), Gc.parse("/use 3", []), Gc.parse("/use", []), Gc.parse("/tmp/x", []), Gc.parse("/xyz more words", []), Gc.parse("/compact", ["compact"]), Gc.parse("/HELP", []), Gc.parse("/xyz", []), Gc.parse(" \n", []), Gc.parse("/s", []), Gc.parse(" /use  a ", []), Gc.parse("/stop x", [])] == [Gc.OCommand{Gc.CHelp{}}, Gc.OAnswer{gc_help()}, Gc.OAnswer{"/help - Show the commands.\nSend one of these. Send / for all commands."}, Gc.OAnswer{"No command /hlep. Did you mean /help?\nNot sent to the agent. Send / for all commands."}, Gc.OCommand{Gc.CUse{"3"}}, Gc.OAnswer{"Usage: /use N - Send messages to session N."}, Gc.OPrompt{}, Gc.OPrompt{}, Gc.OPrompt{}, Gc.OCommand{Gc.CHelp{}}, Gc.OAnswer{String.append("No command /xyz. Not sent to the agent.\n", gc_help())}, Gc.OPrompt{}, Gc.OAnswer{"/sessions - Show the newest sessions.\n/stop - Stop the current turn.\n/status - Show the session state.\nSend one of these. Send / for all commands."}, Gc.OCommand{Gc.CUse{"a"}}, Gc.OAnswer{"Usage: /stop - Stop the current turn."}] : List<&2, Gc.Out>}

# Laws: the entry (R8)
# --------------------

# LAW gateway_commands_entry_answers (R8): the entry answers every request
# Rust spells, every length within the wire, with the spelled meaning of
# the spec
# EXCLUDES: the text and the session names swapped, a session name
#   dropped, command tags in another order, `/use` without its argument,
#   an answer spelled as a prompt, a default
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
# malformed request
# EXCLUDES: a field order other than Rust's, another reply spelling
law gateway_commands_entry_example:
  {[FGc.ffi("5,/help0,"), FGc.ffi("6,/use 30,"), FGc.ffi("4,/use0,"), FGc.ffi("8,/compact1,7,compact"), FGc.ffi("2,hi0,"), FGc.ffi("5,/help0,x"), FGc.ffi("x")] == ["0,0,", "0,2,1,3", "1,43,Usage: /use N - Send messages to session N.", "2,", "2,", Wr.err("gateway_commands: malformed request"), Wr.err("gateway_commands: malformed request")] : List<&2, String>}
