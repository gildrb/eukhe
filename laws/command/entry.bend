# eukhe: the laws of area command, section entry: the entry of the
# compiled core for the slash command paths (bend/ffi_command.bend)

import Base
import ../../bend/command.bend as Cmd
import ../../bend/ffi_command.bend as FCmd
import ../../bend/wire.bend as Wr
import ../base.bend as LawsBase

# LAWS (R14 of laws/command/paths.bend): the entry reads every request that
# fits back whole, answers the model, refuses input left over and
# malformed input; every reply reads back. Each law is an open claim
# about bend/ffi_command.bend; the proofs are proof/command/<law>.bend.
#
#   R14a a request Rust spells (the grammar of the header of
#        bend/ffi_command.bend, every count, length and place within the
#        wire) is answered with the spelling of the model's answer about
#        the table it carries          command_ffi_decides
#   R14b input left over after a spelled request is refused
#                                      command_ffi_spelled_left_over
#   R14c every answer that is not the error form answers exactly the one
#        request the input spells      command_ffi_reads_only_requests
#   R14d a query, row or key tag the grammar does not name is malformed
#                                      command_ffi_unknown_query,
#                                      command_ffi_unknown_row,
#                                      command_ffi_unknown_press
#   R14e the exact strings Rust sends and reads   command_ffi_example
#   R14f a reply tag the reply grammar does not name reads as no reply
#        (one spelling per answer)    command_ffi_unknown_res,
#                                     command_ffi_unknown_menu
# The requests and replies of these laws are spelled with the spec
# spellers below and those of laws/base.bend, never with the entry's own
# encoders.

# Spec helpers
# ------------

# every string of xs fits the wire
def cmd_strs_all(xs: List<&2, String>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{+x, rest}:
      Bool.and(LawsBase.wire_fits(String.length(x)), cmd_strs_all(rest))

# every string of xs fits the wire, and so does their count
def cmd_strs_fit(+xs: List<&2, String>) -> Bool:
  Bool.and(LawsBase.wire_fits(List.length(&2, String, xs)), cmd_strs_all(xs))

def cmd_ent_fits(e: FCmd.EntW) -> Bool:
  match e:
    case FCmd.EntW{p, a, r, f, g}:
      Bool.and(cmd_strs_fit(p), cmd_strs_fit(a))

def cmd_ents_all(t: List<&2, FCmd.EntW>) -> Bool:
  match t:
    case Nil{}:
      True{}
    case Con{e, rest}:
      Bool.and(cmd_ent_fits(e), cmd_ents_all(rest))

def cmd_sel_fits(x: Cmd.Sel) -> Bool:
  match x:
    case Cmd.NoRow{}:
      True{}
    case Cmd.Row{i}:
      LawsBase.wire_fits(i)

def cmd_query_fits(q: FCmd.Query) -> Bool:
  match q:
    case FCmd.QResolve{l}:
      LawsBase.wire_fits(String.length(l))
    case FCmd.QMenu{l}:
      LawsBase.wire_fits(String.length(l))
    case FCmd.QKey{l, x, k}:
      Bool.and(LawsBase.wire_fits(String.length(l)), cmd_sel_fits(x))

# every count, length and place of a request fits the wire
def cmd_req_fits(r: FCmd.Req) -> Bool:
  match r:
    case FCmd.Req{+t, q}:
      Bool.and(Bool.and(LawsBase.wire_fits(List.length(&2, FCmd.EntW, t)), cmd_ents_all(t)), cmd_query_fits(q))

def cmd_res_fits(r: FCmd.ResW) -> Bool:
  match r:
    case FCmd.RunsW{p, a}:
      Bool.and(cmd_strs_fit(p), LawsBase.wire_fits(String.length(a)))
    case FCmd.OpensW{p}:
      cmd_strs_fit(p)
    case FCmd.UnknownW{p, w}:
      Bool.and(cmd_strs_fit(p), LawsBase.wire_fits(String.length(w)))
    case FCmd.NoCmdW{}:
      True{}

def cmd_menu_fits(m: FCmd.MenuW) -> Bool:
  match m:
    case FCmd.NamesW{}:
      True{}
    case FCmd.KidsW{p, +xs}:
      Bool.and(cmd_strs_fit(p), Bool.and(LawsBase.wire_fits(List.length(&2, Nat, xs)), LawsBase.wire_nats_fit(xs)))
    case FCmd.ShutW{}:
      True{}

def cmd_out_fits(o: FCmd.OutW) -> Bool:
  match o:
    case FCmd.OutW{l, a, b}:
      LawsBase.wire_fits(String.length(l))

# LAW command_ffi_round_trip: every request that fits the wire reads back
# as itself, and its reading consumes exactly its encoding
# EXCLUDES: a name, flag, line, row or key lost, swapped or misread on
#   the way to the model
law command_ffi_round_trip:
  for +r: FCmd.Req
  for +rest: String
  for h: {cmd_req_fits(r) == True{} : Bool}
  {FCmd.get_req(FCmd.put_req(r, rest)) == Wr.Got{r, rest} : Wr.Dec<FCmd.Req>}

# LAW command_ffi_answers: the entry answers a request with the model's
# answer about the table it carries
# EXCLUDES: an entry that answers another question, another table, or a
#   default
law command_ffi_answers:
  for +r: FCmd.Req
  for h: {cmd_req_fits(r) == True{} : Bool}
  {FCmd.ffi(FCmd.put_req(r, "")) == FCmd.ffi.run(r) : String}

# LAW command_ffi_left_over: a request with input left over after it is
# refused
# EXCLUDES: trailing input read as part of a request, or ignored
law command_ffi_left_over:
  for +r: FCmd.Req
  for +rest: String
  for h: {cmd_req_fits(r) == True{} : Bool}
  for more: {String.is_empty(rest) == False{} : Bool}
  {FCmd.ffi(FCmd.put_req(r, rest)) == Wr.err("command: input left over") : String}

# LAW command_ffi_malformed: a malformed request answers the error form,
# never an answer
# EXCLUDES: a default answer (a run, a menu) for input the entry cannot
#   read
law command_ffi_malformed:
  for +s: String
  for bad: {FCmd.get_req(s) == Wr.Bad{} : Wr.Dec<FCmd.Req>}
  {FCmd.ffi(s) == Wr.err("command: malformed request") : String}

# LAW command_ffi_res_round_trip: every resolve reply that fits reads
# back as itself (Rust's Reader reads the same grammar)
# EXCLUDES: two answers with one encoding, an answer Rust misreads
law command_ffi_res_round_trip:
  for +x: FCmd.ResW
  for +rest: String
  for h: {cmd_res_fits(x) == True{} : Bool}
  {FCmd.get_res(FCmd.put_res(x, rest)) == Wr.Got{x, rest} : Wr.Dec<FCmd.ResW>}

# LAW command_ffi_menu_round_trip: every menu reply that fits reads back
# as itself
# EXCLUDES: two menus with one encoding, a menu Rust misreads
law command_ffi_menu_round_trip:
  for +x: FCmd.MenuW
  for +rest: String
  for h: {cmd_menu_fits(x) == True{} : Bool}
  {FCmd.get_menu(FCmd.put_menu(x, rest)) == Wr.Got{x, rest} : Wr.Dec<FCmd.MenuW>}

# LAW command_ffi_out_round_trip: every key reply that fits reads back as
# itself
# EXCLUDES: a new line, menu flag or submit flag Rust misreads
law command_ffi_out_round_trip:
  for +x: FCmd.OutW
  for +rest: String
  for h: {cmd_out_fits(x) == True{} : Bool}
  {FCmd.get_out(FCmd.put_out(x, rest)) == Wr.Got{x, rest} : Wr.Dec<FCmd.OutW>}

# LAW command_ffi_witness: a request that fits exists, a malformed one
# exists, and input can be left over
law command_ffi_witness:
  exs r: FCmd.Req
  exs s: String
  exs rest: String
  {(cmd_req_fits(r), (FCmd.get_req(s), String.is_empty(rest))) == (True{}, (Wr.Bad{}, False{})) : Bool & (Wr.Dec<FCmd.Req> & Bool)}

# Spec spellers
# -------------
# The grammar of the header of bend/ffi_command.bend, spelled with the
# spellers of laws/base.bend and the wire primitives; names and lines
# cross as strings, the model reads them as char codes.

# the char codes of s, as the model reads a line or a name
def cmd_codes(s: String) -> List<&2, Nat>:
  match s:
    case SNil{}:
      Nil{}
    case SCon{c, r}:
      U32.to_nat(Char.to_u32(c)) <> cmd_codes(r)

# the string of the char codes ns, as a reply carries a line or a name
def cmd_text(ns: List<&2, Nat>) -> String:
  match ns:
    case Nil{}:
      SNil{}
    case Con{n, r}:
      SCon{Chr{U32.from_nat(n)}, cmd_text(r)}

def cmd_texts(ps: List<&2, List<&2, Nat>>) -> List<&2, String>:
  match ps:
    case Nil{}:
      Nil{}
    case Con{p, r}:
      cmd_text(p) <> cmd_texts(r)

def cmd_name_codes(xs: List<&2, String>) -> List<&2, List<&2, Nat>>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{x, r}:
      cmd_codes(x) <> cmd_name_codes(r)

# the table as the model reads it: every name as char codes
def cmd_model_table(t: List<&2, FCmd.EntW>) -> List<&2, Cmd.Ent>:
  match t:
    case Nil{}:
      Nil{}
    case Con{FCmd.EntW{p, a, r, f, g}, rest}:
      Cmd.Ent{cmd_name_codes(p), cmd_name_codes(a), r, f, g} <> cmd_model_table(rest)

# an entry: its path, its aliases, then run, free and arg
def cmd_spell_ent(e: FCmd.EntW, rest: String) -> String:
  match e:
    case FCmd.EntW{p, a, r, f, g}:
      LawsBase.wire_spell_strs(p, LawsBase.wire_spell_strs(a, Wr.put_bool(r, Wr.put_bool(f, Wr.put_bool(g, rest)))))

def cmd_spell_ents(t: List<&2, FCmd.EntW>, rest: String) -> String:
  match t:
    case Nil{}:
      rest
    case Con{e, more}:
      cmd_spell_ent(e, cmd_spell_ents(more, rest))

# a table: its count, then its entries
def cmd_spell_table(+t: List<&2, FCmd.EntW>, rest: String) -> String:
  Wr.put_nat(List.length(&2, FCmd.EntW, t), cmd_spell_ents(t, rest))

# a row: tag 0 none, tag 1 then its place
def cmd_spell_sel(x: Cmd.Sel, rest: String) -> String:
  match x:
    case Cmd.NoRow{}:
      Wr.put_nat(0n, rest)
    case Cmd.Row{i}:
      Wr.put_nat(1n, Wr.put_nat(i, rest))

# a key: tag 0 Tab, tag 1 Enter
def cmd_spell_press(k: Cmd.Press, rest: String) -> String:
  match k:
    case Cmd.Tab{}:
      Wr.put_nat(0n, rest)
    case Cmd.Enter{}:
      Wr.put_nat(1n, rest)

# a question: tag 0 resolve, 1 menu, 2 key; then its line (and for a key
# its row and key)
def cmd_spell_query(q: FCmd.Query, rest: String) -> String:
  match q:
    case FCmd.QResolve{l}:
      Wr.put_nat(0n, Wr.put_str(l, rest))
    case FCmd.QMenu{l}:
      Wr.put_nat(1n, Wr.put_str(l, rest))
    case FCmd.QKey{l, x, k}:
      Wr.put_nat(2n, Wr.put_str(l, cmd_spell_sel(x, cmd_spell_press(k, rest))))

# a request: the table, then the question
def cmd_spell_req(r: FCmd.Req, rest: String) -> String:
  match r:
    case FCmd.Req{t, q}:
      cmd_spell_table(t, cmd_spell_query(q, rest))

# a resolution: tag 0 runs (path, text), 1 opens (path), 2 unknown (path,
# word), 3 no command
def cmd_spell_res(x: Cmd.Res) -> String:
  match x:
    case Cmd.Runs{p, a}:
      Wr.put_nat(0n, LawsBase.wire_spell_strs(cmd_texts(p), Wr.put_str(cmd_text(a), "")))
    case Cmd.Opens{p}:
      Wr.put_nat(1n, LawsBase.wire_spell_strs(cmd_texts(p), ""))
    case Cmd.Unknown{p, w}:
      Wr.put_nat(2n, LawsBase.wire_spell_strs(cmd_texts(p), Wr.put_str(cmd_text(w), "")))
    case Cmd.NoCmd{}:
      Wr.put_nat(3n, "")

# a menu: tag 0 the command names, 1 the children (path, places), 2 none
def cmd_spell_menu(m: Cmd.Menu) -> String:
  match m:
    case Cmd.Names{}:
      Wr.put_nat(0n, "")
    case Cmd.Kids{p, xs}:
      Wr.put_nat(1n, LawsBase.wire_spell_strs(cmd_texts(p), LawsBase.wire_spell_nats(xs, "")))
    case Cmd.Shut{}:
      Wr.put_nat(2n, "")

# a key's answer: the new line, open, submit
def cmd_spell_out(o: Cmd.Out) -> String:
  match o:
    case Cmd.Out{l, a, b}:
      Wr.put_str(cmd_text(l), Wr.put_bool(a, Wr.put_bool(b, "")))

# the spelling of the model's answer to question q about table t
def cmd_spell_answer(+t: List<&2, Cmd.Ent>, q: FCmd.Query) -> String:
  match q:
    case FCmd.QResolve{l}:
      cmd_spell_res(Cmd.resolve(t, cmd_codes(l)))
    case FCmd.QMenu{l}:
      cmd_spell_menu(Cmd.menu(t, cmd_codes(l)))
    case FCmd.QKey{l, x, k}:
      cmd_spell_out(Cmd.key(t, cmd_codes(l), x, k))

# the spelling of the model's answer to request r
def cmd_spell_reply(r: FCmd.Req) -> String:
  match r:
    case FCmd.Req{t, q}:
      cmd_spell_answer(cmd_model_table(t), q)

# the example table as Rust spells it: /memory (a default; view, model)
# and /goal (text)
def cmd_example_wire_table() -> String:
  "4,1,6,memory0,TFF2,6,memory4,view0,TTF2,6,memory5,model0,TTF1,4,goal0,TTT"

# Laws: the spelled entry
# -----------------------

# LAW command_ffi_decides: a request spelled by the grammar, whose counts,
# lengths and places fit the wire, is answered with the spelling of the
# model's answer (resolve, menu or key) about the table it carries
# EXCLUDES: an entry that answers another question, another table, a
#   changed line or name, a reply in another tag or order, a default
law command_ffi_decides:
  for +r: FCmd.Req
  for h: {cmd_req_fits(r) == True{} : Bool}
  {FCmd.ffi(cmd_spell_req(r, "")) == cmd_spell_reply(r) : String}

# LAW command_ffi_spelled_left_over: input left over after a spelled
# request is refused
# EXCLUDES: trailing input ignored, or read as part of the request
law command_ffi_spelled_left_over:
  for +r: FCmd.Req
  for +rest: String
  for h: {cmd_req_fits(r) == True{} : Bool}
  for more: {String.is_empty(rest) == False{} : Bool}
  {FCmd.ffi(cmd_spell_req(r, rest)) == Wr.err("command: input left over") : String}

# LAW command_ffi_reads_only_requests: an answer that is not the error
# form answers a request: the input is the spelling of a request that
# fits the wire, and the answer is the model's answer to it
# EXCLUDES: a decoder that accepts an unknown tag, a bad flag, a short
#   string, a count or place past the wire, or a missing field, and
#   answers it anyway (a default instead of the error form)
law command_ffi_reads_only_requests:
  for +s: String
  for ok: {LawsBase.wire_opens_err(FCmd.ffi(s)) == False{} : Bool}
  exs r: FCmd.Req
  {(s, (cmd_req_fits(r), FCmd.ffi(s))) == (cmd_spell_req(r, ""), (True{}, cmd_spell_reply(r))) : String & (Bool & String)}

# LAW command_ffi_unknown_query: after a table, a question tag past 2
# (resolve, menu, key) is malformed, whatever follows
# EXCLUDES: an unknown question answered as a resolve, a menu or a key
law command_ffi_unknown_query:
  for +t: List<&2, FCmd.EntW>
  for +n: Nat
  for +rest: String
  for h: {Bool.and(LawsBase.wire_fits(List.length(&2, FCmd.EntW, t)), cmd_ents_all(t)) == True{} : Bool}
  {FCmd.ffi(cmd_spell_table(t, Wr.put_nat(3n+n, rest))) == Wr.err("command: malformed request") : String}

# LAW command_ffi_unknown_row: in a key question, a row tag past 1 (none,
# a place) is malformed, whatever follows
# EXCLUDES: an unknown row read as no row or as a place
law command_ffi_unknown_row:
  for +t: List<&2, FCmd.EntW>
  for +l: String
  for +n: Nat
  for +rest: String
  for h: {Bool.and(LawsBase.wire_fits(List.length(&2, FCmd.EntW, t)), cmd_ents_all(t)) == True{} : Bool}
  for hl: {LawsBase.wire_fits(String.length(l)) == True{} : Bool}
  {FCmd.ffi(cmd_spell_table(t, Wr.put_nat(2n, Wr.put_str(l, Wr.put_nat(2n+n, rest))))) == Wr.err("command: malformed request") : String}

# LAW command_ffi_unknown_press: in a key question, a key tag past 1
# (Tab, Enter) is malformed, whatever follows
# EXCLUDES: an unknown key read as Tab or Enter
law command_ffi_unknown_press:
  for +t: List<&2, FCmd.EntW>
  for +l: String
  for +x: Cmd.Sel
  for +n: Nat
  for +rest: String
  for h: {Bool.and(LawsBase.wire_fits(List.length(&2, FCmd.EntW, t)), cmd_ents_all(t)) == True{} : Bool}
  for hl: {Bool.and(LawsBase.wire_fits(String.length(l)), cmd_sel_fits(x)) == True{} : Bool}
  {FCmd.ffi(cmd_spell_table(t, Wr.put_nat(2n, Wr.put_str(l, cmd_spell_sel(x, Wr.put_nat(2n+n, rest)))))) == Wr.err("command: malformed request") : String}

# LAW command_ffi_unknown_res: a resolve reply tag past 3 (runs, opens,
# unknown, no command) reads as no reply, whatever follows
# EXCLUDES: a reply grammar where an unknown tag reads as a resolution
#   (two spellings of one answer, a reply Rust and the laws read apart)
law command_ffi_unknown_res:
  for +n: Nat
  for +rest: String
  {FCmd.get_res(Wr.put_nat(4n+n, rest)) == Wr.Bad{} : Wr.Dec<FCmd.ResW>}

# LAW command_ffi_unknown_menu: a menu reply tag past 2 (names, children,
# none) reads as no reply, whatever follows
# EXCLUDES: a reply grammar where an unknown tag reads as a menu
law command_ffi_unknown_menu:
  for +n: Nat
  for +rest: String
  {FCmd.get_menu(Wr.put_nat(3n+n, rest)) == Wr.Bad{} : Wr.Dec<FCmd.MenuW>}

# LAW command_ffi_example: anchor: the exact strings Rust sends and reads
# for the example table: `memory model` runs memory model; the menu of
# `memory ` lists places 1 and 2; Tab on row 0 of `mem` completes
# `memory ` with its menu open; question tag 7, row tag 2 and key tag 5
# are malformed
law command_ffi_example:
  {[FCmd.ffi(String.concat([cmd_example_wire_table(), "0,12,memory model"])), FCmd.ffi(String.concat([cmd_example_wire_table(), "1,7,memory "])), FCmd.ffi(String.concat([cmd_example_wire_table(), "2,3,mem1,0,0,"])), FCmd.ffi(String.concat([cmd_example_wire_table(), "7,"])), FCmd.ffi(String.concat([cmd_example_wire_table(), "2,3,mem2,0,"])), FCmd.ffi(String.concat([cmd_example_wire_table(), "2,3,mem0,5,"]))] == ["0,2,6,memory5,model0,", "1,1,6,memory2,1,2,", "7,memory TF", "E command: malformed request", "E command: malformed request", "E command: malformed request"] : List<&2, String>}

# LAW command_ffi_premises_witness: witness: requests and replies that
# fit exist, and so does a malformed input
# EXCLUDES: a vacuous entry law whose premise no request meets
law command_ffi_premises_witness:
  {Bool.and(cmd_req_fits(FCmd.Req{[], FCmd.QResolve{""}}), Bool.and(cmd_res_fits(FCmd.NoCmdW{}), Bool.and(cmd_menu_fits(FCmd.NamesW{}), cmd_out_fits(FCmd.OutW{"", True{}, True{}})))) == True{} : Bool} & {FCmd.get_req("") == Wr.Bad{} : Wr.Dec<FCmd.Req>}
