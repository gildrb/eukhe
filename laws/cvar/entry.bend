# eukhe: the laws of area cvar: the compiled entry

import Base
import ../../bend/cvar.bend as Cv
import ../../bend/ffi_cvar.bend as FCv
import ../../bend/wire.bend as Wr
import ../base.bend as LawsBase

# ---- cvar_entry ----

# LAWS (S4, the compiled core): the entries of bend/ffi_cvar.bend run the
# expansion and the key presses for the Rust code. Each law is an open
# claim about those entries; PROOF.bend proves them (as Cvar.<law>) with
# the lemmas of proof/cvar/.

# The entries of the compiled core (bend/ffi_cvar.bend)
# ------------------------------------------------------
# The Rust code (crates/eukhe-bend/src/rules/cvar.rs) numbers the aliases
# and the keys, and keeps every command that is not a run aside: such a
# command crosses as CToggle{its place} (the model passes it through
# unchanged: alias_runs_body, alias_expands_in_order).

# the numbers of a value fit the wire
def cvar_val_fits(v: Cv.Val) -> Bool:
  match v:
    case Cv.VNat{n}:
      LawsBase.wire_fits(n)
    case Cv.VBool{b}:
      True{}

# the numbers of a command fit the wire
def cvar_cmd_fits(c: Cv.Cmd) -> Bool:
  match c:
    case Cv.CSet{i, v}:
      Bool.and(LawsBase.wire_fits(i), cvar_val_fits(v))
    case Cv.CToggle{i}:
      LawsBase.wire_fits(i)
    case Cv.CRun{n}:
      LawsBase.wire_fits(n)
    case Cv.CGone{n}:
      LawsBase.wire_fits(n)

# every item of xs fits the wire
def cvar_cmds_all(xs: List<&2, Cv.Cmd>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{+x, t}:
      Bool.and(cvar_cmd_fits(x), cvar_cmds_all(t))

# a command list fits the wire
def cvar_cmds_fit(+cs: List<&2, Cv.Cmd>) -> Bool:
  Bool.and(LawsBase.wire_fits(List.length(&2, Cv.Cmd, cs)), cvar_cmds_all(cs))

# an alias fits the wire
def cvar_alias_fits(a: Cv.Alias) -> Bool:
  match a:
    case Cv.Alias{n, b}:
      Bool.and(LawsBase.wire_fits(n), cvar_cmds_fit(b))

# every item of xs fits the wire
def cvar_aliases_all(xs: List<&2, Cv.Alias>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{+x, t}:
      Bool.and(cvar_alias_fits(x), cvar_aliases_all(t))

# a key bind fits the wire
def cvar_bind_fits(k: Cv.KeyBind) -> Bool:
  match k:
    case Cv.KeyBind{n, c}:
      Bool.and(LawsBase.wire_fits(n), cvar_cmds_fit(c))

# every item of xs fits the wire
def cvar_binds_all(xs: List<&2, Cv.KeyBind>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{+x, t}:
      Bool.and(cvar_bind_fits(x), cvar_binds_all(t))

# an alias table fits the wire
def cvar_aliases_fit(+as: List<&2, Cv.Alias>) -> Bool:
  Bool.and(LawsBase.wire_fits(List.length(&2, Cv.Alias, as)), cvar_aliases_all(as))

# a bind table fits the wire
def cvar_binds_fit(+bs: List<&2, Cv.KeyBind>) -> Bool:
  Bool.and(LawsBase.wire_fits(List.length(&2, Cv.KeyBind, bs)), cvar_binds_all(bs))

# LAW cvar_ffi_round_trip: an expand request that fits reads back whole
# EXCLUDES: an alias, a command or a number lost, swapped or misread on
#   the way to the model
law cvar_ffi_round_trip:
  for +as: List<&2, Cv.Alias>
  for +cs: List<&2, Cv.Cmd>
  for +rest: String
  for h: {Bool.and(cvar_aliases_fit(as), cvar_cmds_fit(cs)) == True{} : Bool}
  {FCv.get_xreq(FCv.put_xreq(FCv.Xreq{as, cs}, rest)) == Wr.Got{FCv.Xreq{as, cs}, rest} : Wr.Dec<FCv.Xreq>}

# LAW cvar_ffi_is_expand: the expand entry answers the model's expansion
# EXCLUDES: an entry that expands by any other rule, or answers a default
law cvar_ffi_is_expand:
  for +as: List<&2, Cv.Alias>
  for +cs: List<&2, Cv.Cmd>
  for h: {Bool.and(cvar_aliases_fit(as), cvar_cmds_fit(cs)) == True{} : Bool}
  {FCv.ffi(FCv.put_xreq(FCv.Xreq{as, cs}, "")) == FCv.put_exp(Cv.expand(cs, as), "") : String}

# LAW cvar_ffi_malformed: a malformed expand request answers the error form
# EXCLUDES: a default expansion (nothing to run) for bad input
law cvar_ffi_malformed:
  for +s: String
  for h: {FCv.get_xreq(s) == Wr.Bad{} : Wr.Dec<FCv.Xreq>}
  {FCv.ffi(s) == Wr.err("cvar: malformed expand request") : String}

# LAW cvar_ffi_open: a bind table that fits opens the press state of that table
# EXCLUDES: a table read with a bind or an alias lost or changed
law cvar_ffi_open:
  for +bs: List<&2, Cv.KeyBind>
  for +as: List<&2, Cv.Alias>
  for h: {Bool.and(cvar_binds_fit(bs), cvar_aliases_fit(as)) == True{} : Bool}
  {FCv.open(FCv.put_table(bs, as, "")) == (FCv.Table{bs, as}, "") : FCv.St & String}

# LAW cvar_ffi_open_malformed: a malformed bind table opens the refused state, with the error form
# EXCLUDES: an empty table (every key unbound) for bad input
law cvar_ffi_open_malformed:
  for +s: String
  for h: {FCv.get_table(s) == Wr.Bad{} : Wr.Dec<FCv.St>}
  {FCv.open(s) == (FCv.Refused{}, Wr.err("cvar: malformed press table")) : FCv.St & String}

# LAW cvar_ffi_press: a press of a key answers the model's press, and the table stays
# EXCLUDES: a press by any other rule, a table that changes between
#   presses
law cvar_ffi_press:
  for +bs: List<&2, Cv.KeyBind>
  for +as: List<&2, Cv.Alias>
  for +k: Nat
  for h: {LawsBase.wire_fits(k) == True{} : Bool}
  {FCv.step(FCv.Table{bs, as}, Wr.put_nat(k, "")) == (FCv.Table{bs, as}, FCv.put_exp(Cv.press(bs, k, as), "")) : FCv.St & String}

# LAW cvar_ffi_refused: a refused table answers every press with the error form
# EXCLUDES: a press that runs anything after a refused open
law cvar_ffi_refused:
  for +s: String
  {FCv.step(FCv.Refused{}, s) == (FCv.Refused{}, Wr.err("cvar: the press table was refused")) : FCv.St & String}

# LAW cvar_fits_example: witness: a table and a command list fit
law cvar_fits_example:
  {Bool.and(cvar_binds_fit([Cv.KeyBind{0n, [Cv.CRun{1n}, Cv.CToggle{0n}]}]), Bool.and(cvar_aliases_fit([Cv.Alias{1n, [Cv.CSet{2n, Cv.VBool{True{}}}, Cv.CGone{3n}]}]), cvar_cmds_fit([Cv.CSet{0n, Cv.VNat{7n}}]))) == True{} : Bool}

# The bytes of the entries, spelled
# ---------------------------------
# The grammar Rust writes and reads (crates/eukhe-bend/src/rules/cvar.rs),
# spelled from the wire primitives only, never the entry's put_*/get_*:
# Val = 0 n | 1 b; Cmd = 0 i Val | 1 i | 2 n | 3 n; a list is its count,
# then its items; Alias = name, body; KeyBind = key, commands; Exp = 0
# commands (Flat) | 1 n (Cycle) | 2 n (Unknown). An expand request is the
# aliases, then the commands; a press table the binds, then the aliases;
# a press the key.

def cvar_spell_val(v: Cv.Val, rest: String) -> String:
  match v:
    case Cv.VNat{n}:
      Wr.put_nat(0n, Wr.put_nat(n, rest))
    case Cv.VBool{b}:
      Wr.put_nat(1n, Wr.put_bool(b, rest))

def cvar_spell_cmd(c: Cv.Cmd, rest: String) -> String:
  match c:
    case Cv.CSet{i, v}:
      Wr.put_nat(0n, Wr.put_nat(i, cvar_spell_val(v, rest)))
    case Cv.CToggle{i}:
      Wr.put_nat(1n, Wr.put_nat(i, rest))
    case Cv.CRun{n}:
      Wr.put_nat(2n, Wr.put_nat(n, rest))
    case Cv.CGone{n}:
      Wr.put_nat(3n, Wr.put_nat(n, rest))

def cvar_spell_cmds.items(cs: List<&2, Cv.Cmd>, rest: String) -> String:
  match cs:
    case Nil{}:
      rest
    case Con{c, t}:
      cvar_spell_cmd(c, cvar_spell_cmds.items(t, rest))

def cvar_spell_cmds(+cs: List<&2, Cv.Cmd>, rest: String) -> String:
  Wr.put_nat(List.length(&2, Cv.Cmd, cs), cvar_spell_cmds.items(cs, rest))

def cvar_spell_alias(a: Cv.Alias, rest: String) -> String:
  match a:
    case Cv.Alias{n, b}:
      Wr.put_nat(n, cvar_spell_cmds(b, rest))

def cvar_spell_aliases.items(xs: List<&2, Cv.Alias>, rest: String) -> String:
  match xs:
    case Nil{}:
      rest
    case Con{x, t}:
      cvar_spell_alias(x, cvar_spell_aliases.items(t, rest))

def cvar_spell_aliases(+xs: List<&2, Cv.Alias>, rest: String) -> String:
  Wr.put_nat(List.length(&2, Cv.Alias, xs), cvar_spell_aliases.items(xs, rest))

def cvar_spell_bind(k: Cv.KeyBind, rest: String) -> String:
  match k:
    case Cv.KeyBind{n, c}:
      Wr.put_nat(n, cvar_spell_cmds(c, rest))

def cvar_spell_binds.items(xs: List<&2, Cv.KeyBind>, rest: String) -> String:
  match xs:
    case Nil{}:
      rest
    case Con{x, t}:
      cvar_spell_bind(x, cvar_spell_binds.items(t, rest))

def cvar_spell_binds(+xs: List<&2, Cv.KeyBind>, rest: String) -> String:
  Wr.put_nat(List.length(&2, Cv.KeyBind, xs), cvar_spell_binds.items(xs, rest))

def cvar_spell_exp(e: Cv.Exp, rest: String) -> String:
  match e:
    case Cv.Flat{cs}:
      Wr.put_nat(0n, cvar_spell_cmds(cs, rest))
    case Cv.Cycle{n}:
      Wr.put_nat(1n, Wr.put_nat(n, rest))
    case Cv.Unknown{n}:
      Wr.put_nat(2n, Wr.put_nat(n, rest))

# the state of a stepper's answer
def cvar_st_of(r: FCv.St & String) -> FCv.St:
  match r:
    case (st, a):
      st

# the reply of a stepper's answer
def cvar_reply_of(r: FCv.St & String) -> String:
  match r:
    case (st, a):
      a

def cvar_refused_with.at(st: FCv.St, a: String, text: String) -> Bool:
  match st:
    case FCv.Table{bs, as}:
      False{}
    case FCv.Refused{}:
      String.eq(a, Wr.err(text))

# the answer is the refused state with the error form of text
def cvar_refused_with(r: FCv.St & String, text: String) -> Bool:
  match r:
    case (st, a):
      cvar_refused_with.at(st, a, text)

# LAW cvar_ffi_answers_spelled: an expand request spelled by the grammar, every number within
# the wire, answers the spelled expansion of the model (Cv.expand)
# EXCLUDES: a command, value or expansion tag or a field order that drifts
#   from Rust's grammar on both sides of the entry alike, a field lost or
#   swapped, a reversed Bool, an expansion by another rule
law cvar_ffi_answers_spelled:
  for +as: List<&2, Cv.Alias>
  for +cs: List<&2, Cv.Cmd>
  for fits: {Bool.and(cvar_aliases_fit(as), cvar_cmds_fit(cs)) == True{} : Bool}
  {FCv.ffi(cvar_spell_aliases(as, cvar_spell_cmds(cs, ""))) == cvar_spell_exp(Cv.expand(cs, as), "") : String}

# LAW cvar_ffi_left_over_spelled: a spelled expand request that fits, then any more input,
# answers the error form "cvar: input left over"
# EXCLUDES: trailing input ignored or read as part of the request, another error text
law cvar_ffi_left_over_spelled:
  for +as: List<&2, Cv.Alias>
  for +cs: List<&2, Cv.Cmd>
  for fits: {Bool.and(cvar_aliases_fit(as), cvar_cmds_fit(cs)) == True{} : Bool}
  for +c: Char
  for +t: String
  {FCv.ffi(cvar_spell_aliases(as, cvar_spell_cmds(cs, SCon{c, t}))) == Wr.err("cvar: input left over") : String}

# LAW cvar_ffi_reads_only_requests: an expand answer that is not the error form answers a
# request: the input is exactly a spelled request that fits, the answer its spelled expansion
# EXCLUDES: a decoder that accepts an unknown tag, a missing or extra field
#   or item, a number past the wire or input left over, and answers it anyway
law cvar_ffi_reads_only_requests:
  for +s: String
  for ok: {LawsBase.wire_opens_err(FCv.ffi(s)) == False{} : Bool}
  exs as: List<&2, Cv.Alias>
  exs cs: List<&2, Cv.Cmd>
  {(s, (Bool.and(cvar_aliases_fit(as), cvar_cmds_fit(cs)), FCv.ffi(s))) == (cvar_spell_aliases(as, cvar_spell_cmds(cs, "")), (True{}, cvar_spell_exp(Cv.expand(cs, as), ""))) : String & (Bool & String)}

# LAW cvar_ffi_malformed_unless_request: every expand answer but the error form "cvar:
# malformed expand request" comes from an input that begins with a spelled request that fits
# EXCLUDES: the left-over error or an expansion for input that holds no
#   request (an unknown tag, a short list, a number past the wire), the
#   malformed error spelled with another text
law cvar_ffi_malformed_unless_request:
  for +s: String
  for other: {String.eq(FCv.ffi(s), Wr.err("cvar: malformed expand request")) == False{} : Bool}
  exs as: List<&2, Cv.Alias>
  exs cs: List<&2, Cv.Cmd>
  exs rest: String
  {(s, Bool.and(cvar_aliases_fit(as), cvar_cmds_fit(cs))) == (cvar_spell_aliases(as, cvar_spell_cmds(cs, rest)), True{}) : String & Bool}

# LAW cvar_open_answers_spelled: a press table spelled by the grammar, every number within the
# wire, opens the press state of exactly that table, with the empty reply
# EXCLUDES: a bind or alias lost, swapped or misread under a tag or field
#   order both sides of the entry share, a refused good table
law cvar_open_answers_spelled:
  for +bs: List<&2, Cv.KeyBind>
  for +as: List<&2, Cv.Alias>
  for fits: {Bool.and(cvar_binds_fit(bs), cvar_aliases_fit(as)) == True{} : Bool}
  {FCv.open(cvar_spell_binds(bs, cvar_spell_aliases(as, ""))) == (FCv.Table{bs, as}, "") : FCv.St & String}

# LAW cvar_open_left_over_spelled: a spelled press table that fits, then any more input, opens
# the refused state with the error form "cvar: input left over"
# EXCLUDES: trailing input ignored, a table opened from it, another error text
law cvar_open_left_over_spelled:
  for +bs: List<&2, Cv.KeyBind>
  for +as: List<&2, Cv.Alias>
  for fits: {Bool.and(cvar_binds_fit(bs), cvar_aliases_fit(as)) == True{} : Bool}
  for +c: Char
  for +t: String
  {FCv.open(cvar_spell_binds(bs, cvar_spell_aliases(as, SCon{c, t}))) == (FCv.Refused{}, Wr.err("cvar: input left over")) : FCv.St & String}

# LAW cvar_open_reads_only_tables: an open whose reply is not the error form read exactly a
# spelled table that fits, and opens its press state with the empty reply
# EXCLUDES: a table opened from an unknown tag, a short list, a number past
#   the wire or input left over
law cvar_open_reads_only_tables:
  for +s: String
  for ok: {LawsBase.wire_opens_err(cvar_reply_of(FCv.open(s))) == False{} : Bool}
  exs bs: List<&2, Cv.KeyBind>
  exs as: List<&2, Cv.Alias>
  {(s, (Bool.and(cvar_binds_fit(bs), cvar_aliases_fit(as)), FCv.open(s))) == (cvar_spell_binds(bs, cvar_spell_aliases(as, "")), (True{}, (FCv.Table{bs, as}, ""))) : String & (Bool & (FCv.St & String))}

# LAW cvar_open_malformed_unless_table: every open but the refused state with the error form
# "cvar: malformed press table" reads an input that begins with a spelled table that fits
# EXCLUDES: a table (or the left-over error) for input that holds no table,
#   a malformed table that opens anything but the refused state, the
#   malformed error spelled with another text
law cvar_open_malformed_unless_table:
  for +s: String
  for other: {cvar_refused_with(FCv.open(s), "cvar: malformed press table") == False{} : Bool}
  exs bs: List<&2, Cv.KeyBind>
  exs as: List<&2, Cv.Alias>
  exs rest: String
  {(s, Bool.and(cvar_binds_fit(bs), cvar_aliases_fit(as))) == (cvar_spell_binds(bs, cvar_spell_aliases(as, rest)), True{}) : String & Bool}

# LAW cvar_step_answers_spelled: a press of a key spelled on the wire, within it, answers the
# spelled expansion of the model's press (Cv.press) on the table, and the table stays
# EXCLUDES: an expansion tag that drifts from Rust's grammar on both sides,
#   a press by another rule, a table that changes between presses
law cvar_step_answers_spelled:
  for +bs: List<&2, Cv.KeyBind>
  for +as: List<&2, Cv.Alias>
  for +k: Nat
  for fits: {LawsBase.wire_fits(k) == True{} : Bool}
  {FCv.step(FCv.Table{bs, as}, Wr.put_nat(k, "")) == (FCv.Table{bs, as}, cvar_spell_exp(Cv.press(bs, k, as), "")) : FCv.St & String}

# LAW cvar_step_left_over_spelled: a spelled key that fits, then any more input, answers the
# error form "cvar: input left over", and the table stays
# EXCLUDES: trailing input ignored or read as part of the key, another error text
law cvar_step_left_over_spelled:
  for +bs: List<&2, Cv.KeyBind>
  for +as: List<&2, Cv.Alias>
  for +k: Nat
  for fits: {LawsBase.wire_fits(k) == True{} : Bool}
  for +c: Char
  for +t: String
  {FCv.step(FCv.Table{bs, as}, Wr.put_nat(k, SCon{c, t})) == (FCv.Table{bs, as}, Wr.err("cvar: input left over")) : FCv.St & String}

# LAW cvar_step_keeps_table: a press of any input, malformed or not, leaves the table as it was
# EXCLUDES: a malformed press that drops, refuses or changes the table
law cvar_step_keeps_table:
  for +bs: List<&2, Cv.KeyBind>
  for +as: List<&2, Cv.Alias>
  for +s: String
  {cvar_st_of(FCv.step(FCv.Table{bs, as}, s)) == FCv.Table{bs, as} : FCv.St}

# LAW cvar_step_reads_only_keys: a press reply that is not the error form answers exactly a
# spelled key within the wire, with the spelled expansion of its press
# EXCLUDES: a key read with leading zeros, past the wire or with input left
#   over, and answered anyway
law cvar_step_reads_only_keys:
  for +bs: List<&2, Cv.KeyBind>
  for +as: List<&2, Cv.Alias>
  for +s: String
  for ok: {LawsBase.wire_opens_err(cvar_reply_of(FCv.step(FCv.Table{bs, as}, s))) == False{} : Bool}
  exs k: Nat
  {(s, (LawsBase.wire_fits(k), cvar_reply_of(FCv.step(FCv.Table{bs, as}, s)))) == (Wr.put_nat(k, ""), (True{}, cvar_spell_exp(Cv.press(bs, k, as), ""))) : String & (Bool & String)}

# LAW cvar_step_malformed_unless_key: every press reply but the error form "cvar: malformed
# key" reads an input that begins with a spelled key within the wire
# EXCLUDES: the left-over error or an expansion for input that holds no
#   key, the malformed error spelled with another text
law cvar_step_malformed_unless_key:
  for +bs: List<&2, Cv.KeyBind>
  for +as: List<&2, Cv.Alias>
  for +s: String
  for other: {String.eq(cvar_reply_of(FCv.step(FCv.Table{bs, as}, s)), Wr.err("cvar: malformed key")) == False{} : Bool}
  exs k: Nat
  exs rest: String
  {(s, LawsBase.wire_fits(k)) == (Wr.put_nat(k, rest), True{}) : String & Bool}

# LAW cvar_tags_example: anchor: the bytes Rust sends and reads: alias 0 = [toggle 3], then
# [toggle 0, run 0] is flat [toggle 0, toggle 3]; alias 0 = [run 0] run is a cycle at 0; a run
# of a missing alias and a gone command name it; sets of a Bool and a Nat pass through; a
# command tag 4, a value tag 2, input left over are refused. The table key 0 = [run 0], alias 0
# = [toggle 1] opens with the empty reply; key 0 runs toggle 1, key 1 nothing; a key with
# input left over, a key that is no number, a short or left-over table, a press after a
# refused open get their error forms
# EXCLUDES: a tag table both sides of the Bend entry agree on but Rust does
#   not, an unknown tag read as a known one, an error text swapped
law cvar_tags_example:
  {[FCv.ffi("1,0,1,1,3,2,1,0,2,0,"), FCv.ffi("1,0,1,2,0,1,2,0,"), FCv.ffi("0,1,2,0,"), FCv.ffi("0,1,3,5,"), FCv.ffi("0,2,0,4,1,T0,9,0,7,"), FCv.ffi("0,1,4,0,"), FCv.ffi("0,1,0,4,2,0,"), FCv.ffi("0,0,x")] == ["0,2,1,0,1,3,", "1,0,", "2,0,", "2,5,", "0,2,0,4,1,T0,9,0,7,", Wr.err("cvar: malformed expand request"), Wr.err("cvar: malformed expand request"), Wr.err("cvar: input left over")] : List<&2, String>} &
  {FCv.open("1,0,1,2,0,1,0,1,1,1,") == (FCv.Table{[Cv.KeyBind{0n, [Cv.CRun{0n}]}], [Cv.Alias{0n, [Cv.CToggle{1n}]}]}, "") : FCv.St & String} &
  {[cvar_reply_of(FCv.step(cvar_st_of(FCv.open("1,0,1,2,0,1,0,1,1,1,")), "0,")), cvar_reply_of(FCv.step(cvar_st_of(FCv.open("1,0,1,2,0,1,0,1,1,1,")), "1,")), cvar_reply_of(FCv.step(cvar_st_of(FCv.open("1,0,1,2,0,1,0,1,1,1,")), "0,x")), cvar_reply_of(FCv.step(cvar_st_of(FCv.open("1,0,1,2,0,1,0,1,1,1,")), "x")), cvar_reply_of(FCv.open("1,")), cvar_reply_of(FCv.open("1,0,1,2,0,1,0,1,1,1,x")), cvar_reply_of(FCv.step(cvar_st_of(FCv.open("1,")), "0,"))] == ["0,1,1,1,", "0,0,", Wr.err("cvar: input left over"), Wr.err("cvar: malformed key"), Wr.err("cvar: malformed press table"), Wr.err("cvar: input left over"), Wr.err("cvar: the press table was refused")] : List<&2, String>}
