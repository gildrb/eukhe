# eukhe: the laws of area cvar_entry

import Base
import ../bend/cvar.bend as Cv
import ../bend/ffi_cvar.bend as FCv
import ../bend/wire.bend as Wr
import ./base.bend as LawsBase
import ./cvar/entry.bend as Cvar

# ---- cvar_entry ----

# LAWS (S4, the compiled core): the entries of bend/ffi_cvar.bend, whole.
# The call `expand` and the stepper `press` (open, then one key per step)
# answer every input as these spec helpers say: the requests and replies
# of the grammar (the header of bend/ffi_cvar.bend, crates/eukhe-bend/
# WIRE.md) spelled and read with the wire primitives of bend/wire.bend and
# these helpers alone, never with the entry's own encoders or decoders,
# and the decisions by the spec of laws/cvar/entry.bend (spec_expand,
# spec_press: alias_expand_exact, bind_press_exact). With cvar_ffi_exact,
# cvar_open_exact and cvar_step_exact (and cvar_ffi_refused for a refused
# table), every answer and every state of the entries follows from the
# spec: a reply that is no error is the spec's decision on the request the
# input spells; every error is one of the entry's fixed texts.
# Every input is free: any text, any table.

# Spellings
# ---------

def cvs_spell_val(v: Cv.Val, rest: String) -> String:
  match v:
    case Cv.VNat{n}:
      Wr.put_nat(0n, Wr.put_nat(n, rest))
    case Cv.VBool{b}:
      Wr.put_nat(1n, Wr.put_bool(b, rest))

def cvs_spell_cmd(c: Cv.Cmd, rest: String) -> String:
  match c:
    case Cv.CSet{i, v}:
      Wr.put_nat(0n, Wr.put_nat(i, cvs_spell_val(v, rest)))
    case Cv.CToggle{i}:
      Wr.put_nat(1n, Wr.put_nat(i, rest))
    case Cv.CRun{n}:
      Wr.put_nat(2n, Wr.put_nat(n, rest))
    case Cv.CGone{n}:
      Wr.put_nat(3n, Wr.put_nat(n, rest))

# an expansion: 0 the commands | 1 a cycle's alias | 2 an unknown alias
def cvs_spell_exp(e: Cv.Exp, rest: String) -> String:
  match e:
    case Cv.Flat{cs}:
      Wr.put_nat(0n, Wr.put_list(~Cv.Cmd, ~cvs_spell_cmd, cs, rest))
    case Cv.Cycle{n}:
      Wr.put_nat(1n, Wr.put_nat(n, rest))
    case Cv.Unknown{n}:
      Wr.put_nat(2n, Wr.put_nat(n, rest))

def cvs_expand.run(q: FCv.Xreq) -> String:
  match q:
    case FCv.Xreq{as, cs}:
      cvs_spell_exp(Cvar.spec_expand(cs, as), "")

def cvs_expand.end(done: Bool, q: FCv.Xreq) -> String:
  match done:
    case True{}:
      cvs_expand.run(q)
    case False{}:
      Wr.err("cvar: input left over")

def cvs_expand.go(d: Wr.Dec<FCv.Xreq>) -> String:
  match d:
    case Wr.Got{q, s}:
      cvs_expand.end(Wr.end(s), q)
    case Wr.Bad{}:
      Wr.err("cvar: malformed expand request")

def cvs_read_alias.body(n: Nat, d: Wr.Dec<List<&2, Cv.Cmd>>) -> Wr.Dec<Cv.Alias>:
  match d:
    case Wr.Got{b, s}:
      Wr.Got{Cv.Alias{n, b}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def cvs_read_gone(d: Wr.Dec<Nat>) -> Wr.Dec<Cv.Cmd>:
  match d:
    case Wr.Got{n, s}:
      Wr.Got{Cv.CGone{n}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def cvs_read_run(d: Wr.Dec<Nat>) -> Wr.Dec<Cv.Cmd>:
  match d:
    case Wr.Got{n, s}:
      Wr.Got{Cv.CRun{n}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def cvs_read_set.v(i: Nat, d: Wr.Dec<Cv.Val>) -> Wr.Dec<Cv.Cmd>:
  match d:
    case Wr.Got{v, s}:
      Wr.Got{Cv.CSet{i, v}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def cvs_read_val.bool(d: Wr.Dec<Bool>) -> Wr.Dec<Cv.Val>:
  match d:
    case Wr.Got{b, s}:
      Wr.Got{Cv.VBool{b}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def cvs_read_val.nat(d: Wr.Dec<Nat>) -> Wr.Dec<Cv.Val>:
  match d:
    case Wr.Got{n, s}:
      Wr.Got{Cv.VNat{n}, s}
    case Wr.Bad{}:
      Wr.Bad{}

# tags: 0 a Nat, 1 a Bool
def cvs_read_val.tag(t: Nat, s: String) -> Wr.Dec<Cv.Val>:
  match t:
    case 0n:
      cvs_read_val.nat(Wr.get_nat(s))
    case 1n:
      cvs_read_val.bool(Wr.get_bool(s))
    case 2n+x:
      Wr.Bad{}

def cvs_read_val.go(d: Wr.Dec<Nat>) -> Wr.Dec<Cv.Val>:
  match d:
    case Wr.Got{t, s}:
      cvs_read_val.tag(t, s)
    case Wr.Bad{}:
      Wr.Bad{}

def cvs_read_set(d: Wr.Dec<Nat>) -> Wr.Dec<Cv.Cmd>:
  match d:
    case Wr.Got{i, s}:
      cvs_read_set.v(i, cvs_read_val.go(Wr.get_nat(s)))
    case Wr.Bad{}:
      Wr.Bad{}

def cvs_read_toggle(d: Wr.Dec<Nat>) -> Wr.Dec<Cv.Cmd>:
  match d:
    case Wr.Got{i, s}:
      Wr.Got{Cv.CToggle{i}, s}
    case Wr.Bad{}:
      Wr.Bad{}

# tags: 0 a set, 1 a toggle (any command that runs no alias), 2 a run,
# 3 a run of a missing alias
def cvs_read_cmd.tag(t: Nat, s: String) -> Wr.Dec<Cv.Cmd>:
  match t:
    case 0n:
      cvs_read_set(Wr.get_nat(s))
    case 1n:
      cvs_read_toggle(Wr.get_nat(s))
    case 2n:
      cvs_read_run(Wr.get_nat(s))
    case 3n:
      cvs_read_gone(Wr.get_nat(s))
    case 4n+x:
      Wr.Bad{}

def cvs_read_cmd.go(d: Wr.Dec<Nat>) -> Wr.Dec<Cv.Cmd>:
  match d:
    case Wr.Got{t, s}:
      cvs_read_cmd.tag(t, s)
    case Wr.Bad{}:
      Wr.Bad{}

def cvs_read_cmd(s: String) -> Wr.Dec<Cv.Cmd>:
  cvs_read_cmd.go(Wr.get_nat(s))

def cvs_read_alias.name(d: Wr.Dec<Nat>) -> Wr.Dec<Cv.Alias>:
  match d:
    case Wr.Got{n, s}:
      cvs_read_alias.body(n, Wr.get_list(~Cv.Cmd, ~cvs_read_cmd, s))
    case Wr.Bad{}:
      Wr.Bad{}

# an alias: its number, then its body
def cvs_read_alias(s: String) -> Wr.Dec<Cv.Alias>:
  cvs_read_alias.name(Wr.get_nat(s))

def cvs_read_xreq.cmds(as: List<&2, Cv.Alias>, d: Wr.Dec<List<&2, Cv.Cmd>>) -> Wr.Dec<FCv.Xreq>:
  match d:
    case Wr.Got{cs, s}:
      Wr.Got{FCv.Xreq{as, cs}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def cvs_read_xreq.aliases(d: Wr.Dec<List<&2, Cv.Alias>>) -> Wr.Dec<FCv.Xreq>:
  match d:
    case Wr.Got{as, s}:
      cvs_read_xreq.cmds(as, Wr.get_list(~Cv.Cmd, ~cvs_read_cmd, s))
    case Wr.Bad{}:
      Wr.Bad{}

# the expand request at the start of s: the aliases, then the commands
def cvs_read_xreq(s: String) -> Wr.Dec<FCv.Xreq>:
  cvs_read_xreq.aliases(Wr.get_list(~Cv.Alias, ~cvs_read_alias, s))

# the call's answer to s: the spelled expansion of the request s is, when
# nothing is left after it; else one of the two error texts
def cvs_expand(s: String) -> String:
  cvs_expand.go(cvs_read_xreq(s))

# LAW cvar_ffi_exact: on every input the expand call answers the spec: the spec's expansion, spelled, of the request the input spells (read by the spec's reader with the wire primitives) when nothing is left after it; `E cvar: input left over` when input is left; `E cvar: malformed expand request` for any other input
# EXCLUDES: an answer for an input that spells no request, a request read
#   otherwise than the grammar spells it, an expansion other than the
#   spec's, a reply spelled otherwise, an error text that varies
law cvar_ffi_exact:
  for +s: String
  {FCv.ffi(s) == cvs_expand(s) : String}

def cvs_open.end(done: Bool, t: FCv.St) -> FCv.St & String:
  match done:
    case True{}:
      (t, "")
    case False{}:
      (FCv.Refused{}, Wr.err("cvar: input left over"))

def cvs_open.go(d: Wr.Dec<FCv.St>) -> FCv.St & String:
  match d:
    case Wr.Got{t, s}:
      cvs_open.end(Wr.end(s), t)
    case Wr.Bad{}:
      (FCv.Refused{}, Wr.err("cvar: malformed press table"))

def cvs_read_bind.cmds(n: Nat, d: Wr.Dec<List<&2, Cv.Cmd>>) -> Wr.Dec<Cv.KeyBind>:
  match d:
    case Wr.Got{c, s}:
      Wr.Got{Cv.KeyBind{n, c}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def cvs_read_bind.key(d: Wr.Dec<Nat>) -> Wr.Dec<Cv.KeyBind>:
  match d:
    case Wr.Got{n, s}:
      cvs_read_bind.cmds(n, Wr.get_list(~Cv.Cmd, ~cvs_read_cmd, s))
    case Wr.Bad{}:
      Wr.Bad{}

# a bind: its key, then its commands
def cvs_read_bind(s: String) -> Wr.Dec<Cv.KeyBind>:
  cvs_read_bind.key(Wr.get_nat(s))

def cvs_read_table.aliases(bs: List<&2, Cv.KeyBind>, d: Wr.Dec<List<&2, Cv.Alias>>) -> Wr.Dec<FCv.St>:
  match d:
    case Wr.Got{as, s}:
      Wr.Got{FCv.Table{bs, as}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def cvs_read_table.binds(d: Wr.Dec<List<&2, Cv.KeyBind>>) -> Wr.Dec<FCv.St>:
  match d:
    case Wr.Got{bs, s}:
      cvs_read_table.aliases(bs, Wr.get_list(~Cv.Alias, ~cvs_read_alias, s))
    case Wr.Bad{}:
      Wr.Bad{}

# the press table at the start of s: the binds, then the aliases
def cvs_read_table(s: String) -> Wr.Dec<FCv.St>:
  cvs_read_table.binds(Wr.get_list(~Cv.KeyBind, ~cvs_read_bind, s))

# an open: the table s is with an empty reply, when nothing is left after
# it; else the refused state, with one of the two error texts
def cvs_open(s: String) -> FCv.St & String:
  cvs_open.go(cvs_read_table(s))

def cvs_spell_alias(a: Cv.Alias, rest: String) -> String:
  match a:
    case Cv.Alias{n, b}:
      Wr.put_nat(n, Wr.put_list(~Cv.Cmd, ~cvs_spell_cmd, b, rest))

def cvs_spell_bind(k: Cv.KeyBind, rest: String) -> String:
  match k:
    case Cv.KeyBind{n, c}:
      Wr.put_nat(n, Wr.put_list(~Cv.Cmd, ~cvs_spell_cmd, c, rest))

# the press table Rust opens: the binds, then the aliases
def cvs_spell_table(bs: List<&2, Cv.KeyBind>, as: List<&2, Cv.Alias>, rest: String) -> String:
  Wr.put_list(~Cv.KeyBind, ~cvs_spell_bind, bs, Wr.put_list(~Cv.Alias, ~cvs_spell_alias, as, rest))

# the expand request Rust writes: the aliases, then the commands
def cvs_spell_xreq(as: List<&2, Cv.Alias>, cs: List<&2, Cv.Cmd>, rest: String) -> String:
  Wr.put_list(~Cv.Alias, ~cvs_spell_alias, as, Wr.put_list(~Cv.Cmd, ~cvs_spell_cmd, cs, rest))

def cvs_step.go(+bs: List<&2, Cv.KeyBind>, +as: List<&2, Cv.Alias>, d: Wr.Dec<Nat>) -> FCv.St & String:
  match d:
    case Wr.Got{k, s}:
      match s:
        case SNil{}:
          (FCv.Table{bs, as}, cvs_spell_exp(Cvar.spec_press(bs, k, as), ""))
        case SCon{c, t}:
          (FCv.Table{bs, as}, Wr.err("cvar: input left over"))
    case Wr.Bad{}:
      (FCv.Table{bs, as}, Wr.err("cvar: malformed key"))

# a step of the table (bs, as): the table stays; the reply is the spelled
# press of the key s is, when nothing is left after it, else an error text
def cvs_step(+bs: List<&2, Cv.KeyBind>, +as: List<&2, Cv.Alias>, s: String) -> FCv.St & String:
  cvs_step.go(bs, as, Wr.get_nat(s))

# LAW cvar_step_exact: on every input a step of an opened table keeps the table and answers the spec: the spec's press, spelled, of the key the input spells when nothing is left after it; `E cvar: input left over` when input is left; `E cvar: malformed key` for any other input
# EXCLUDES: a table that changes between presses, a press by another rule,
#   a key read otherwise, a press of input that spells no key
law cvar_step_exact:
  for +bs: List<&2, Cv.KeyBind>
  for +as: List<&2, Cv.Alias>
  for +s: String
  {FCv.step(FCv.Table{bs, as}, s) == cvs_step(bs, as, s) : FCv.St & String}

# LAW cvar_ffi_spelled: every expand request Rust writes whose numbers fit the wire, spelled by the spec, gets the spec's expansion
# EXCLUDES: a request Rust writes refused or answered for another request
law cvar_ffi_spelled:
  for +as: List<&2, Cv.Alias>
  for +cs: List<&2, Cv.Cmd>
  for h: {Bool.and(Cvar.cvar_aliases_fit(as), Cvar.cvar_cmds_fit(cs)) == True{} : Bool}
  {FCv.ffi(cvs_spell_xreq(as, cs, "")) == cvs_spell_exp(Cvar.spec_expand(cs, as), "") : String}
