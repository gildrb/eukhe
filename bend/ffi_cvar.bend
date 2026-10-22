# ffi_cvar: the entries of the command language (bend/cvar.bend: expand,
# press) in the compiled Bend core. Rust (crates/eukhe-bend/src/rules/
# cvar.rs) numbers the aliases and keeps every command that is not a run
# of an alias aside: such a command crosses as `CToggle{i}`, i its place
# in Rust's list (the model passes every command that is not a run
# through unchanged: alias_runs_body, alias_expands_in_order), and a run
# crosses as `CRun{n}`, n the alias's number (its place in the table, or a
# number past the table for a name the table does not hold).
#
# Wire (crates/eukhe-bend/WIRE.md):
#   Val     = tag 0 VNat (Nat) | 1 VBool (Bool)
#   Cmd     = tag 0 CSet (Nat, Val) | 1 CToggle (Nat) | 2 CRun (Nat)
#             | 3 CGone (Nat)
#   Alias   = a record (name: Nat, body: List<Cmd>)
#   KeyBind = a record (key: Nat, cmds: List<Cmd>)
#   Exp     = tag 0 Flat (List<Cmd>) | 1 Cycle (Nat) | 2 Unknown (Nat)
#
# call (`expand`): request a record (aliases: List<Alias>, cmds:
# List<Cmd>); reply the Exp of Cv.expand(cmds, aliases).
# stepper (`press`): open with a record (binds: List<KeyBind>, aliases:
# List<Alias>), reply empty; each step is a key (a Nat), its reply the Exp
# of Cv.press(binds, key, aliases); the table never changes.

import Base
import ./wire.bend as W
import ./cvar.bend as Cv

# Values
# ------

def put_val(v: Cv.Val, rest: String) -> String:
  match v:
    case Cv.VNat{n}:
      W.put_nat(0n, W.put_nat(n, rest))
    case Cv.VBool{b}:
      W.put_nat(1n, W.put_bool(b, rest))

def get_val.nat(r: W.Dec<Nat>) -> W.Dec<Cv.Val>:
  match r:
    case W.Got{n, s}:
      W.Got{Cv.VNat{n}, s}
    case W.Bad{}:
      W.Bad{}

def get_val.bool(r: W.Dec<Bool>) -> W.Dec<Cv.Val>:
  match r:
    case W.Got{b, s}:
      W.Got{Cv.VBool{b}, s}
    case W.Bad{}:
      W.Bad{}

def get_val.tag(t: Nat, s: String) -> W.Dec<Cv.Val>:
  match t:
    case 0n:
      get_val.nat(W.get_nat(s))
    case 1n:
      get_val.bool(W.get_bool(s))
    case 2n+x:
      W.Bad{}

def get_val.go(r: W.Dec<Nat>) -> W.Dec<Cv.Val>:
  match r:
    case W.Got{t, s}:
      get_val.tag(t, s)
    case W.Bad{}:
      W.Bad{}

def get_val(s: String) -> W.Dec<Cv.Val>:
  get_val.go(W.get_nat(s))

# Commands
# --------

def put_cmd(c: Cv.Cmd, rest: String) -> String:
  match c:
    case Cv.CSet{i, v}:
      W.put_nat(0n, W.put_nat(i, put_val(v, rest)))
    case Cv.CToggle{i}:
      W.put_nat(1n, W.put_nat(i, rest))
    case Cv.CRun{n}:
      W.put_nat(2n, W.put_nat(n, rest))
    case Cv.CGone{n}:
      W.put_nat(3n, W.put_nat(n, rest))

def get_cmd.set.v(i: Nat, r: W.Dec<Cv.Val>) -> W.Dec<Cv.Cmd>:
  match r:
    case W.Got{v, s}:
      W.Got{Cv.CSet{i, v}, s}
    case W.Bad{}:
      W.Bad{}

def get_cmd.set(r: W.Dec<Nat>) -> W.Dec<Cv.Cmd>:
  match r:
    case W.Got{i, s}:
      get_cmd.set.v(i, get_val(s))
    case W.Bad{}:
      W.Bad{}

def get_cmd.toggle(r: W.Dec<Nat>) -> W.Dec<Cv.Cmd>:
  match r:
    case W.Got{i, s}:
      W.Got{Cv.CToggle{i}, s}
    case W.Bad{}:
      W.Bad{}

def get_cmd.run(r: W.Dec<Nat>) -> W.Dec<Cv.Cmd>:
  match r:
    case W.Got{n, s}:
      W.Got{Cv.CRun{n}, s}
    case W.Bad{}:
      W.Bad{}

def get_cmd.gone(r: W.Dec<Nat>) -> W.Dec<Cv.Cmd>:
  match r:
    case W.Got{n, s}:
      W.Got{Cv.CGone{n}, s}
    case W.Bad{}:
      W.Bad{}

def get_cmd.tag(t: Nat, s: String) -> W.Dec<Cv.Cmd>:
  match t:
    case 0n:
      get_cmd.set(W.get_nat(s))
    case 1n:
      get_cmd.toggle(W.get_nat(s))
    case 2n:
      get_cmd.run(W.get_nat(s))
    case 3n:
      get_cmd.gone(W.get_nat(s))
    case 4n+x:
      W.Bad{}

def get_cmd.go(r: W.Dec<Nat>) -> W.Dec<Cv.Cmd>:
  match r:
    case W.Got{t, s}:
      get_cmd.tag(t, s)
    case W.Bad{}:
      W.Bad{}

def get_cmd(s: String) -> W.Dec<Cv.Cmd>:
  get_cmd.go(W.get_nat(s))

def put_cmds(cs: List<&2, Cv.Cmd>, rest: String) -> String:
  W.put_list(~Cv.Cmd, ~put_cmd, cs, rest)

def get_cmds(s: String) -> W.Dec<List<&2, Cv.Cmd>>:
  W.get_list(~Cv.Cmd, ~get_cmd, s)

# Aliases and binds
# -----------------

def put_alias(a: Cv.Alias, rest: String) -> String:
  match a:
    case Cv.Alias{n, b}:
      W.put_nat(n, put_cmds(b, rest))

def get_alias.body(n: Nat, r: W.Dec<List<&2, Cv.Cmd>>) -> W.Dec<Cv.Alias>:
  match r:
    case W.Got{b, s}:
      W.Got{Cv.Alias{n, b}, s}
    case W.Bad{}:
      W.Bad{}

def get_alias.name(r: W.Dec<Nat>) -> W.Dec<Cv.Alias>:
  match r:
    case W.Got{n, s}:
      get_alias.body(n, get_cmds(s))
    case W.Bad{}:
      W.Bad{}

def get_alias(s: String) -> W.Dec<Cv.Alias>:
  get_alias.name(W.get_nat(s))

def put_bind(k: Cv.KeyBind, rest: String) -> String:
  match k:
    case Cv.KeyBind{n, c}:
      W.put_nat(n, put_cmds(c, rest))

def get_bind.cmds(n: Nat, r: W.Dec<List<&2, Cv.Cmd>>) -> W.Dec<Cv.KeyBind>:
  match r:
    case W.Got{c, s}:
      W.Got{Cv.KeyBind{n, c}, s}
    case W.Bad{}:
      W.Bad{}

def get_bind.key(r: W.Dec<Nat>) -> W.Dec<Cv.KeyBind>:
  match r:
    case W.Got{n, s}:
      get_bind.cmds(n, get_cmds(s))
    case W.Bad{}:
      W.Bad{}

def get_bind(s: String) -> W.Dec<Cv.KeyBind>:
  get_bind.key(W.get_nat(s))

# Expansions
# ----------

def put_exp(e: Cv.Exp, rest: String) -> String:
  match e:
    case Cv.Flat{cs}:
      W.put_nat(0n, put_cmds(cs, rest))
    case Cv.Cycle{n}:
      W.put_nat(1n, W.put_nat(n, rest))
    case Cv.Unknown{n}:
      W.put_nat(2n, W.put_nat(n, rest))

# The expand request
# ------------------

type Xreq is Data:
  Xreq{aliases: List<&2, Cv.Alias>, cmds: List<&2, Cv.Cmd>}

def put_xreq(q: Xreq, rest: String) -> String:
  match q:
    case Xreq{as, cs}:
      W.put_list(~Cv.Alias, ~put_alias, as, put_cmds(cs, rest))

def get_xreq.cmds(as: List<&2, Cv.Alias>, r: W.Dec<List<&2, Cv.Cmd>>) -> W.Dec<Xreq>:
  match r:
    case W.Got{cs, s}:
      W.Got{Xreq{as, cs}, s}
    case W.Bad{}:
      W.Bad{}

def get_xreq.aliases(r: W.Dec<List<&2, Cv.Alias>>) -> W.Dec<Xreq>:
  match r:
    case W.Got{as, s}:
      get_xreq.cmds(as, get_cmds(s))
    case W.Bad{}:
      W.Bad{}

def get_xreq(s: String) -> W.Dec<Xreq>:
  get_xreq.aliases(W.get_list(~Cv.Alias, ~get_alias, s))

def ffi.run(q: Xreq) -> String:
  match q:
    case Xreq{as, cs}:
      put_exp(Cv.expand(cs, as), "")

def ffi.whole(q: Xreq, done: Bool) -> String:
  match done:
    case True{}:
      ffi.run(q)
    case False{}:
      W.err("cvar: input left over")

def ffi.go(r: W.Dec<Xreq>) -> String:
  match r:
    case W.Got{q, s}:
      ffi.whole(q, W.end(s))
    case W.Bad{}:
      W.err("cvar: malformed expand request")

# expand: the alias table and a command list in, the expansion out
def ffi(input: String) -> String:
  ffi.go(get_xreq(input))

# The press stepper
# -----------------

# the binds and the aliases of a press table, or a refused open
type St is Data:
  Table{binds: List<&2, Cv.KeyBind>, aliases: List<&2, Cv.Alias>}
  Refused{}

def get_table.aliases(bs: List<&2, Cv.KeyBind>, r: W.Dec<List<&2, Cv.Alias>>) -> W.Dec<St>:
  match r:
    case W.Got{as, s}:
      W.Got{Table{bs, as}, s}
    case W.Bad{}:
      W.Bad{}

def get_table.binds(r: W.Dec<List<&2, Cv.KeyBind>>) -> W.Dec<St>:
  match r:
    case W.Got{bs, s}:
      get_table.aliases(bs, W.get_list(~Cv.Alias, ~get_alias, s))
    case W.Bad{}:
      W.Bad{}

def get_table(s: String) -> W.Dec<St>:
  get_table.binds(W.get_list(~Cv.KeyBind, ~get_bind, s))

def put_table(bs: List<&2, Cv.KeyBind>, as: List<&2, Cv.Alias>, rest: String) -> String:
  W.put_list(~Cv.KeyBind, ~put_bind, bs, W.put_list(~Cv.Alias, ~put_alias, as, rest))

def open.whole(t: St, done: Bool) -> St & String:
  match done:
    case True{}:
      (t, "")
    case False{}:
      (Refused{}, W.err("cvar: input left over"))

def open.go(r: W.Dec<St>) -> St & String:
  match r:
    case W.Got{t, s}:
      open.whole(t, W.end(s))
    case W.Bad{}:
      (Refused{}, W.err("cvar: malformed press table"))

# open: the press table in; the reply is empty
def open(input: String) -> St & String:
  open.go(get_table(input))

def step.key(+bs: List<&2, Cv.KeyBind>, +as: List<&2, Cv.Alias>, r: W.Dec<Nat>) -> St & String:
  match r:
    case W.Got{k, s}:
      match s:
        case SNil{}:
          (Table{bs, as}, put_exp(Cv.press(bs, k, as), ""))
        case SCon{c, t}:
          (Table{bs, as}, W.err("cvar: input left over"))
    case W.Bad{}:
      (Table{bs, as}, W.err("cvar: malformed key"))

# step: a key in, the expansion of its press out; the table stays
def step(st: St, input: String) -> St & String:
  match st:
    case Table{+bs, +as}:
      step.key(bs, as, W.get_nat(input))
    case Refused{}:
      (Refused{}, W.err("cvar: the press table was refused"))
