# eukhe: the laws of area cvar

import Base
import ../bend/cvar.bend as Cv
import ../bend/ffi_cvar.bend as FCv
import ../bend/wire.bend as Wr
import ./base.bend as LawsBase

# (S4) Settings as console variables
# ----------------------------------
# docs/control.md S4, the model in bend/cvar.bend. Every input is free:
# any declarations (duplicate ids, wrong defaults), any config.cfg, any
# family of agents with any profiles and sets (wrong types, Global cvars,
# undeclared ids), any alias table.

# LAW: the registry holds each id once: a second declaration is rejected
law cvar_registry_unique:
  for xs: List<&2, Cv.Decl>
  {Cv.unique(Cv.registry(xs)) == True{} : Bool}

# LAW: every declaration of the registry has a default of its type
law cvar_registry_typed:
  for xs: List<&2, Cv.Decl>
  {Cv.all_typed(Cv.registry(xs)) == True{} : Bool}

# LAW: every value has the type of its cvar, in every agent; an
# undeclared cvar has no value
law cvar_value_typed:
  for +xs: List<&2, Cv.Decl>
  for +cfg: List<&2, Cv.Bind>
  for +fam: List<&2, Cv.Ag>
  for +x: Nat
  {Cv.typed.at(Cv.find(Cv.registry(xs), x), Cv.value(Cv.registry(xs), cfg, fam, x)) == True{} : Bool}

# LAW: a subagent with no profile and no sets has its parent's values
law cvar_inherits:
  for +ds: List<&2, Cv.Decl>
  for +cfg: List<&2, Cv.Bind>
  for +fam: List<&2, Cv.Ag>
  for +x: Nat
  {Cv.value(ds, cfg, List.append(&2, Cv.Ag, fam, [Cv.Ag{Nil{}, Nil{}}]), x) == Cv.value(ds, cfg, fam, x) : Maybe<&2, Cv.Val>}

# LAW: a subagent's last valid set wins over its parent's value
law cvar_set_wins:
  for +ds: List<&2, Cv.Decl>
  for +cfg: List<&2, Cv.Bind>
  for +fam: List<&2, Cv.Ag>
  for +p: List<&2, Cv.Bind>
  for +ss: List<&2, Cv.Bind>
  for +x: Nat
  for +v: Cv.Val
  for ok: {Cv.valid(ds, Cv.Agent{}, Cv.Bind{x, v}) == True{} : Bool}
  {Cv.value(ds, cfg, List.append(&2, Cv.Ag, fam, [Cv.Ag{p, List.append(&2, Cv.Bind, ss, [Cv.Bind{x, v}])}]), x) == Some{v} : Maybe<&2, Cv.Val>}

# LAW: a Global cvar has one value in every agent of every family: the
# value of config.cfg on the default; no profile or set changes it
law cvar_global_uniform:
  for +ds: List<&2, Cv.Decl>
  for +cfg: List<&2, Cv.Bind>
  for +fam: List<&2, Cv.Ag>
  for +x: Nat
  for +d: Cv.Decl
  for found: {Cv.find(ds, x) == Some{d} : Maybe<&2, Cv.Decl>}
  for global: {Cv.Decl.local(d) == False{} : Bool}
  {Cv.value(ds, cfg, fam, x) == Some{Cv.root.val(ds, cfg, x, d)} : Maybe<&2, Cv.Val>}

# LAW: an agent writes to its cfg only cvars that persist, and replicates
# only cvars that replicate
law cvar_written_flagged:
  for ss: List<&2, Cv.Bind>
  for +ds: List<&2, Cv.Decl>
  for +f: Cv.Flag
  {Cv.all_flag(Cv.written(ss, ds, f), ds, f) == True{} : Bool}

# LAW: the cfg an agent writes, read back as its profile, gives the same
# value of every cvar that persists
law cvar_persist_roundtrip:
  for +ds: List<&2, Cv.Decl>
  for +cfg: List<&2, Cv.Bind>
  for +ss: List<&2, Cv.Bind>
  for +x: Nat
  for keeps: {Cv.flag.at(Cv.find(ds, x), Cv.Persist{}) == True{} : Bool}
  {Cv.value(ds, cfg, [Cv.Ag{Cv.written(ss, ds, Cv.Persist{}), Nil{}}], x) == Cv.value(ds, cfg, [Cv.Ag{Nil{}, ss}], x) : Maybe<&2, Cv.Val>}

# LAW: a toggle twice, in any agent of any family, gives back the value
law cvar_toggle_twice:
  for +ds: List<&2, Cv.Decl>
  for +cfg: List<&2, Cv.Bind>
  for +fam: List<&2, Cv.Ag>
  for +a: Cv.Ag
  for +x: Nat
  {Cv.value(ds, cfg, List.append(&2, Cv.Ag, fam, [Cv.toggle(ds, cfg, fam, Cv.toggle(ds, cfg, fam, a, x), x)]), x) == Cv.value(ds, cfg, List.append(&2, Cv.Ag, fam, [a]), x) : Maybe<&2, Cv.Val>}

# LAW: an expansion leaves no alias to run: every alias is expanded, or
# the expansion reports a cycle or an unknown alias
law alias_expands_fully:
  for cs: List<&2, Cv.Cmd>
  for +as: List<&2, Cv.Alias>
  {Cv.Exp.plain(Cv.expand(cs, as)) == True{} : Bool}

# LAW: an alias that runs itself is a cycle, not an endless expansion;
# the cycle names the alias
law alias_self_cycle:
  for +n: Nat
  for +as: List<&2, Cv.Alias>
  {Cv.expand([Cv.CRun{n}], Cv.Alias{n, [Cv.CRun{n}]} <> as) == Cv.Cycle{n} : Cv.Exp}

# LAW: a run of an alias that does not exist is reported, with its name
law alias_unknown_reported:
  for +n: Nat
  for +as: List<&2, Cv.Alias>
  for gone: {Cv.body(as, n) == [Cv.CGone{n}] : List<&2, Cv.Cmd>}
  {Cv.expand([Cv.CRun{n}], as) == Cv.Unknown{n} : Cv.Exp}

# LAW: an alias with plain commands runs exactly its commands
law alias_runs_body:
  for +n: Nat
  for +b: List<&2, Cv.Cmd>
  for +as: List<&2, Cv.Alias>
  for flat: {Cv.plain(b) == True{} : Bool}
  {Cv.expand([Cv.CRun{n}], Cv.Alias{n, b} <> as) == Cv.Flat{b} : Cv.Exp}

# two expansions one after the other: the commands of both, in order, or
# the first error (an error of the first stops it before the second)
def cvar_cat(a: Cv.Exp, b: Cv.Exp) -> Cv.Exp:
  match a:
    case Cv.Flat{x}:
      match b:
        case Cv.Flat{y}:
          Cv.Flat{List.append(&2, Cv.Cmd, x, y)}
        case Cv.Cycle{n}:
          Cv.Cycle{n}
        case Cv.Unknown{n}:
          Cv.Unknown{n}
    case Cv.Cycle{n}:
      Cv.Cycle{n}
    case Cv.Unknown{n}:
      Cv.Unknown{n}

# LAW: a list expands command by command, in order: the expansion of two
# lists one after the other is the first's commands then the second's,
# and the first error, left to right, is the outcome
law alias_expands_in_order:
  for +cs: List<&2, Cv.Cmd>
  for +more: List<&2, Cv.Cmd>
  for +as: List<&2, Cv.Alias>
  {Cv.expand(List.append(&2, Cv.Cmd, cs, more), as) == cvar_cat(Cv.expand(cs, as), Cv.expand(more, as)) : Cv.Exp}

# LAW: anchor (the Rust test of expand): aliases a = [set x, run b],
# b = [set y], loop = [run loop2], loop2 = [run loop], gone = [run
# missing] (numbered 0 to 4, missing 5, the cvars x y z q 10 to 13):
# [run a, set z] runs x, y, z; [run loop] is a cycle at loop; [run gone]
# names missing; [set q, run loop, run missing] stops at the cycle
law alias_expand_example:
  {[Cv.expand([Cv.CRun{0n}, Cv.CToggle{12n}], [Cv.Alias{0n, [Cv.CToggle{10n}, Cv.CRun{1n}]}, Cv.Alias{1n, [Cv.CToggle{11n}]}, Cv.Alias{2n, [Cv.CRun{3n}]}, Cv.Alias{3n, [Cv.CRun{2n}]}, Cv.Alias{4n, [Cv.CRun{5n}]}]), Cv.expand([Cv.CRun{2n}], [Cv.Alias{0n, [Cv.CToggle{10n}, Cv.CRun{1n}]}, Cv.Alias{1n, [Cv.CToggle{11n}]}, Cv.Alias{2n, [Cv.CRun{3n}]}, Cv.Alias{3n, [Cv.CRun{2n}]}, Cv.Alias{4n, [Cv.CRun{5n}]}]), Cv.expand([Cv.CRun{4n}], [Cv.Alias{0n, [Cv.CToggle{10n}, Cv.CRun{1n}]}, Cv.Alias{1n, [Cv.CToggle{11n}]}, Cv.Alias{2n, [Cv.CRun{3n}]}, Cv.Alias{3n, [Cv.CRun{2n}]}, Cv.Alias{4n, [Cv.CRun{5n}]}]), Cv.expand([Cv.CToggle{13n}, Cv.CRun{2n}, Cv.CRun{5n}], [Cv.Alias{0n, [Cv.CToggle{10n}, Cv.CRun{1n}]}, Cv.Alias{1n, [Cv.CToggle{11n}]}, Cv.Alias{2n, [Cv.CRun{3n}]}, Cv.Alias{3n, [Cv.CRun{2n}]}, Cv.Alias{4n, [Cv.CRun{5n}]}])] == [Cv.Flat{[Cv.CToggle{10n}, Cv.CToggle{11n}, Cv.CToggle{12n}]}, Cv.Cycle{2n}, Cv.Unknown{5n}, Cv.Cycle{2n}] : List<&2, Cv.Exp>}

# LAW: a key press runs only plain commands: every alias it names is
# expanded, or the press reports a cycle or an unknown alias
law bind_press_plain:
  for +bs: List<&2, Cv.KeyBind>
  for +k: Nat
  for +as: List<&2, Cv.Alias>
  {Cv.Exp.plain(Cv.press(bs, k, as)) == True{} : Bool}

# LAW: a key with no bind runs nothing
law bind_unbound_runs_nothing:
  for +bs: List<&2, Cv.KeyBind>
  for +k: Nat
  for +as: List<&2, Cv.Alias>
  for free: {Cv.bound(bs, k) == Nil{} : List<&2, Cv.Cmd>}
  {Cv.press(bs, k, as) == Cv.Flat{Nil{}} : Cv.Exp}

# LAW: a press of a key runs the commands of its first bind
law bind_first_wins:
  for +k: Nat
  for +c: List<&2, Cv.Cmd>
  for +rest: List<&2, Cv.KeyBind>
  for +as: List<&2, Cv.Alias>
  {Cv.press(Cv.KeyBind{k, c} <> rest, k, as) == Cv.expand(c, as) : Cv.Exp}

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

# LAW: an expand request that fits reads back whole
# EXCLUDES: an alias, a command or a number lost, swapped or misread on
#   the way to the model
law cvar_ffi_round_trip:
  for +as: List<&2, Cv.Alias>
  for +cs: List<&2, Cv.Cmd>
  for +rest: String
  for h: {Bool.and(cvar_aliases_fit(as), cvar_cmds_fit(cs)) == True{} : Bool}
  {FCv.get_xreq(FCv.put_xreq(FCv.Xreq{as, cs}, rest)) == Wr.Got{FCv.Xreq{as, cs}, rest} : Wr.Dec<FCv.Xreq>}

# LAW: the expand entry answers the model's expansion
# EXCLUDES: an entry that expands by any other rule, or answers a default
law cvar_ffi_is_expand:
  for +as: List<&2, Cv.Alias>
  for +cs: List<&2, Cv.Cmd>
  for h: {Bool.and(cvar_aliases_fit(as), cvar_cmds_fit(cs)) == True{} : Bool}
  {FCv.ffi(FCv.put_xreq(FCv.Xreq{as, cs}, "")) == FCv.put_exp(Cv.expand(cs, as), "") : String}

# LAW: a malformed expand request answers the error form
# EXCLUDES: a default expansion (nothing to run) for bad input
law cvar_ffi_malformed:
  for +s: String
  for h: {FCv.get_xreq(s) == Wr.Bad{} : Wr.Dec<FCv.Xreq>}
  {FCv.ffi(s) == Wr.err("cvar: malformed expand request") : String}

# LAW: a bind table that fits opens the press state of that table
# EXCLUDES: a table read with a bind or an alias lost or changed
law cvar_ffi_open:
  for +bs: List<&2, Cv.KeyBind>
  for +as: List<&2, Cv.Alias>
  for h: {Bool.and(cvar_binds_fit(bs), cvar_aliases_fit(as)) == True{} : Bool}
  {FCv.open(FCv.put_table(bs, as, "")) == (FCv.Table{bs, as}, "") : FCv.St & String}

# LAW: a malformed bind table opens the refused state, with the error form
# EXCLUDES: an empty table (every key unbound) for bad input
law cvar_ffi_open_malformed:
  for +s: String
  for h: {FCv.get_table(s) == Wr.Bad{} : Wr.Dec<FCv.St>}
  {FCv.open(s) == (FCv.Refused{}, Wr.err("cvar: malformed press table")) : FCv.St & String}

# LAW: a press of a key answers the model's press, and the table stays
# EXCLUDES: a press by any other rule, a table that changes between
#   presses
law cvar_ffi_press:
  for +bs: List<&2, Cv.KeyBind>
  for +as: List<&2, Cv.Alias>
  for +k: Nat
  for h: {LawsBase.wire_fits(k) == True{} : Bool}
  {FCv.step(FCv.Table{bs, as}, Wr.put_nat(k, "")) == (FCv.Table{bs, as}, FCv.put_exp(Cv.press(bs, k, as), "")) : FCv.St & String}

# LAW: a refused table answers every press with the error form
# EXCLUDES: a press that runs anything after a refused open
law cvar_ffi_refused:
  for +s: String
  {FCv.step(FCv.Refused{}, s) == (FCv.Refused{}, Wr.err("cvar: the press table was refused")) : FCv.St & String}

# LAW: witness: a table and a command list fit
law cvar_fits_example:
  {Bool.and(cvar_binds_fit([Cv.KeyBind{0n, [Cv.CRun{1n}, Cv.CToggle{0n}]}]), Bool.and(cvar_aliases_fit([Cv.Alias{1n, [Cv.CSet{2n, Cv.VBool{True{}}}, Cv.CGone{3n}]}]), cvar_cmds_fit([Cv.CSet{0n, Cv.VNat{7n}}]))) == True{} : Bool}
