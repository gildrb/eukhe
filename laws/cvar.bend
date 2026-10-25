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

# LAW cvar_registry_unique: the registry holds each id once: a second declaration is rejected
law cvar_registry_unique:
  for xs: List<&2, Cv.Decl>
  {Cv.unique(Cv.registry(xs)) == True{} : Bool}

# LAW cvar_registry_typed: every declaration of the registry has a default of its type
law cvar_registry_typed:
  for xs: List<&2, Cv.Decl>
  {Cv.all_typed(Cv.registry(xs)) == True{} : Bool}

# LAW cvar_value_typed: every value has the type of its cvar, in every agent; an
# undeclared cvar has no value
law cvar_value_typed:
  for +xs: List<&2, Cv.Decl>
  for +cfg: List<&2, Cv.Bind>
  for +fam: List<&2, Cv.Ag>
  for +x: Nat
  {Cv.typed.at(Cv.find(Cv.registry(xs), x), Cv.value(Cv.registry(xs), cfg, fam, x)) == True{} : Bool}

# LAW cvar_inherits: a subagent with no profile and no sets has its parent's values
law cvar_inherits:
  for +ds: List<&2, Cv.Decl>
  for +cfg: List<&2, Cv.Bind>
  for +fam: List<&2, Cv.Ag>
  for +x: Nat
  {Cv.value(ds, cfg, List.append(&2, Cv.Ag, fam, [Cv.Ag{Nil{}, Nil{}}]), x) == Cv.value(ds, cfg, fam, x) : Maybe<&2, Cv.Val>}

# LAW cvar_set_wins: a subagent's last valid set wins over its parent's value
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

# LAW cvar_global_uniform: a Global cvar has one value in every agent of every family: the
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

# LAW cvar_written_flagged: an agent writes to its cfg only cvars that persist, and replicates
# only cvars that replicate
law cvar_written_flagged:
  for ss: List<&2, Cv.Bind>
  for +ds: List<&2, Cv.Decl>
  for +f: Cv.Flag
  {Cv.all_flag(Cv.written(ss, ds, f), ds, f) == True{} : Bool}

# LAW cvar_persist_roundtrip: the cfg an agent writes, read back as its profile, gives the same
# value of every cvar that persists
law cvar_persist_roundtrip:
  for +ds: List<&2, Cv.Decl>
  for +cfg: List<&2, Cv.Bind>
  for +ss: List<&2, Cv.Bind>
  for +x: Nat
  for keeps: {Cv.flag.at(Cv.find(ds, x), Cv.Persist{}) == True{} : Bool}
  {Cv.value(ds, cfg, [Cv.Ag{Cv.written(ss, ds, Cv.Persist{}), Nil{}}], x) == Cv.value(ds, cfg, [Cv.Ag{Nil{}, ss}], x) : Maybe<&2, Cv.Val>}

# LAW cvar_toggle_twice: a toggle twice, in any agent of any family, gives back the value
law cvar_toggle_twice:
  for +ds: List<&2, Cv.Decl>
  for +cfg: List<&2, Cv.Bind>
  for +fam: List<&2, Cv.Ag>
  for +a: Cv.Ag
  for +x: Nat
  {Cv.value(ds, cfg, List.append(&2, Cv.Ag, fam, [Cv.toggle(ds, cfg, fam, Cv.toggle(ds, cfg, fam, a, x), x)]), x) == Cv.value(ds, cfg, List.append(&2, Cv.Ag, fam, [a]), x) : Maybe<&2, Cv.Val>}

# LAW alias_expands_fully: an expansion leaves no alias to run: every alias is expanded, or
# the expansion reports a cycle or an unknown alias
law alias_expands_fully:
  for cs: List<&2, Cv.Cmd>
  for +as: List<&2, Cv.Alias>
  {Cv.Exp.plain(Cv.expand(cs, as)) == True{} : Bool}

# LAW alias_self_cycle: an alias that runs itself is a cycle, not an endless expansion;
# the cycle names the alias
law alias_self_cycle:
  for +n: Nat
  for +as: List<&2, Cv.Alias>
  {Cv.expand([Cv.CRun{n}], Cv.Alias{n, [Cv.CRun{n}]} <> as) == Cv.Cycle{n} : Cv.Exp}

# LAW alias_unknown_reported: a run of an alias that does not exist is reported, with its name
law alias_unknown_reported:
  for +n: Nat
  for +as: List<&2, Cv.Alias>
  for gone: {Cv.body(as, n) == [Cv.CGone{n}] : List<&2, Cv.Cmd>}
  {Cv.expand([Cv.CRun{n}], as) == Cv.Unknown{n} : Cv.Exp}

# LAW alias_runs_body: an alias with plain commands runs exactly its commands
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

# LAW alias_expands_in_order: a list expands command by command, in order: the expansion of two
# lists one after the other is the first's commands then the second's,
# and the first error, left to right, is the outcome
law alias_expands_in_order:
  for +cs: List<&2, Cv.Cmd>
  for +more: List<&2, Cv.Cmd>
  for +as: List<&2, Cv.Alias>
  {Cv.expand(List.append(&2, Cv.Cmd, cs, more), as) == cvar_cat(Cv.expand(cs, as), Cv.expand(more, as)) : Cv.Exp}

# LAW alias_expand_example: anchor (the Rust test of expand): aliases a = [set x, run b],
# b = [set y], loop = [run loop2], loop2 = [run loop], gone = [run
# missing] (numbered 0 to 4, missing 5, the cvars x y z q 10 to 13):
# [run a, set z] runs x, y, z; [run loop] is a cycle at loop; [run gone]
# names missing; [set q, run loop, run missing] stops at the cycle
law alias_expand_example:
  {[Cv.expand([Cv.CRun{0n}, Cv.CToggle{12n}], [Cv.Alias{0n, [Cv.CToggle{10n}, Cv.CRun{1n}]}, Cv.Alias{1n, [Cv.CToggle{11n}]}, Cv.Alias{2n, [Cv.CRun{3n}]}, Cv.Alias{3n, [Cv.CRun{2n}]}, Cv.Alias{4n, [Cv.CRun{5n}]}]), Cv.expand([Cv.CRun{2n}], [Cv.Alias{0n, [Cv.CToggle{10n}, Cv.CRun{1n}]}, Cv.Alias{1n, [Cv.CToggle{11n}]}, Cv.Alias{2n, [Cv.CRun{3n}]}, Cv.Alias{3n, [Cv.CRun{2n}]}, Cv.Alias{4n, [Cv.CRun{5n}]}]), Cv.expand([Cv.CRun{4n}], [Cv.Alias{0n, [Cv.CToggle{10n}, Cv.CRun{1n}]}, Cv.Alias{1n, [Cv.CToggle{11n}]}, Cv.Alias{2n, [Cv.CRun{3n}]}, Cv.Alias{3n, [Cv.CRun{2n}]}, Cv.Alias{4n, [Cv.CRun{5n}]}]), Cv.expand([Cv.CToggle{13n}, Cv.CRun{2n}, Cv.CRun{5n}], [Cv.Alias{0n, [Cv.CToggle{10n}, Cv.CRun{1n}]}, Cv.Alias{1n, [Cv.CToggle{11n}]}, Cv.Alias{2n, [Cv.CRun{3n}]}, Cv.Alias{3n, [Cv.CRun{2n}]}, Cv.Alias{4n, [Cv.CRun{5n}]}])] == [Cv.Flat{[Cv.CToggle{10n}, Cv.CToggle{11n}, Cv.CToggle{12n}]}, Cv.Cycle{2n}, Cv.Unknown{5n}, Cv.Cycle{2n}] : List<&2, Cv.Exp>}

# LAW bind_press_plain: a key press runs only plain commands: every alias it names is
# expanded, or the press reports a cycle or an unknown alias
law bind_press_plain:
  for +bs: List<&2, Cv.KeyBind>
  for +k: Nat
  for +as: List<&2, Cv.Alias>
  {Cv.Exp.plain(Cv.press(bs, k, as)) == True{} : Bool}

# LAW bind_unbound_runs_nothing: a key with no bind runs nothing
law bind_unbound_runs_nothing:
  for +bs: List<&2, Cv.KeyBind>
  for +k: Nat
  for +as: List<&2, Cv.Alias>
  for free: {Cv.bound(bs, k) == Nil{} : List<&2, Cv.Cmd>}
  {Cv.press(bs, k, as) == Cv.Flat{Nil{}} : Cv.Exp}

# LAW bind_first_wins: a press of a key runs the commands of its first bind
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

# ---- cvar resolution ----

# LAWS (S4, the decisions the compiled core makes for the Rust code; the
# entry bend/ffi_cvar_layers.bend, laws/cvar_layers.bend): which
# declaration a registry refuses first, the value of each cvar and the
# value a layer sets, the verdict on a set and on a toggle, the sets an
# agent writes, the config sets of a settings document. Each is pinned
# whole to a spec written here from the requirement. Every input is free:
# any declarations (duplicate ids, wrong defaults), any config, any family
# with any profiles and sets (wrong types, Global cvars, undeclared ids).

# Spec helpers
# ------------

def spec_id(d: Cv.Decl) -> Nat:
  match d:
    case Cv.Decl{i, t, c, p, r, v}:
      i

def spec_ty(d: Cv.Decl) -> Cv.Ty:
  match d:
    case Cv.Decl{i, t, c, p, r, v}:
      t

def spec_init(d: Cv.Decl) -> Cv.Val:
  match d:
    case Cv.Decl{i, t, c, p, r, v}:
      v

# the cvar may differ per agent
def spec_local(d: Cv.Decl) -> Bool:
  match d:
    case Cv.Decl{i, t, c, p, r, v}:
      match c:
        case Cv.Global{}:
          False{}
        case Cv.Local{}:
          True{}

# the declaration has flag f
def spec_flag(d: Cv.Decl, f: Cv.Flag) -> Bool:
  match d:
    case Cv.Decl{i, t, c, p, r, v}:
      match f:
        case Cv.Persist{}:
          p
        case Cv.Replicate{}:
          r

# the value v has type t
def spec_typed(v: Cv.Val, t: Cv.Ty) -> Bool:
  match v:
    case Cv.VNat{n}:
      match t:
        case Cv.TNat{}:
          True{}
        case Cv.TBool{}:
          False{}
    case Cv.VBool{b}:
      match t:
        case Cv.TNat{}:
          False{}
        case Cv.TBool{}:
          True{}

def spec_find.pick(hit: Bool, d: Cv.Decl, r: Maybe<&2, Cv.Decl>) -> Maybe<&2, Cv.Decl>:
  match hit:
    case True{}:
      Some{d}
    case False{}:
      r

# the declaration of x: the first one with id x
def spec_find(ds: List<&2, Cv.Decl>, +x: Nat) -> Maybe<&2, Cv.Decl>:
  match ds:
    case Nil{}:
      None{}
    case +d <> rest:
      spec_find.pick(Nat.is_eq(spec_id(d), x), d, spec_find(rest, x))

def spec_valid.agent(local: Bool, ok: Bool) -> Bool:
  match local:
    case True{}:
      ok
    case False{}:
      False{}

def spec_valid.at(m: Maybe<&2, Cv.Decl>, l: Cv.Layer, v: Cv.Val) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{+d}:
      match l:
        case Cv.Config{}:
          spec_typed(v, spec_ty(d))
        case Cv.Agent{}:
          spec_valid.agent(spec_local(d), spec_typed(v, spec_ty(d)))

# a set counts in layer l: its cvar is declared, the value has its type,
# and an agent layer (a profile, an agent's own sets) holds Local cvars only
def spec_valid(+ds: List<&2, Cv.Decl>, l: Cv.Layer, s: Cv.Bind) -> Bool:
  match s:
    case Cv.Bind{i, v}:
      spec_valid.at(spec_find(ds, i), l, v)

def spec_last.pick(ok: Bool, v: Cv.Val, cur: Maybe<&2, Cv.Val>) -> Maybe<&2, Cv.Val>:
  match ok:
    case True{}:
      Some{v}
    case False{}:
      cur

# the value of the last set of x in ss that counts in layer l, else cur
def spec_last(ss: List<&2, Cv.Bind>, +ds: List<&2, Cv.Decl>, +l: Cv.Layer, +x: Nat, cur: Maybe<&2, Cv.Val>) -> Maybe<&2, Cv.Val>:
  match ss:
    case Nil{}:
      cur
    case Cv.Bind{+i, +v} <> rest:
      spec_last(rest, ds, l, x, spec_last.pick(Bool.and(Nat.is_eq(i, x), spec_valid(ds, l, Cv.Bind{i, v})), v, cur))

# the agents in order, root first: each one's profile, then its own sets
def spec_agents(fam: List<&2, Cv.Ag>, +ds: List<&2, Cv.Decl>, +x: Nat, cur: Maybe<&2, Cv.Val>) -> Maybe<&2, Cv.Val>:
  match fam:
    case Nil{}:
      cur
    case Cv.Ag{p, s} <> rest:
      spec_agents(rest, ds, x, spec_last(s, ds, Cv.Agent{}, x, spec_last(p, ds, Cv.Agent{}, x, cur)))

# the value the layers set for x: the last set that counts, over
# config.cfg, then each agent of the family chain, root first
def spec_layered(+ds: List<&2, Cv.Decl>, cfg: List<&2, Cv.Bind>, fam: List<&2, Cv.Ag>, +x: Nat) -> Maybe<&2, Cv.Val>:
  spec_agents(fam, ds, x, spec_last(cfg, ds, Cv.Config{}, x, None{}))

def spec_value.at(m: Maybe<&2, Cv.Decl>, l: Maybe<&2, Cv.Val>) -> Maybe<&2, Cv.Val>:
  match m:
    case None{}:
      None{}
    case Some{d}:
      Some{Maybe.default(&2, Cv.Val, l, spec_init(d))}

# the value of x for the last agent of the chain: what the layers set,
# else its default; none for an undeclared x
def spec_value(+ds: List<&2, Cv.Decl>, cfg: List<&2, Cv.Bind>, fam: List<&2, Cv.Ag>, +x: Nat) -> Maybe<&2, Cv.Val>:
  spec_value.at(spec_find(ds, x), spec_layered(ds, cfg, fam, x))

# x is one of ys
def spec_mem(+x: Nat, ys: List<&2, Nat>) -> Bool:
  match ys:
    case Nil{}:
      False{}
    case y <> rest:
      Bool.or(Nat.is_eq(y, x), spec_mem(x, rest))

def spec_refusal.pick(dup: Bool, good: Bool, i: Nat, next: Cv.Refusal) -> Cv.Refusal:
  match dup:
    case True{}:
      Cv.Twice{i}
    case False{}:
      match good:
        case True{}:
          next
        case False{}:
          Cv.BadInit{i}

# the first declaration of xs whose id is one of seen or of an earlier
# one, or whose default does not have its type
def spec_refusal(xs: List<&2, Cv.Decl>, +seen: List<&2, Nat>) -> Cv.Refusal:
  match xs:
    case Nil{}:
      Cv.Accept{}
    case +d <> rest:
      +i = spec_id(d)
      spec_refusal.pick(spec_mem(i, seen), spec_typed(spec_init(d), spec_ty(d)), i, spec_refusal(rest, List.append(&2, Nat, seen, [i])))

def spec_check.ty(ok: Bool) -> Cv.Check:
  match ok:
    case True{}:
      Cv.CkFine{}
    case False{}:
      Cv.CkType{}

def spec_check.agent(local: Bool, ok: Bool) -> Cv.Check:
  match local:
    case True{}:
      spec_check.ty(ok)
    case False{}:
      Cv.CkGlobal{}

def spec_check.at(m: Maybe<&2, Cv.Decl>, l: Cv.Layer, v: Cv.Val) -> Cv.Check:
  match m:
    case None{}:
      Cv.CkUndeclared{}
    case Some{+d}:
      match l:
        case Cv.Config{}:
          spec_check.ty(spec_typed(v, spec_ty(d)))
        case Cv.Agent{}:
          spec_check.agent(spec_local(d), spec_typed(v, spec_ty(d)))

# the verdict on a set in layer l: undeclared first, then a Global cvar
# in an agent layer, then a value of the wrong type; else valid
def spec_check(+ds: List<&2, Cv.Decl>, l: Cv.Layer, s: Cv.Bind) -> Cv.Check:
  match s:
    case Cv.Bind{i, v}:
      spec_check.at(spec_find(ds, i), l, v)

def spec_tog.flip(x: Nat, m: Maybe<&2, Cv.Val>) -> Cv.Tog:
  match m:
    case None{}:
      Cv.TgNotBool{}
    case Some{v}:
      match v:
        case Cv.VNat{n}:
          Cv.TgNotBool{}
        case Cv.VBool{b}:
          Cv.TgFlip{Cv.Bind{x, Cv.VBool{Bool.not(b)}}}

def spec_tog.agent(local: Bool, +ds: List<&2, Cv.Decl>, cfg: List<&2, Cv.Bind>, fam: List<&2, Cv.Ag>, +x: Nat) -> Cv.Tog:
  match local:
    case True{}:
      spec_tog.flip(x, spec_value(ds, cfg, fam, x))
    case False{}:
      Cv.TgGlobal{}

def spec_tog.at(m: Maybe<&2, Cv.Decl>, l: Cv.Layer, +ds: List<&2, Cv.Decl>, cfg: List<&2, Cv.Bind>, fam: List<&2, Cv.Ag>, +x: Nat) -> Cv.Tog:
  match m:
    case None{}:
      Cv.TgUndeclared{}
    case Some{d}:
      match l:
        case Cv.Config{}:
          spec_tog.flip(x, spec_value(ds, cfg, fam, x))
        case Cv.Agent{}:
          spec_tog.agent(spec_local(d), ds, cfg, fam, x)

# a toggle of x into layer l by the last agent of the chain: undeclared
# first, then a Global cvar in an agent layer; else the set of the
# opposite of the Bool value that agent has (inherited values included),
# or not a Bool
def spec_tog(+ds: List<&2, Cv.Decl>, cfg: List<&2, Cv.Bind>, fam: List<&2, Cv.Ag>, l: Cv.Layer, +x: Nat) -> Cv.Tog:
  spec_tog.at(spec_find(ds, x), l, ds, cfg, fam, x)

def spec_flag.at(m: Maybe<&2, Cv.Decl>, f: Cv.Flag) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{d}:
      spec_flag(d, f)

def spec_keep(ok: Bool, s: Cv.Bind, rest: List<&2, Cv.Bind>) -> List<&2, Cv.Bind>:
  match ok:
    case True{}:
      s <> rest
    case False{}:
      rest

# the sets of ss, in order, of cvars with flag f that count in an agent
# layer
def spec_written(ss: List<&2, Cv.Bind>, +ds: List<&2, Cv.Decl>, +f: Cv.Flag) -> List<&2, Cv.Bind>:
  match ss:
    case Nil{}:
      Nil{}
    case Cv.Bind{+i, +v} <> rest:
      spec_keep(Bool.and(spec_flag.at(spec_find(ds, i), f), spec_valid(ds, Cv.Agent{}, Cv.Bind{i, v})), Cv.Bind{i, v}, spec_written(rest, ds, f))

def spec_doc.src(local: Bool, merged: List<&2, Cv.Bind>, global: List<&2, Cv.Bind>) -> List<&2, Cv.Bind>:
  match local:
    case True{}:
      merged
    case False{}:
      global

def spec_doc.one(x: Nat, m: Maybe<&2, Cv.Val>, rest: List<&2, Cv.Bind>) -> List<&2, Cv.Bind>:
  match m:
    case None{}:
      rest
    case Some{v}:
      Cv.Bind{x, v} <> rest

def spec_doc.first(seen: Bool, x: Nat, m: Maybe<&2, Cv.Val>, rest: List<&2, Cv.Bind>) -> List<&2, Cv.Bind>:
  match seen:
    case True{}:
      rest
    case False{}:
      spec_doc.one(x, m, rest)

# per declaration of xs, in order, whose id is not one of seen nor of an
# earlier one: the last set of its cvar that counts in config, from merged
# for a Local cvar and from global for a Global one
def spec_document(xs: List<&2, Cv.Decl>, +ds: List<&2, Cv.Decl>, +merged: List<&2, Cv.Bind>, +global: List<&2, Cv.Bind>, +seen: List<&2, Nat>) -> List<&2, Cv.Bind>:
  match xs:
    case Nil{}:
      Nil{}
    case +d <> rest:
      +x = spec_id(d)
      spec_doc.first(spec_mem(x, seen), x, spec_last(spec_doc.src(spec_local(d), merged, global), ds, Cv.Config{}, x, None{}), spec_document(rest, ds, merged, global, List.append(&2, Nat, seen, [x])))

# Laws
# ----

# LAW cvar_find_exact: the declaration of a cvar is the first one with its id
# EXCLUDES: a lookup that takes a later duplicate, or misses a declaration
law cvar_find_exact:
  for ds: List<&2, Cv.Decl>
  for +x: Nat
  {Cv.find(ds, x) == spec_find(ds, x) : Maybe<&2, Cv.Decl>}

# LAW cvar_layered_exact: the value the layers set for a cvar is its last set that counts, over config.cfg, then each agent of the family, root first, each one's profile before its own sets; a set counts when its cvar is declared and the value has its type, and in a profile or an agent's sets only for a Local cvar
# EXCLUDES: a layer skipped or read out of order, a first set winning over
#   a later one, a Global cvar set by an agent, a value of the wrong type
#   or of an undeclared cvar counted
law cvar_layered_exact:
  for +ds: List<&2, Cv.Decl>
  for +cfg: List<&2, Cv.Bind>
  for +fam: List<&2, Cv.Ag>
  for +x: Nat
  {Cv.layered(ds, cfg, fam, x) == spec_layered(ds, cfg, fam, x) : Maybe<&2, Cv.Val>}

# LAW cvar_value_exact: the value of a cvar is what the layers set, else its default; an undeclared cvar has none
# EXCLUDES: a default that wins over a set, a value invented for an
#   undeclared cvar, any other layering
law cvar_value_exact:
  for +ds: List<&2, Cv.Decl>
  for +cfg: List<&2, Cv.Bind>
  for +fam: List<&2, Cv.Ag>
  for +x: Nat
  {Cv.value(ds, cfg, fam, x) == spec_value(ds, cfg, fam, x) : Maybe<&2, Cv.Val>}

# LAW cvar_refusal_exact: a registry refuses the first declaration, in order, that repeats an earlier id (named as declared twice) or has a default not of its type (named as a bad default; a declaration that does both is named as declared twice); it accepts a list with neither
# EXCLUDES: a duplicate or a wrong default accepted, a good table
#   refused, the wrong declaration or reason named
law cvar_refusal_exact:
  for +xs: List<&2, Cv.Decl>
  {Cv.refusal(xs) == spec_refusal(xs, Nil{}) : Cv.Refusal}

# LAW cvar_check_exact: a set of an undeclared cvar is refused as undeclared, then one of a Global cvar in an agent layer as Global, then a value of the wrong type; any other is valid
# EXCLUDES: a Global cvar set by an agent, a wrong value accepted, a valid
#   set refused, the wrong reason
law cvar_check_exact:
  for +ds: List<&2, Cv.Decl>
  for l: Cv.Layer
  for +s: Cv.Bind
  {Cv.check(ds, l, s) == spec_check(ds, l, s) : Cv.Check}

# LAW cvar_tog_exact: a toggle of an undeclared cvar is refused, then one of a Global cvar in an agent layer; else it sets the cvar to the opposite of the Bool value the agent has, inherited values included, or is refused when that value is not a Bool
# EXCLUDES: a toggle that ignores the parent's value, flips a non-Bool,
#   flips a Global cvar from an agent, or sets the same value
law cvar_tog_exact:
  for +ds: List<&2, Cv.Decl>
  for +cfg: List<&2, Cv.Bind>
  for +fam: List<&2, Cv.Ag>
  for l: Cv.Layer
  for +x: Nat
  {Cv.tog(ds, cfg, fam, l, x) == spec_tog(ds, cfg, fam, l, x) : Cv.Tog}

# LAW cvar_written_exact: an agent writes (persist) or replicates exactly its sets of cvars with that flag that count in an agent layer, in order
# EXCLUDES: a set lost, invented, reordered, or one of a cvar without the
#   flag, of a Global cvar or with a wrong value written
law cvar_written_exact:
  for ss: List<&2, Cv.Bind>
  for +ds: List<&2, Cv.Decl>
  for +f: Cv.Flag
  {Cv.written(ss, ds, f) == spec_written(ss, ds, f) : List<&2, Cv.Bind>}

# LAW cvar_document_exact: the config sets of a settings document are, per cvar in the order of its first declaration, the last set of it that counts in config, from the merged document when that first declaration is Local and from the global document alone when it is Global; a later declaration of the same id adds nothing
# EXCLUDES: a Global cvar taken from a project (also through a later Local
#   declaration of its id), a value of the wrong type kept, a declaration
#   skipped, repeated or out of order
law cvar_document_exact:
  for +ds: List<&2, Cv.Decl>
  for +merged: List<&2, Cv.Bind>
  for +global: List<&2, Cv.Bind>
  {Cv.document(ds, merged, global) == spec_document(ds, ds, merged, global, Nil{}) : List<&2, Cv.Bind>}

# The model's own terms, pinned
# -----------------------------
# The laws of S4 above read the model's predicates (unique, all_typed,
# typed.at, all_flag, Exp.plain); these pin each to its meaning.

# the ids of ds, in order
def spec_ids(ds: List<&2, Cv.Decl>) -> List<&2, Nat>:
  match ds:
    case Nil{}:
      Nil{}
    case d <> rest:
      spec_id(d) <> spec_ids(rest)

# no id of ds is the id of a later one
def spec_unique(ds: List<&2, Cv.Decl>) -> Bool:
  match ds:
    case Nil{}:
      True{}
    case +d <> +rest:
      Bool.and(Bool.not(spec_mem(spec_id(d), spec_ids(rest))), spec_unique(rest))

# every default of ds has its declaration's type
def spec_all_typed(ds: List<&2, Cv.Decl>) -> Bool:
  match ds:
    case Nil{}:
      True{}
    case +d <> rest:
      Bool.and(spec_typed(spec_init(d), spec_ty(d)), spec_all_typed(rest))

# a value has its declaration's type; no declaration, no value
def spec_typed_at(m: Maybe<&2, Cv.Decl>, v: Maybe<&2, Cv.Val>) -> Bool:
  match m:
    case None{}:
      match v:
        case None{}:
          True{}
        case Some{y}:
          False{}
    case Some{d}:
      match v:
        case None{}:
          False{}
        case Some{y}:
          spec_typed(y, spec_ty(d))

# every set of ss is of a declared cvar with flag f
def spec_all_flag(ss: List<&2, Cv.Bind>, +ds: List<&2, Cv.Decl>, +f: Cv.Flag) -> Bool:
  match ss:
    case Nil{}:
      True{}
    case Cv.Bind{i, v} <> rest:
      Bool.and(spec_flag.at(spec_find(ds, i), f), spec_all_flag(rest, ds, f))

# no command of cs runs an alias (a run, or a run of a missing alias)
def spec_plain(cs: List<&2, Cv.Cmd>) -> Bool:
  match cs:
    case Nil{}:
      True{}
    case c <> rest:
      match c:
        case Cv.CSet{i, v}:
          spec_plain(rest)
        case Cv.CToggle{i}:
          spec_plain(rest)
        case Cv.CRun{n}:
          False{}
        case Cv.CGone{n}:
          False{}

# an expansion is plain: its commands run no alias; an error is plain
def spec_exp_plain(e: Cv.Exp) -> Bool:
  match e:
    case Cv.Flat{cs}:
      spec_plain(cs)
    case Cv.Cycle{n}:
      True{}
    case Cv.Unknown{n}:
      True{}

# LAW cvar_terms_exact: the model's predicates mean what the laws above read them as: unique holds when no declaration's id is the id of a later one, all_typed when every default has its type, typed.at when a value has its declaration's type (and an undeclared cvar has no value), all_flag when every set is of a declared cvar with the flag, Exp.plain when an expansion's commands run no alias (an error expansion is plain)
# EXCLUDES: a constant or input-ignoring predicate that makes
#   cvar_registry_unique, cvar_registry_typed, cvar_value_typed,
#   cvar_written_flagged, alias_expands_fully or bind_press_plain hold
#   vacuously
law cvar_terms_exact:
  for +ds: List<&2, Cv.Decl>
  for m: Maybe<&2, Cv.Decl>
  for v: Maybe<&2, Cv.Val>
  for ss: List<&2, Cv.Bind>
  for +es: List<&2, Cv.Decl>
  for +f: Cv.Flag
  for e: Cv.Exp
  {Cv.unique(ds) == spec_unique(ds) : Bool} & {Cv.all_typed(ds) == spec_all_typed(ds) : Bool} & {Cv.typed.at(m, v) == spec_typed_at(m, v) : Bool} & {Cv.all_flag(ss, es, f) == spec_all_flag(ss, es, f) : Bool} & {Cv.Exp.plain(e) == spec_exp_plain(e) : Bool}
