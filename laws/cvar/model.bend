# eukhe: the laws of area cvar: the model (S4)

import Base
import ../../bend/cvar.bend as Cv

# (S4) Settings as console variables
# ----------------------------------
# the model in bend/cvar.bend. Every input is free:
# any declarations (duplicate ids, wrong defaults), any config.cfg, any
# family of agents with any profiles and sets (wrong types, Global cvars,
# undeclared ids), any alias table.
#
# Requirements (stated: bend/cvar.bend header, crates/eukhe-bend/src/
# rules/cvar.rs and cvar_layers.rs, crates/eukhe-core/src/settings/cvar;
# laws/cvar/resolution.bend, whole.bend and entry.bend cite them):
# R1  a cvar's declaration is its first declaration; the registry keeps,
#     of each id, its first declaration whose default has its type, in
#     order, and nothing else.
# R2  the registry's refusal names the first declaration it drops and why
#     (an id declared before; else a default of the wrong type).
# R3  values come in layers, a later layer winning: default < config.cfg
#     < each agent of the family chain, root first, its profile, then its
#     own sets; a subagent starts from its parent's values.
# R4  a set counts only for a declared cvar, with a value of its type,
#     and in an agent's layers only for a Local cvar (a Global cvar has
#     one value per family); the verdict on a set says which rule fails.
# R5  a toggle flips the Bool value the agent has (inherited included)
#     and nothing else; its verdict says why it cannot.
# R6  an agent writes (persist) or replicates exactly its sets that count
#     of cvars with that flag, in order.
# R7  the config sets of a settings document: per declared cvar, in the
#     order of its first declaration, the value its source sets (the
#     merged document for a Local cvar, the global one for a Global cvar).
# R8  the model write Cv.save of a setting into the global config.cfg
#     reads back, keeps every other cvar, and leaves one set of the cvar.
# R9  an expansion runs a run's alias body (the first alias of the name),
#     keeps every set and toggle, in order; a missing alias is unknown, a
#     nest deeper than the table a cycle; the first error stops it.
# R10 a key press runs the commands of the key's first bind, else nothing.
# R11 the entries bend/ffi_cvar.bend and bend/ffi_cvar_layers.bend answer
#     every input as their grammar says (laws/cvar/entry.bend; R1, R2 of
#     laws/cvar_layers.bend).

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
