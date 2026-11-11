# eukhe: the laws of area cvar: the resolution

import Base
import ../../bend/cvar.bend as Cv

# ---- cvar resolution ----

# LAWS (S4, the decisions the compiled core makes for the Rust code; the
# entry bend/ffi_cvar_layers.bend, laws/cvar_layers.bend): the lookup of a
# declaration (R1), the value a layer sets and the value of each cvar (R3,
# R4), which declaration a registry refuses first (R2), the verdict on a
# set (R4) and on a toggle (R5), the sets an agent writes (R6), the config
# sets of a settings document (R7); the requirements R<n> are listed in
# laws/cvar/model.bend. Each decision is stated by a property of its own
# (first match, last set, filter, read back) or tied to another decision
# (a set is fine exactly when the layers count it), never by a copy of the
# model's case split. Every input is free: any declarations (duplicate
# ids, wrong defaults), any config, any family with any profiles and sets
# (wrong types, Global cvars, undeclared ids). The spec helpers read the
# model's lookup Cv.find (pinned by cvar_find_first, cvar_find_absent) and
# its verdicts Cv.check, Cv.layered (pinned below); nothing else of it.

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

# the declaration's default has its type
def spec_good(d: Cv.Decl) -> Bool:
  match d:
    case Cv.Decl{i, t, c, p, r, v}:
      spec_typed(v, t)

def spec_bid(s: Cv.Bind) -> Nat:
  match s:
    case Cv.Bind{i, v}:
      i

def spec_bval(s: Cv.Bind) -> Cv.Val:
  match s:
    case Cv.Bind{i, v}:
      v

# no declaration of ds has id x
def spec_no_id(ds: List<&2, Cv.Decl>, +x: Nat) -> Bool:
  match ds:
    case Nil{}:
      True{}
    case d <> rest:
      Bool.and(Bool.not(Nat.is_eq(spec_id(d), x)), spec_no_id(rest, x))

# Lookup (R1)
# -----------

# LAW cvar_find_first: the declaration of a cvar is its first declaration: in pre ++ [d] ++ post, where no declaration of pre has d's id, the lookup of that id gives d, whatever post holds
# EXCLUDES: a lookup that takes a later duplicate, skips a matching
#   declaration, or stops at the first declaration whatever its id
law cvar_find_first:
  for +pre: List<&2, Cv.Decl>
  for +d: Cv.Decl
  for +post: List<&2, Cv.Decl>
  for fresh: {spec_no_id(pre, spec_id(d)) == True{} : Bool}
  {Cv.find(List.append(&2, Cv.Decl, pre, d <> post), spec_id(d)) == Some{d} : Maybe<&2, Cv.Decl>}

# LAW cvar_find_absent: a cvar no declaration has is undeclared: the lookup gives none
# EXCLUDES: a declaration invented for an id nobody declared (the first
#   or last declaration as a default)
law cvar_find_absent:
  for +ds: List<&2, Cv.Decl>
  for +x: Nat
  for none: {spec_no_id(ds, x) == True{} : Bool}
  {Cv.find(ds, x) == None{} : Maybe<&2, Cv.Decl>}

# Layers (R3, R4)
# ---------------

# a set counts in layer l: its cvar is declared, the value has the
# declaration's type, and in an agent layer (a profile, an agent's own
# sets) the cvar is Local (R4: a Global cvar has one value per family)
def spec_counts.at(m: Maybe<&2, Cv.Decl>, l: Cv.Layer, v: Cv.Val) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{+d}:
      match l:
        case Cv.Config{}:
          spec_typed(v, spec_ty(d))
        case Cv.Agent{}:
          Bool.and(spec_typed(v, spec_ty(d)), spec_local(d))

def spec_counts(+ds: List<&2, Cv.Decl>, l: Cv.Layer, +s: Cv.Bind) -> Bool:
  spec_counts.at(Cv.find(ds, spec_bid(s)), l, spec_bval(s))

# a set and the layer it comes from
type LSet is Data:
  LSet{layer: Cv.Layer, set: Cv.Bind}

# the sets ss, each with the layer it comes from
def spec_tag(+l: Cv.Layer, ss: List<&2, Cv.Bind>) -> List<&2, LSet>:
  match ss:
    case Nil{}:
      Nil{}
    case s <> rest:
      LSet{l, s} <> spec_tag(l, rest)

# every set of a family chain, root first, each agent's profile before its
# own sets, all in agent layers
def spec_flat_fam(fam: List<&2, Cv.Ag>) -> List<&2, LSet>:
  match fam:
    case Nil{}:
      Nil{}
    case Cv.Ag{p, s} <> rest:
      List.append(&2, LSet, spec_tag(Cv.Agent{}, p), List.append(&2, LSet, spec_tag(Cv.Agent{}, s), spec_flat_fam(rest)))

# every set, lowest layer first: config.cfg, then the family chain
def spec_flat(cfg: List<&2, Cv.Bind>, fam: List<&2, Cv.Ag>) -> List<&2, LSet>:
  List.append(&2, LSet, spec_tag(Cv.Config{}, cfg), spec_flat_fam(fam))

def spec_latest.or(later: Maybe<&2, Cv.Val>, here: Bool, v: Cv.Val) -> Maybe<&2, Cv.Val>:
  match later:
    case Some{w}:
      Some{w}
    case None{}:
      match here:
        case True{}:
          Some{v}
        case False{}:
          None{}

def spec_latest.at(ls: LSet, later: Maybe<&2, Cv.Val>, +ds: List<&2, Cv.Decl>, +x: Nat) -> Maybe<&2, Cv.Val>:
  match ls:
    case LSet{l, +s}:
      spec_latest.or(later, Bool.and(Nat.is_eq(spec_bid(s), x), spec_counts(ds, l, s)), spec_bval(s))

# the value of the latest set of x that counts, if any: a later set wins,
# so the sets after a set are asked first
def spec_latest(ts: List<&2, LSet>, +ds: List<&2, Cv.Decl>, +x: Nat) -> Maybe<&2, Cv.Val>:
  match ts:
    case Nil{}:
      None{}
    case t <> rest:
      spec_latest.at(t, spec_latest(rest, ds, x), ds, x)

# LAW cvar_layered_last: the value the layers set for a cvar is the value of its latest set that counts, over every set of config.cfg, then of each agent of the family chain, root first, each one's profile before its own sets; a set counts when its cvar is declared (Cv.find) and the value has the declaration's type, and in a profile or an agent's own sets only for a Local cvar; none when no set counts
# EXCLUDES: a layer skipped or read out of order, a first set winning over
#   a later one, a Global cvar set by an agent, a value of the wrong type
#   or of an undeclared cvar counted, a set of another cvar read
law cvar_layered_last:
  for +ds: List<&2, Cv.Decl>
  for +cfg: List<&2, Cv.Bind>
  for +fam: List<&2, Cv.Ag>
  for +x: Nat
  {Cv.layered(ds, cfg, fam, x) == spec_latest(spec_flat(cfg, fam), ds, x) : Maybe<&2, Cv.Val>}

# the value of a cvar of declaration m whose layers set l: none for an
# undeclared cvar, else what the layers set, else the default
def spec_value.at(m: Maybe<&2, Cv.Decl>, l: Maybe<&2, Cv.Val>) -> Maybe<&2, Cv.Val>:
  match m:
    case None{}:
      None{}
    case Some{d}:
      Some{Maybe.default(&2, Cv.Val, l, spec_init(d))}

# LAW cvar_value_from_layers: the value of a cvar for the last agent of the family is what the layers set (Cv.layered, cvar_layered_last), else the default of its declaration (Cv.find); an undeclared cvar has none
# EXCLUDES: a default that wins over a set, a value invented for an
#   undeclared cvar, a value that differs from the layered value the entry
#   reports beside it, the default of a later declaration
law cvar_value_from_layers:
  for +ds: List<&2, Cv.Decl>
  for +cfg: List<&2, Cv.Bind>
  for +fam: List<&2, Cv.Ag>
  for +x: Nat
  {Cv.value(ds, cfg, fam, x) == spec_value.at(Cv.find(ds, x), Cv.layered(ds, cfg, fam, x)) : Maybe<&2, Cv.Val>}

# Verdicts on a set (R4)
# ----------------------

def spec_ck_fine(c: Cv.Check) -> Bool:
  match c:
    case Cv.CkUndeclared{}:
      False{}
    case Cv.CkGlobal{}:
      False{}
    case Cv.CkType{}:
      False{}
    case Cv.CkFine{}:
      True{}

def spec_ck_undeclared(c: Cv.Check) -> Bool:
  match c:
    case Cv.CkUndeclared{}:
      True{}
    case Cv.CkGlobal{}:
      False{}
    case Cv.CkType{}:
      False{}
    case Cv.CkFine{}:
      False{}

def spec_ck_global(c: Cv.Check) -> Bool:
  match c:
    case Cv.CkUndeclared{}:
      False{}
    case Cv.CkGlobal{}:
      True{}
    case Cv.CkType{}:
      False{}
    case Cv.CkFine{}:
      False{}

# config.cfg holding the one set s when l is Config
def spec_one_cfg(l: Cv.Layer, s: Cv.Bind) -> List<&2, Cv.Bind>:
  match l:
    case Cv.Config{}:
      [s]
    case Cv.Agent{}:
      Nil{}

# one agent whose own sets are the one set s when l is Agent
def spec_one_fam(l: Cv.Layer, s: Cv.Bind) -> List<&2, Cv.Ag>:
  match l:
    case Cv.Config{}:
      Nil{}
    case Cv.Agent{}:
      [Cv.Ag{Nil{}, [s]}]

# layer l is an agent layer and m declares a Global cvar
def spec_global_in(l: Cv.Layer, m: Maybe<&2, Cv.Decl>) -> Bool:
  match l:
    case Cv.Config{}:
      False{}
    case Cv.Agent{}:
      match m:
        case None{}:
          False{}
        case Some{d}:
          Bool.not(spec_local(d))

# LAW cvar_check_fine: the verdict on a set in a layer is valid exactly when that set, alone in that layer (config.cfg, or the own sets of a one-agent family), sets the cvar's value (Cv.layered, cvar_layered_last)
# EXCLUDES: a set accepted that the layers then ignore (a Global cvar set
#   by an agent, a wrong type, an undeclared cvar), a set refused that
#   the layers would count
law cvar_check_fine:
  for +ds: List<&2, Cv.Decl>
  for +l: Cv.Layer
  for +s: Cv.Bind
  {spec_ck_fine(Cv.check(ds, l, s)) == Maybe.is_some(&2, Cv.Val, Cv.layered(ds, spec_one_cfg(l, s), spec_one_fam(l, s), spec_bid(s))) : Bool}

# LAW cvar_check_undeclared: the verdict on a set is "undeclared" exactly when no declaration has its cvar (Cv.find gives none)
# EXCLUDES: a declared cvar refused as undeclared, an undeclared one
#   refused for another reason
law cvar_check_undeclared:
  for +ds: List<&2, Cv.Decl>
  for l: Cv.Layer
  for +s: Cv.Bind
  {spec_ck_undeclared(Cv.check(ds, l, s)) == Bool.not(Maybe.is_some(&2, Cv.Decl, Cv.find(ds, spec_bid(s)))) : Bool}

# LAW cvar_check_global: the verdict on a set is "Global" exactly when the set is in an agent layer and its cvar's declaration (Cv.find) is Global, whatever the value's type (Global is named before a wrong type); with cvar_check_fine and cvar_check_undeclared every other refusal is "wrong type"
# EXCLUDES: a Global cvar's set in an agent layer refused as a wrong type
#   or accepted, a set in config.cfg refused as Global
law cvar_check_global:
  for +ds: List<&2, Cv.Decl>
  for +l: Cv.Layer
  for +s: Cv.Bind
  {spec_ck_global(Cv.check(ds, l, s)) == spec_global_in(l, Cv.find(ds, spec_bid(s))) : Bool}

# Verdicts on a toggle (R5)
# -------------------------

# LAW cvar_tog_undeclared: a toggle of a cvar no declaration has (Cv.find gives none) is refused as undeclared, in any layer
# EXCLUDES: a toggle of an undeclared cvar that sets anything
law cvar_tog_undeclared:
  for +ds: List<&2, Cv.Decl>
  for +cfg: List<&2, Cv.Bind>
  for +fam: List<&2, Cv.Ag>
  for l: Cv.Layer
  for +x: Nat
  for none: {Cv.find(ds, x) == None{} : Maybe<&2, Cv.Decl>}
  {Cv.tog(ds, cfg, fam, l, x) == Cv.TgUndeclared{} : Cv.Tog}

# LAW cvar_tog_global: a toggle into an agent layer of a cvar whose declaration (Cv.find) is Global is refused as Global, whatever its value
# EXCLUDES: an agent that flips a Global cvar (a value the layers then
#   ignore), a Global toggle refused as not a Bool
law cvar_tog_global:
  for +ds: List<&2, Cv.Decl>
  for +cfg: List<&2, Cv.Bind>
  for +fam: List<&2, Cv.Ag>
  for +x: Nat
  for +d: Cv.Decl
  for found: {Cv.find(ds, x) == Some{d} : Maybe<&2, Cv.Decl>}
  for global: {spec_local(d) == False{} : Bool}
  {Cv.tog(ds, cfg, fam, Cv.Agent{}, x) == Cv.TgGlobal{} : Cv.Tog}

# LAW cvar_tog_flips: a toggle the layer allows (not an agent layer with a Global cvar) of a cvar whose value for the last agent of the family (Cv.value, inherited values included) is the Bool b is the set of the cvar to not b
# EXCLUDES: a toggle that ignores the parent's value, sets the same value,
#   or sets another cvar
law cvar_tog_flips:
  for +ds: List<&2, Cv.Decl>
  for +cfg: List<&2, Cv.Bind>
  for +fam: List<&2, Cv.Ag>
  for +l: Cv.Layer
  for +x: Nat
  for +b: Bool
  for allowed: {spec_global_in(l, Cv.find(ds, x)) == False{} : Bool}
  for val: {Cv.value(ds, cfg, fam, x) == Some{Cv.VBool{b}} : Maybe<&2, Cv.Val>}
  {Cv.tog(ds, cfg, fam, l, x) == Cv.TgFlip{Cv.Bind{x, Cv.VBool{Bool.not(b)}}} : Cv.Tog}

# LAW cvar_tog_not_bool: a toggle the layer allows of a cvar whose value for the last agent of the family is a Nat is refused as not a Bool
# EXCLUDES: a Nat cvar flipped or set to a Bool
law cvar_tog_not_bool:
  for +ds: List<&2, Cv.Decl>
  for +cfg: List<&2, Cv.Bind>
  for +fam: List<&2, Cv.Ag>
  for +l: Cv.Layer
  for +x: Nat
  for +n: Nat
  for allowed: {spec_global_in(l, Cv.find(ds, x)) == False{} : Bool}
  for val: {Cv.value(ds, cfg, fam, x) == Some{Cv.VNat{n}} : Maybe<&2, Cv.Val>}
  {Cv.tog(ds, cfg, fam, l, x) == Cv.TgNotBool{} : Cv.Tog}

# The sets an agent writes (R6)
# -----------------------------

# the declaration m has flag f
def spec_has_flag(m: Maybe<&2, Cv.Decl>, f: Cv.Flag) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{d}:
      spec_flag(d, f)

def spec_keep_if(ok: Bool, s: Cv.Bind) -> List<&2, Cv.Bind>:
  match ok:
    case True{}:
      [s]
    case False{}:
      Nil{}

# LAW cvar_written_append: the sets an agent writes (persist) or replicates are chosen set by set: those of two runs of sets one after the other are those of the first, then those of the second
# EXCLUDES: a set lost, invented, reordered or written twice, a choice that
#   depends on the other sets
law cvar_written_append:
  for +a: List<&2, Cv.Bind>
  for +b: List<&2, Cv.Bind>
  for +ds: List<&2, Cv.Decl>
  for +f: Cv.Flag
  {Cv.written(List.append(&2, Cv.Bind, a, b), ds, f) == List.append(&2, Cv.Bind, Cv.written(a, ds, f), Cv.written(b, ds, f)) : List<&2, Cv.Bind>}

# LAW cvar_written_one: one set is written (or replicated) exactly when its cvar's declaration (Cv.find) has that flag and the verdict on the set in an agent layer is valid (Cv.check, cvar_check_fine)
# EXCLUDES: a set of a cvar without the flag, of a Global cvar, of an
#   undeclared cvar or with a wrong value written, a valid flagged set lost
law cvar_written_one:
  for +s: Cv.Bind
  for +ds: List<&2, Cv.Decl>
  for +f: Cv.Flag
  {Cv.written([s], ds, f) == spec_keep_if(Bool.and(spec_has_flag(Cv.find(ds, spec_bid(s)), f), spec_ck_fine(Cv.check(ds, Cv.Agent{}, s))), s) : List<&2, Cv.Bind>}

# The config sets of a settings document (R7)
# -------------------------------------------

# where the cvar of declaration m takes its config value from: the merged
# document for a Local cvar, the global one for a Global cvar (a project
# never sets a Global cvar), nothing for an undeclared one
def spec_doc_src.pick(local: Bool, merged: List<&2, Cv.Bind>, global: List<&2, Cv.Bind>) -> List<&2, Cv.Bind>:
  match local:
    case True{}:
      merged
    case False{}:
      global

def spec_doc_src(m: Maybe<&2, Cv.Decl>, merged: List<&2, Cv.Bind>, global: List<&2, Cv.Bind>) -> List<&2, Cv.Bind>:
  match m:
    case None{}:
      Nil{}
    case Some{d}:
      spec_doc_src.pick(spec_local(d), merged, global)

def spec_drop_nat.pick(hit: Bool, y: Nat, rest: List<&2, Nat>) -> List<&2, Nat>:
  match hit:
    case True{}:
      rest
    case False{}:
      y <> rest

# xs without x
def spec_drop_nat(xs: List<&2, Nat>, +x: Nat) -> List<&2, Nat>:
  match xs:
    case Nil{}:
      Nil{}
    case +y <> rest:
      spec_drop_nat.pick(Nat.is_eq(x, y), y, spec_drop_nat(rest, x))

# the declared ids, in the order of their first declarations, each once
def spec_first_ids(ds: List<&2, Cv.Decl>) -> List<&2, Nat>:
  match ds:
    case Nil{}:
      Nil{}
    case d <> rest:
      +i = spec_id(d)
      i <> spec_drop_nat(spec_first_ids(rest), i)

def spec_doc_one(x: Nat, m: Maybe<&2, Cv.Val>, rest: List<&2, Cv.Bind>) -> List<&2, Cv.Bind>:
  match m:
    case None{}:
      rest
    case Some{v}:
      Cv.Bind{x, v} <> rest

# per cvar of xs, in order: the set of the value its source alone gives
# as config.cfg, when it gives one
def spec_doc_of(+ds: List<&2, Cv.Decl>, +merged: List<&2, Cv.Bind>, +global: List<&2, Cv.Bind>, xs: List<&2, Nat>) -> List<&2, Cv.Bind>:
  match xs:
    case Nil{}:
      Nil{}
    case +x <> rest:
      spec_doc_one(x, Cv.layered(ds, spec_doc_src(Cv.find(ds, x), merged, global), Nil{}, x), spec_doc_of(ds, merged, global, rest))

# LAW cvar_document_per_cvar: the config sets of a settings document are, per declared cvar in the order of its first declaration (each id once), the set of the value its source alone gives when read as config.cfg (Cv.layered with no family), and nothing when it gives none; the source is the merged document for a cvar whose declaration (Cv.find, the first) is Local and the global document alone for a Global one
# EXCLUDES: a Global cvar taken from a project (also through a later Local
#   declaration of its id), a cvar set twice or out of declaration order,
#   a value of the wrong type or of an undeclared cvar written, a set lost
law cvar_document_per_cvar:
  for +ds: List<&2, Cv.Decl>
  for +merged: List<&2, Cv.Bind>
  for +global: List<&2, Cv.Bind>
  {Cv.document(ds, merged, global) == spec_doc_of(ds, merged, global, spec_first_ids(ds)) : List<&2, Cv.Bind>}

# The stores of the config layer
# ------------------------------
# Cv.stores: settings.json, then the global config.cfg, then the
# project's config.cfg, read with an empty family; Cv.save: the MODEL of a
# write of a setting into the global config.cfg (every earlier set of the
# cvar dropped, the new set last). The Rust writer does not call Cv.save:
# it replaces the first line that sets the cvar and drops the others (the
# same sets value-wise: only the sets of one cvar compete in a layer), so
# these laws are about the model write, not the shipped writer (R8).
# Every input is free.

# LAW cvar_save_reads_back: after the model write Cv.save of a set valid in config.cfg into the global config.cfg, the config layer (Cv.stores, read by Cv.layered with no family) reads the written value, whatever settings.json and the global config.cfg held, provided the project's config.cfg sets no valid value of the cvar
# EXCLUDES: a write into a store a higher store shadows (the old
#   settings.json write), a stale earlier set of the cvar surviving the
#   write
law cvar_save_reads_back:
  for +ds: List<&2, Cv.Decl>
  for +doc: List<&2, Cv.Bind>
  for +g: List<&2, Cv.Bind>
  for +p: List<&2, Cv.Bind>
  for +x: Nat
  for +v: Cv.Val
  for ok: {Cv.valid(ds, Cv.Config{}, Cv.Bind{x, v}) == True{} : Bool}
  for quiet: {Cv.layer(p, ds, Cv.Config{}, x, None{}) == None{} : Maybe<&2, Cv.Val>}
  {Cv.layered(ds, Cv.stores(doc, Cv.save(g, Cv.Bind{x, v}), p), Nil{}, x) == Some{v} : Maybe<&2, Cv.Val>}

# LAW cvar_save_keeps_others: the model write Cv.save of one cvar into the global config.cfg leaves the layered config value of every other cvar as it was
# EXCLUDES: a write that drops, adds or reorders the sets of another cvar
#   (a whole-file rewrite that loses lines, a drop by the wrong id)
law cvar_save_keeps_others:
  for +ds: List<&2, Cv.Decl>
  for +doc: List<&2, Cv.Bind>
  for +g: List<&2, Cv.Bind>
  for +p: List<&2, Cv.Bind>
  for +x: Nat
  for +v: Cv.Val
  for +y: Nat
  for +ne: {Nat.is_eq(x, y) == False{} : Bool}
  {Cv.layered(ds, Cv.stores(doc, Cv.save(g, Cv.Bind{x, v}), p), Nil{}, y) == Cv.layered(ds, Cv.stores(doc, g, p), Nil{}, y) : Maybe<&2, Cv.Val>}

# LAW cvar_save_project_wins: when the project's config.cfg sets a valid value of the cvar, the config layer after the model write Cv.save of a valid set reads the project's value
# EXCLUDES: a global write that shadows the project's config.cfg, an
#   override reported from settings.json or the old global value
law cvar_save_project_wins:
  for +ds: List<&2, Cv.Decl>
  for +doc: List<&2, Cv.Bind>
  for +g: List<&2, Cv.Bind>
  for +p: List<&2, Cv.Bind>
  for +x: Nat
  for +v: Cv.Val
  for +w: Cv.Val
  for ok: {Cv.valid(ds, Cv.Config{}, Cv.Bind{x, v}) == True{} : Bool}
  for set: {Cv.layer(p, ds, Cv.Config{}, x, None{}) == Some{w} : Maybe<&2, Cv.Val>}
  {Cv.layered(ds, Cv.stores(doc, Cv.save(g, Cv.Bind{x, v}), p), Nil{}, x) == Some{w} : Maybe<&2, Cv.Val>}

def spec_sets_of.pick(hit: Bool, s: Cv.Bind, rest: List<&2, Cv.Bind>) -> List<&2, Cv.Bind>:
  match hit:
    case True{}:
      s <> rest
    case False{}:
      rest

# the sets of x in ss, in order
def spec_sets_of(ss: List<&2, Cv.Bind>, +x: Nat) -> List<&2, Cv.Bind>:
  match ss:
    case Nil{}:
      Nil{}
    case Cv.Bind{+i, +v} <> rest:
      spec_sets_of.pick(Nat.is_eq(i, x), Cv.Bind{i, v}, spec_sets_of(rest, x))

# LAW cvar_save_once: after the model write Cv.save, the global config.cfg (the list Cv.save returns) sets the cvar exactly once, to the written value
# EXCLUDES: a write appended after the old sets of the cvar (a stale set
#   left in the file), a write lost or written twice
law cvar_save_once:
  for +g: List<&2, Cv.Bind>
  for +x: Nat
  for +v: Cv.Val
  {spec_sets_of(Cv.save(g, Cv.Bind{x, v}), x) == [Cv.Bind{x, v}] : List<&2, Cv.Bind>}

# LAW cvar_save_example: anchor (the user's report): settings.json sets the thinking level low (1), the global config.cfg max (2); the model write Cv.save of 3 into the global config.cfg reads 3, while the old write into settings.json reads the config.cfg's 2: the choice did not stick
# EXCLUDES: a write path that a lower store's set shadows, a vacuous
#   cvar_save_reads_back
law cvar_save_example:
  {Cv.layered([Cv.Decl{0n, Cv.TNat{}, Cv.Local{}, True{}, True{}, Cv.VNat{0n}}], Cv.stores([Cv.Bind{0n, Cv.VNat{1n}}], Cv.save([Cv.Bind{0n, Cv.VNat{2n}}], Cv.Bind{0n, Cv.VNat{3n}}), Nil{}), Nil{}, 0n) == Some{Cv.VNat{3n}} : Maybe<&2, Cv.Val>} & {Cv.layered([Cv.Decl{0n, Cv.TNat{}, Cv.Local{}, True{}, True{}, Cv.VNat{0n}}], Cv.stores([Cv.Bind{0n, Cv.VNat{3n}}], [Cv.Bind{0n, Cv.VNat{2n}}], Nil{}), Nil{}, 0n) == Some{Cv.VNat{2n}} : Maybe<&2, Cv.Val>}
