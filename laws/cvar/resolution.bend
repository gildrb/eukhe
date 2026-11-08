# eukhe: the laws of area cvar: the resolution

import Base
import ../../bend/cvar.bend as Cv

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

# The stores of the config layer
# ------------------------------
# Cv.stores: settings.json, then the global config.cfg, then the
# project's config.cfg, read with an empty family; Cv.save: a write of a
# setting into the global config.cfg (every earlier set of the cvar
# dropped). Every input is free.

# LAW cvar_save_reads_back: a write followed by a read returns the written value, whatever settings.json and the global config.cfg held; only the project's config.cfg can override it
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

# LAW cvar_save_keeps_others: a write of one setting leaves the value of every other setting as it was
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

# LAW cvar_save_project_wins: when the project's config.cfg sets the cvar, a write reads back the project's value: the one override a write reports
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

# LAW cvar_save_once: after a write, the global config.cfg sets the cvar exactly once, to the written value
# EXCLUDES: a write appended after the old sets of the cvar (a stale set
#   left in the file), a write lost or written twice
law cvar_save_once:
  for +g: List<&2, Cv.Bind>
  for +x: Nat
  for +v: Cv.Val
  {spec_sets_of(Cv.save(g, Cv.Bind{x, v}), x) == [Cv.Bind{x, v}] : List<&2, Cv.Bind>}

# LAW cvar_save_example: anchor (the user's report): settings.json sets the thinking level low (1), the global config.cfg max (2); a write of 3 into the global config.cfg reads 3, while the old write into settings.json reads the config.cfg's 2: the choice did not stick
# EXCLUDES: a write path that a lower store's set shadows, a vacuous
#   cvar_save_reads_back
law cvar_save_example:
  {Cv.layered([Cv.Decl{0n, Cv.TNat{}, Cv.Local{}, True{}, True{}, Cv.VNat{0n}}], Cv.stores([Cv.Bind{0n, Cv.VNat{1n}}], Cv.save([Cv.Bind{0n, Cv.VNat{2n}}], Cv.Bind{0n, Cv.VNat{3n}}), Nil{}), Nil{}, 0n) == Some{Cv.VNat{3n}} : Maybe<&2, Cv.Val>} & {Cv.layered([Cv.Decl{0n, Cv.TNat{}, Cv.Local{}, True{}, True{}, Cv.VNat{0n}}], Cv.stores([Cv.Bind{0n, Cv.VNat{3n}}], [Cv.Bind{0n, Cv.VNat{2n}}], Nil{}), Nil{}, 0n) == Some{Cv.VNat{2n}} : Maybe<&2, Cv.Val>}

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
