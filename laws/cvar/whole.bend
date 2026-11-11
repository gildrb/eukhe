# eukhe: the laws of area cvar, section whole: the registry, its refusal,
# a toggle of the model (bend/cvar.bend), and the model's predicates

import Base
import ../../bend/cvar.bend as Cv
import ./resolution.bend as Cvar

# LAWS (S4; R1, R2, R5 of laws/cvar/model.bend): the registry keeps, of
# each id, its first declaration whose default has its type, in order
# (cvar_registry_sublist, cvar_registry_keeps_first, with
# cvar_registry_unique and cvar_registry_typed of laws/cvar/model.bend);
# its refusal names the first declaration that repeats an id or has a
# wrong default; a toggle of the model flips exactly the toggled cvar's
# Bool value, when its flip counts for the agent. Every input is free: any
# declarations (duplicate ids, wrong defaults), any config.cfg, any family
# of agents with any profiles and sets.

# The registry (R1)
# -----------------

def spec_pick.at(k: Bool, d: Cv.Decl, rest: List<&2, Cv.Decl>) -> List<&2, Cv.Decl>:
  match k:
    case True{}:
      d <> rest
    case False{}:
      rest

# the declarations of xs whose flag in keep is True, in order (no flag:
# not kept)
def spec_pick(xs: List<&2, Cv.Decl>, keep: List<&2, Bool>) -> List<&2, Cv.Decl>:
  match xs:
    case Nil{}:
      Nil{}
    case d <> rest:
      match keep:
        case Nil{}:
          Nil{}
        case k <> ks:
          spec_pick.at(k, d, spec_pick(rest, ks))

# LAW cvar_registry_sublist: the registry of a declaration list is some of its declarations, in their order: nothing invented, reordered or repeated
# EXCLUDES: a declaration invented, changed, repeated or moved by the
#   registry (with cvar_registry_keeps_first: an empty registry)
law cvar_registry_sublist:
  for xs: List<&2, Cv.Decl>
  exs keep: List<&2, Bool>
  {spec_pick(xs, keep) == Cv.registry(xs) : List<&2, Cv.Decl>}

# no declaration of ds with id x has a default of its type
def spec_no_good_id(ds: List<&2, Cv.Decl>, +x: Nat) -> Bool:
  match ds:
    case Nil{}:
      True{}
    case +d <> rest:
      Bool.and(Bool.not(Bool.and(Nat.is_eq(Cvar.spec_id(d), x), Cvar.spec_good(d))), spec_no_good_id(rest, x))

# LAW cvar_registry_keeps_first: the registry keeps the first declaration of an id whose default has its type: in pre ++ [d] ++ post, where d's default has its type and no declaration of pre with d's id has a default of its type, the registry's declaration of that id (Cv.find, cvar_find_first) is d, whatever post holds
# EXCLUDES: an empty registry, a good declaration dropped, a later
#   duplicate kept over the first, a good declaration dropped because an
#   earlier one of its id had a wrong default
law cvar_registry_keeps_first:
  for +pre: List<&2, Cv.Decl>
  for +d: Cv.Decl
  for +post: List<&2, Cv.Decl>
  for good: {Cvar.spec_good(d) == True{} : Bool}
  for first: {spec_no_good_id(pre, Cvar.spec_id(d)) == True{} : Bool}
  {Cv.find(Cv.registry(List.append(&2, Cv.Decl, pre, d <> post)), Cvar.spec_id(d)) == Some{d} : Maybe<&2, Cv.Decl>}

# The registry's refusal (R2)
# ---------------------------

# every declaration of xs has a default of its type and an id no later
# one has
def spec_whole(xs: List<&2, Cv.Decl>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case +d <> +rest:
      Bool.and(Cvar.spec_good(d), Bool.and(Cvar.spec_no_id(rest, Cvar.spec_id(d)), spec_whole(rest)))

# LAW cvar_refusal_accepts: a declaration list whose ids are distinct and whose defaults have their types is accepted whole
# EXCLUDES: a good table refused
law cvar_refusal_accepts:
  for +xs: List<&2, Cv.Decl>
  for whole: {spec_whole(xs) == True{} : Bool}
  {Cv.refusal(xs) == Cv.Accept{} : Cv.Refusal}

# why the declaration of id i is dropped: its id is declared before
# (free: False), else its default has the wrong type
def spec_reason(free: Bool, i: Nat) -> Cv.Refusal:
  match free:
    case True{}:
      Cv.BadInit{i}
    case False{}:
      Cv.Twice{i}

# LAW cvar_refusal_first_drop: the refusal names the first declaration that repeats an earlier id or has a default not of its type: in pre ++ [d] ++ post, where pre's ids are distinct and its defaults have their types and d repeats an id of pre or has a wrong default, the refusal is "declared twice" with d's id when pre declares d's id (also when d's default is wrong too), else "bad default" with d's id, whatever post holds
# EXCLUDES: a duplicate or a wrong default accepted, a later bad
#   declaration named, the wrong reason
law cvar_refusal_first_drop:
  for +pre: List<&2, Cv.Decl>
  for +d: Cv.Decl
  for +post: List<&2, Cv.Decl>
  for whole: {spec_whole(pre) == True{} : Bool}
  for drop: {Bool.and(Cvar.spec_no_id(pre, Cvar.spec_id(d)), Cvar.spec_good(d)) == False{} : Bool}
  {Cv.refusal(List.append(&2, Cv.Decl, pre, d <> post)) == spec_reason(Cvar.spec_no_id(pre, Cvar.spec_id(d)), Cvar.spec_id(d)) : Cv.Refusal}

# A toggle (R5)
# -------------

def spec_toggled.pick(go: Bool, b: Bool, v: Maybe<&2, Cv.Val>) -> Maybe<&2, Cv.Val>:
  match go:
    case True{}:
      Some{Cv.VBool{Bool.not(b)}}
    case False{}:
      v

def spec_toggled.at(eq: Bool, m: Maybe<&2, Cv.Decl>, w: Cv.Val) -> Maybe<&2, Cv.Val>:
  match w:
    case Cv.VNat{n}:
      Some{Cv.VNat{n}}
    case Cv.VBool{+b}:
      spec_toggled.pick(Bool.and(eq, Cvar.spec_counts.at(m, Cv.Agent{}, Cv.VBool{Bool.not(b)})), b, Some{Cv.VBool{b}})

# a value v of a cvar after a toggle: when it is the toggled cvar (eq),
# its value is the Bool b and the set of not b counts for an agent under
# its declaration m, the value is not b; else v
def spec_toggled(eq: Bool, m: Maybe<&2, Cv.Decl>, v: Maybe<&2, Cv.Val>) -> Maybe<&2, Cv.Val>:
  match v:
    case None{}:
      None{}
    case Some{w}:
      spec_toggled.at(eq, m, w)

# LAW cvar_toggle_values: after agent a, the last of the family chain, toggles x, every cvar y keeps the value it had, except x itself when its value is a Bool b and a set of not b counts for an agent (x declared, Local, of type Bool): x then has not b; inherited values included
# EXCLUDES: a toggle that leaves the agent as it was, sets the same value,
#   ignores the parent's value, flips a non-Bool, changes another cvar
law cvar_toggle_values:
  for +ds: List<&2, Cv.Decl>
  for +cfg: List<&2, Cv.Bind>
  for +fam: List<&2, Cv.Ag>
  for +a: Cv.Ag
  for +x: Nat
  for +y: Nat
  {Cv.value(ds, cfg, List.append(&2, Cv.Ag, fam, [Cv.toggle(ds, cfg, fam, a, x)]), y) == spec_toggled(Nat.is_eq(x, y), Cv.find(ds, x), Cv.value(ds, cfg, List.append(&2, Cv.Ag, fam, [a]), y)) : Maybe<&2, Cv.Val>}

# The model's own terms
# ---------------------

# LAW cvar_terms_example: anchor: the model's predicates that laws/cvar/model.bend reads are not constant: a declaration twice is not unique, a Nat cvar with a Bool default is not well typed, a value of an undeclared cvar and no value of a declared one are not typed, a set of a cvar without the flag is not flagged, a run of an alias is not plain
# EXCLUDES: a constant True predicate that makes cvar_registry_unique,
#   cvar_registry_typed, cvar_value_typed, cvar_written_flagged,
#   alias_expands_fully or bind_press_plain hold vacuously
law cvar_terms_example:
  {[Cv.unique([Cv.Decl{0n, Cv.TNat{}, Cv.Local{}, False{}, False{}, Cv.VNat{0n}}, Cv.Decl{0n, Cv.TNat{}, Cv.Local{}, False{}, False{}, Cv.VNat{0n}}]), Cv.all_typed([Cv.Decl{0n, Cv.TNat{}, Cv.Local{}, False{}, False{}, Cv.VBool{True{}}}]), Cv.typed.at(None{}, Some{Cv.VNat{0n}}), Cv.typed.at(Some{Cv.Decl{0n, Cv.TNat{}, Cv.Local{}, False{}, False{}, Cv.VNat{0n}}}, None{}), Cv.typed.at(Some{Cv.Decl{0n, Cv.TNat{}, Cv.Local{}, False{}, False{}, Cv.VNat{0n}}}, Some{Cv.VBool{True{}}}), Cv.all_flag([Cv.Bind{0n, Cv.VNat{1n}}], [Cv.Decl{0n, Cv.TNat{}, Cv.Local{}, False{}, False{}, Cv.VNat{0n}}], Cv.Persist{}), Cv.Exp.plain(Cv.Flat{[Cv.CRun{0n}]}), Cv.Exp.plain(Cv.Flat{[Cv.CGone{0n}]})] == [False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}] : List<&2, Bool>} &
  {[Cv.unique([Cv.Decl{0n, Cv.TNat{}, Cv.Local{}, False{}, False{}, Cv.VNat{0n}}, Cv.Decl{1n, Cv.TNat{}, Cv.Local{}, False{}, False{}, Cv.VNat{0n}}]), Cv.all_typed([Cv.Decl{0n, Cv.TBool{}, Cv.Local{}, False{}, False{}, Cv.VBool{True{}}}]), Cv.typed.at(Some{Cv.Decl{0n, Cv.TNat{}, Cv.Local{}, False{}, False{}, Cv.VNat{0n}}}, Some{Cv.VNat{3n}}), Cv.all_flag([Cv.Bind{0n, Cv.VNat{1n}}], [Cv.Decl{0n, Cv.TNat{}, Cv.Local{}, True{}, False{}, Cv.VNat{0n}}], Cv.Persist{}), Cv.Exp.plain(Cv.Flat{[Cv.CToggle{0n}]})] == [True{}, True{}, True{}, True{}, True{}] : List<&2, Bool>}
