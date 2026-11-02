# eukhe: the laws of area cvar, section whole: the registry and a toggle
# of the model (bend/cvar.bend), each pinned whole to a spec built from
# the spec helpers of laws/cvar.bend

import Base
import ../../bend/cvar.bend as Cv
import ../cvar.bend as Cvar

# LAWS (S4): cvar_registry_unique, cvar_registry_typed and
# cvar_value_typed hold of an empty registry, and cvar_toggle_twice of a
# toggle that leaves the agent as it was; these pin both whole. Every
# input is free: any declarations (duplicate ids, wrong defaults), any
# config.cfg, any family of agents with any profiles and sets.

def spec_registry.pick(dup: Bool, good: Bool, kept: List<&2, Cv.Decl>, d: Cv.Decl) -> List<&2, Cv.Decl>:
  match dup:
    case True{}:
      kept
    case False{}:
      match good:
        case True{}:
          List.append(&2, Cv.Decl, kept, [d])
        case False{}:
          kept

# the declarations of xs kept onto kept, in order: a declaration is kept
# unless its id is the id of one kept before it or its default does not
# have its type
def spec_registry(xs: List<&2, Cv.Decl>, +kept: List<&2, Cv.Decl>) -> List<&2, Cv.Decl>:
  match xs:
    case Nil{}:
      kept
    case +d <> rest:
      spec_registry(rest, spec_registry.pick(Cvar.spec_mem(Cvar.spec_id(d), Cvar.spec_ids(kept)), Cvar.spec_typed(Cvar.spec_init(d), Cvar.spec_ty(d)), kept, d))

# LAW cvar_registry_exact (S4): the registry of a declaration list is its declarations in order, each one dropped whose id a declaration kept before it has or whose default is not of its type
# EXCLUDES: an empty registry (the audit's: it keeps cvar_registry_unique,
#   cvar_registry_typed and cvar_value_typed true), a good declaration
#   dropped, a later duplicate kept over the first, a declaration with a
#   wrong default kept, the order changed
law cvar_registry_exact:
  for xs: List<&2, Cv.Decl>
  {Cv.registry(xs) == spec_registry(xs, Nil{}) : List<&2, Cv.Decl>}

# agent a after a toggle with verdict t: the set it names after a's own
# sets; a refused toggle leaves a as it was
def spec_tog_apply(a: Cv.Ag, t: Cv.Tog) -> Cv.Ag:
  match a:
    case Cv.Ag{p, ss}:
      match t:
        case Cv.TgUndeclared{}:
          Cv.Ag{p, ss}
        case Cv.TgGlobal{}:
          Cv.Ag{p, ss}
        case Cv.TgNotBool{}:
          Cv.Ag{p, ss}
        case Cv.TgFlip{s}:
          Cv.Ag{p, List.append(&2, Cv.Bind, ss, [s])}

# LAW cvar_toggle_exact (S4): a toggle of x by agent a, the last of the family chain, adds to a's own sets, last, the set the toggle verdict names (Cvar.spec_tog read with no layer restriction, the Config verdict) and changes nothing else: the set of the opposite of the Bool value a has, inherited values included; an undeclared or non-Bool cvar leaves a as it was. The model's toggle takes no layer: the flip of a Global cvar is added and every agent layer ignores it (cvar_layered_exact), so a's value stays, as cvar_toggle_twice reads it
# EXCLUDES: a toggle that leaves the agent as it was (the audit's: it
#   keeps cvar_toggle_twice true), one that sets the same value, ignores
#   the parent's value, flips a non-Bool, changes the profile or the
#   other sets, or puts the set anywhere but last
law cvar_toggle_exact:
  for +ds: List<&2, Cv.Decl>
  for +cfg: List<&2, Cv.Bind>
  for +fam: List<&2, Cv.Ag>
  for +a: Cv.Ag
  for +x: Nat
  {Cv.toggle(ds, cfg, fam, a, x) == spec_tog_apply(a, Cvar.spec_tog(ds, cfg, List.append(&2, Cv.Ag, fam, [a]), Cv.Config{}, x)) : Cv.Ag}
