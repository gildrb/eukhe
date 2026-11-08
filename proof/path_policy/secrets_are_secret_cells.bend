# eukhe: the proof of LAW secrets_are_secret_cells

import Base
import ../../bend/path_policy.bend as Pp
import ../../laws/path_policy.bend as PathPolicy
import ./base.bend as LA

# the store's keep is the spec's
def pp.keep_eq(h: Bool, c: Pp.Cell, r: List<&2, Pp.Cell>) -> {Pp.keep.pick(h, c, r) == PathPolicy.pp_keep(h, c, r) : List<&2, Pp.Cell>}:
  match h:
    case True{}:
      {==}
    case False{}:
      {==}

def pp.secrets_spec(cs: List<&2, Pp.Cell>, +ro: List<&2, List<&2, Nat>>, +ru: List<&2, Pp.Rule>, +se: List<&2, List<&2, Nat>>) -> {Pp.secrets(cs, Pp.Pol{ro, ru, se}) == PathPolicy.pp_secret_cells(se, cs) : List<&2, Pp.Cell>}:
  match cs:
    case Nil{}:
      {==}
    case c <> +rest:
      match c:
        case Pp.Cell{+a, +w}:
          %Equal.sym(Bool, Pp.Cls.secret(Pp.class_of(Pp.Pol{ro, ru, se}, a)), PathPolicy.pp_under_any(se, a), LA.pp.class_of_secret(ro, ru, se, a)) : {Pp.keep.pick(_, Pp.Cell{a, w}, Pp.secrets(rest, Pp.Pol{ro, ru, se})) == PathPolicy.pp_keep(PathPolicy.pp_under_any(se, a), Pp.Cell{a, w}, PathPolicy.pp_secret_cells(se, rest)) : List<&2, Pp.Cell>}
          %pp.secrets_spec(rest, ro, ru, se) : {Pp.keep.pick(PathPolicy.pp_under_any(se, a), Pp.Cell{a, w}, Pp.secrets(rest, Pp.Pol{ro, ru, se})) == PathPolicy.pp_keep(PathPolicy.pp_under_any(se, a), Pp.Cell{a, w}, _) : List<&2, Pp.Cell>}
          pp.keep_eq(PathPolicy.pp_under_any(se, a), Pp.Cell{a, w}, Pp.secrets(rest, Pp.Pol{ro, ru, se}))

def PathPolicy.secrets_are_secret_cells(ro, ru, se, cs):
  pp.secrets_spec(cs, ro, ru, se)
