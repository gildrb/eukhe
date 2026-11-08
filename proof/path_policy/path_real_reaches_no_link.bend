# eukhe: the proof of LAW path_real_reaches_no_link

import Base
import ../../bend/path_policy.bend as Pp
import ../../bend/tools.bend as Tl
import ../../laws/path_policy/policy.bend as PathPolicy
import ./base.bend as LA
import ./path_real_has_no_link.bend as PPathRealHasNoLink

# the pick of a lookup finds no link exactly when neither the head nor the
# rest is one
def pp.pick_none(h: Bool, -l: Pp.Link, -r: Maybe<&2, Pp.Link>, -x: Bool, ih: {Maybe.is_none(&2, Pp.Link, r) == Bool.not(x) : Bool}) -> {Maybe.is_none(&2, Pp.Link, Pp.link.pick(h, l, r)) == Bool.not(Bool.or(h, x)) : Bool}:
  match h:
    case True{}:
      {==}
    case False{}:
      ih

# the model's lookup finds no link at k exactly when the spec sees none
def pp.find_spec(ls: List<&2, Pp.Link>, +k: List<&2, Nat>) -> {Maybe.is_none(&2, Pp.Link, Pp.link.find(ls, k)) == Bool.not(PathPolicy.pp_link_at(ls, k)) : Bool}:
  match ls:
    case Nil{}:
      {==}
    case l <> +rest:
      match l:
        case Pp.Link{+a, b, t}:
          %Equal.sym(Bool, Tl.ids.eq(a, k), PathPolicy.pp_same(a, k), LA.pp.ids_same(a, k)) : {Maybe.is_none(&2, Pp.Link, Pp.link.pick(_, Pp.Link{a, b, t}, Pp.link.find(rest, k))) == Bool.not(Bool.or(PathPolicy.pp_same(a, k), PathPolicy.pp_link_at(rest, k))) : Bool}
          pp.pick_none(PathPolicy.pp_same(a, k), Pp.Link{a, b, t}, Pp.link.find(rest, k), PathPolicy.pp_link_at(rest, k), pp.find_spec(rest, k))

# the model's linkfree is the spec's
def pp.linkfree_spec(+ls: List<&2, Pp.Link>, at: List<&2, Nat>) -> {Pp.linkfree(ls, at) == PathPolicy.pp_linkfree(ls, at) : Bool}:
  match at:
    case Nil{}:
      {==}
    case +a <> +above:
      %pp.find_spec(ls, a <> above) : {Bool.and(Maybe.is_none(&2, Pp.Link, Pp.link.find(ls, a <> above)), Pp.linkfree(ls, above)) == Bool.and(_, PathPolicy.pp_linkfree(ls, above)) : Bool}
      %pp.linkfree_spec(ls, above) : {Bool.and(Maybe.is_none(&2, Pp.Link, Pp.link.find(ls, a <> above)), Pp.linkfree(ls, above)) == Bool.and(Maybe.is_none(&2, Pp.Link, Pp.link.find(ls, a <> above)), _) : Bool}
      {==}

def PathPolicy.path_real_reaches_no_link(ls, segs):
  %pp.linkfree_spec(ls, Pp.Res.at(Pp.real(ls, segs))) : {Bool.or(Pp.Res.looped(Pp.real(ls, segs)), _) == True{} : Bool}
  PPathRealHasNoLink.pp.path_real_has_no_link(ls, segs)
