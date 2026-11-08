# eukhe: the proof of LAW path_resolve_spec
# The walk from the names at, after segs, is the spec's reading of segs:
# its uncancelled `..` climb at (none past its root), then its names stay.

import Base
import ../../bend/tools.bend as Tl
import ../../laws/tools.bend as Tools
import ../base/list.bend as LList

# u uncancelled `..` climbing the names at, then the names ns on top
def prs.at(u: Nat, ns: List<&2, Nat>, at: List<&2, Nat>) -> Maybe<&2, List<&2, Nat>>:
  match u:
    case 0n:
      Some{List.append(&2, Nat, ns, at)}
    case 1n+v:
      match at:
        case Nil{}:
          None{}
        case a <> t:
          prs.at(v, ns, t)

# a name n on top of at: it cancels one `..` of u, or stays under ns
def prs.name(+n: Nat, u: Nat, +ns: List<&2, Nat>, +at: List<&2, Nat>) -> {prs.at(u, ns, n <> at) == prs.at(Tools.tp_ups.name(u), Tools.tp_names.name(n, u, ns), at) : Maybe<&2, List<&2, Nat>>}:
  match u:
    case 0n:
      %LList.pd.app_assoc(Nat, ns, [n], at) : {Some{_} == Some{List.append(&2, Nat, List.append(&2, Nat, ns, [n]), at)} : Maybe<&2, List<&2, Nat>>}
      {==}
    case 1n+v:
      {==}

def prs.walk(segs: List<&2, Tl.Seg>, +at: List<&2, Nat>) -> {Tl.walk(segs, at) == prs.at(Tools.tp_ups(segs), Tools.tp_names(segs), at) : Maybe<&2, List<&2, Nat>>}:
  match segs:
    case Nil{}:
      {==}
    case g <> +rest:
      match g:
        case Tl.Name{+n}:
          Equal.trans(Maybe<&2, List<&2, Nat>>, Tl.walk(rest, n <> at), prs.at(Tools.tp_ups(rest), Tools.tp_names(rest), n <> at), prs.at(Tools.tp_ups.name(Tools.tp_ups(rest)), Tools.tp_names.name(n, Tools.tp_ups(rest), Tools.tp_names(rest)), at), prs.walk(rest, n <> at), prs.name(n, Tools.tp_ups(rest), Tools.tp_names(rest), at))
        case Tl.Up{}:
          match at:
            case Nil{}:
              {==}
            case a <> t:
              prs.walk(rest, t)
        case Tl.Here{}:
          prs.walk(rest, at)

def prs.root(u: Nat, +ns: List<&2, Nat>) -> {prs.at(u, ns, Nil{}) == Tools.tp_resolve.at(u, ns) : Maybe<&2, List<&2, Nat>>}:
  match u:
    case 0n:
      Equal.cong(List<&2, Nat>, Maybe<&2, List<&2, Nat>>, l => Some{l}, List.append(&2, Nat, ns, Nil{}), ns, LList.pd.app_nil(Nat, ns))
    case 1n+v:
      {==}

def Tools.path_resolve_spec(segs):
  Equal.trans(Maybe<&2, List<&2, Nat>>, Tl.resolve(segs), prs.at(Tools.tp_ups(segs), Tools.tp_names(segs), Nil{}), Tools.tp_resolve(segs), prs.walk(segs, Nil{}), prs.root(Tools.tp_ups(segs), Tools.tp_names(segs)))
