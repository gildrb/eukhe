# eukhe: the proof of LAW path_real_exact
#
# PROOF: the model's lookup is the spec's (pre.find, pre.next, pre.some:
# ids.eq is pp_same), its `..` is the spec's parent (pre.up); past the
# fuel the walk keeps every link as a name like pp_walk_past (pre.past);
# with fuel both walks branch on the same lookup and follow the same
# target from the same directory (pre.walk, by induction on the fuel, then
# the segments).

import Base
import ../../bend/path_policy.bend as Pp
import ../../bend/tools.bend as Tl
import ../../laws/path_policy.bend as PathPolicy
import ./base.bend as LA

# the model's pick is the spec's
def pre.pick(h: Bool, l: Pp.Link, r: Maybe<&2, Pp.Link>) -> {Pp.link.pick(h, l, r) == PathPolicy.pp_link_pick(h, l, r) : Maybe<&2, Pp.Link>}:
  match h:
    case True{}:
      {==}
    case False{}:
      {==}

# the model's lookup finds the spec's link
def pre.find(ls: List<&2, Pp.Link>, +k: List<&2, Nat>) -> {Pp.link.find(ls, k) == PathPolicy.pp_link_of(ls, k) : Maybe<&2, Pp.Link>}:
  match ls:
    case Nil{}:
      {==}
    case l <> +rest:
      match l:
        case Pp.Link{+a, +b, +t}:
          %LA.pp.ids_same(a, k) : {Pp.link.pick(Tl.ids.eq(a, k), Pp.Link{a, b, t}, Pp.link.find(rest, k)) == PathPolicy.pp_link_pick(_, Pp.Link{a, b, t}, PathPolicy.pp_link_of(rest, k)) : Maybe<&2, Pp.Link>}
          %pre.find(rest, k) : {Pp.link.pick(Tl.ids.eq(a, k), Pp.Link{a, b, t}, Pp.link.find(rest, k)) == PathPolicy.pp_link_pick(Tl.ids.eq(a, k), Pp.Link{a, b, t}, _) : Maybe<&2, Pp.Link>}
          pre.pick(Tl.ids.eq(a, k), Pp.Link{a, b, t}, Pp.link.find(rest, k))

# the model's next lookup is the spec's
def pre.next(+ls: List<&2, Pp.Link>, segs: List<&2, Tl.Seg>, at: List<&2, Nat>) -> {Pp.look.at(ls, segs, at) == PathPolicy.pp_link_next(ls, segs, at) : Maybe<&2, Pp.Link>}:
  match segs:
    case Nil{}:
      {==}
    case s <> rest:
      match s:
        case Tl.Name{n}:
          pre.find(ls, n <> at)
        case Tl.Up{}:
          {==}
        case Tl.Here{}:
          {==}

# a pick finds a link exactly when it hits or the rest finds one
def pre.pick_some(h: Bool, -l: Pp.Link, r: Maybe<&2, Pp.Link>) -> {Maybe.is_some(&2, Pp.Link, Pp.link.pick(h, l, r)) == Bool.or(h, Maybe.is_some(&2, Pp.Link, r)) : Bool}:
  match h:
    case True{}:
      {==}
    case False{}:
      {==}

# the model's lookup finds a link exactly when the spec sees one
def pre.some(ls: List<&2, Pp.Link>, +k: List<&2, Nat>) -> {Maybe.is_some(&2, Pp.Link, Pp.link.find(ls, k)) == PathPolicy.pp_link_at(ls, k) : Bool}:
  match ls:
    case Nil{}:
      {==}
    case l <> +rest:
      match l:
        case Pp.Link{+a, +b, +t}:
          %LA.pp.ids_same(a, k) : {Maybe.is_some(&2, Pp.Link, Pp.link.pick(Tl.ids.eq(a, k), Pp.Link{a, b, t}, Pp.link.find(rest, k))) == Bool.or(_, PathPolicy.pp_link_at(rest, k)) : Bool}
          %pre.some(rest, k) : {Maybe.is_some(&2, Pp.Link, Pp.link.pick(Tl.ids.eq(a, k), Pp.Link{a, b, t}, Pp.link.find(rest, k))) == Bool.or(Tl.ids.eq(a, k), _) : Bool}
          pre.pick_some(Tl.ids.eq(a, k), Pp.Link{a, b, t}, Pp.link.find(rest, k))

# the model's `..` is the spec's parent
def pre.up(at: List<&2, Nat>) -> {Pp.up(at) == PathPolicy.pp_parent(at) : List<&2, Nat>}:
  match at:
    case Nil{}:
      {==}
    case x <> r:
      {==}

# past the fuel, the model walks like pp_walk_past
def pre.past(segs: List<&2, Tl.Seg>, +ls: List<&2, Pp.Link>, +at: List<&2, Nat>, +l: Bool, +look: Maybe<&2, Pp.Link>, +lk: {look == Pp.look.at(ls, segs, at) : Maybe<&2, Pp.Link>}) -> {Pp.go(0n, segs, ls, at, l, look) == PathPolicy.pp_walk_past(segs, ls, at, l) : Pp.Res}:
  match segs:
    case Nil{}:
      {==}
    case s <> +rest:
      match s:
        case Tl.Name{+n}:
          %Equal.sym(Maybe<&2, Pp.Link>, look, Pp.link.find(ls, n <> at), lk) : {Pp.go(0n, Tl.Name{n} <> rest, ls, at, l, _) == PathPolicy.pp_walk_past(Tl.Name{n} <> rest, ls, at, l) : Pp.Res}
          %pre.some(ls, n <> at) : {Pp.go(0n, rest, ls, n <> at, Bool.or(l, Maybe.is_some(&2, Pp.Link, Pp.link.find(ls, n <> at))), Pp.look.at(ls, rest, n <> at)) == PathPolicy.pp_walk_past(rest, ls, n <> at, Bool.or(l, _)) : Pp.Res}
          pre.past(rest, ls, n <> at, Bool.or(l, Maybe.is_some(&2, Pp.Link, Pp.link.find(ls, n <> at))), Pp.look.at(ls, rest, n <> at), {==})
        case Tl.Up{}:
          %pre.up(at) : {Pp.go(0n, rest, ls, Pp.up(at), l, Pp.look.at(ls, rest, Pp.up(at))) == PathPolicy.pp_walk_past(rest, ls, _, l) : Pp.Res}
          pre.past(rest, ls, Pp.up(at), l, Pp.look.at(ls, rest, Pp.up(at)), {==})
        case Tl.Here{}:
          pre.past(rest, ls, at, l, Pp.look.at(ls, rest, at), {==})

# the model's walk (nothing looped yet) is the spec's walk, for any fuel
def pre.walk(fuel: Nat, segs: List<&2, Tl.Seg>, +ls: List<&2, Pp.Link>, +at: List<&2, Nat>, +look: Maybe<&2, Pp.Link>, +lk: {look == Pp.look.at(ls, segs, at) : Maybe<&2, Pp.Link>}) -> {Pp.go(fuel, segs, ls, at, False{}, look) == PathPolicy.pp_walk(fuel, segs, ls, at, look) : Pp.Res}:
  match fuel:
    case 0n:
      pre.past(segs, ls, at, False{}, look, lk)
    case 1n+f:
      match segs:
        case Nil{}:
          {==}
        case s <> +rest:
          match s:
            case Tl.Name{+n}:
              match look:
                case None{}:
                  %pre.next(ls, rest, n <> at) : {Pp.go(1n+f, rest, ls, n <> at, False{}, Pp.look.at(ls, rest, n <> at)) == PathPolicy.pp_walk(1n+f, rest, ls, n <> at, _) : Pp.Res}
                  pre.walk(1n+f, rest, ls, n <> at, Pp.look.at(ls, rest, n <> at), {==})
                case Some{lw}:
                  match lw:
                    case Pp.Link{la, abs, +to}:
                      match abs:
                        case True{}:
                          %pre.next(ls, List.append(&2, Tl.Seg, to, rest), Nil{}) : {Pp.go(f, List.append(&2, Tl.Seg, to, rest), ls, Nil{}, False{}, Pp.look.at(ls, List.append(&2, Tl.Seg, to, rest), Nil{})) == PathPolicy.pp_walk(f, List.append(&2, Tl.Seg, to, rest), ls, Nil{}, _) : Pp.Res}
                          pre.walk(f, List.append(&2, Tl.Seg, to, rest), ls, Nil{}, Pp.look.at(ls, List.append(&2, Tl.Seg, to, rest), Nil{}), {==})
                        case False{}:
                          %pre.next(ls, List.append(&2, Tl.Seg, to, rest), at) : {Pp.go(f, List.append(&2, Tl.Seg, to, rest), ls, at, False{}, Pp.look.at(ls, List.append(&2, Tl.Seg, to, rest), at)) == PathPolicy.pp_walk(f, List.append(&2, Tl.Seg, to, rest), ls, at, _) : Pp.Res}
                          pre.walk(f, List.append(&2, Tl.Seg, to, rest), ls, at, Pp.look.at(ls, List.append(&2, Tl.Seg, to, rest), at), {==})
            case Tl.Up{}:
              %pre.up(at) : {Pp.go(1n+f, rest, ls, Pp.up(at), False{}, Pp.look.at(ls, rest, Pp.up(at))) == PathPolicy.pp_walk(1n+f, rest, ls, _, PathPolicy.pp_link_next(ls, rest, _)) : Pp.Res}
              %pre.next(ls, rest, Pp.up(at)) : {Pp.go(1n+f, rest, ls, Pp.up(at), False{}, Pp.look.at(ls, rest, Pp.up(at))) == PathPolicy.pp_walk(1n+f, rest, ls, Pp.up(at), _) : Pp.Res}
              pre.walk(1n+f, rest, ls, Pp.up(at), Pp.look.at(ls, rest, Pp.up(at)), {==})
            case Tl.Here{}:
              %pre.next(ls, rest, at) : {Pp.go(1n+f, rest, ls, at, False{}, Pp.look.at(ls, rest, at)) == PathPolicy.pp_walk(1n+f, rest, ls, at, _) : Pp.Res}
              pre.walk(1n+f, rest, ls, at, Pp.look.at(ls, rest, at), {==})

def PathPolicy.path_real_exact(ls, segs):
  %pre.next(ls, segs, Nil{}) : {Pp.real(ls, segs) == PathPolicy.pp_walk(40n, segs, ls, Nil{}, _) : Pp.Res}
  pre.walk(Pp.max_links(), segs, ls, Nil{}, Pp.look.at(ls, segs, Nil{}), {==})
