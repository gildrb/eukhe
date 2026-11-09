# eukhe: lemmas of area path_policy on the resolution of a path, split at
# a prefix
#
# prw.split: walking p then s is walking s from the state p reaches (the
# links left, the directory, whether a link looped: prw.st), so the laws of
# the real path compare two suffixes from one state. prw.le_fuel: the links
# left never grow. prw.stays: a loop is never undone. prw.more and
# prw.up_to: a walk that ends unlooped ends the same with more links left.

import Base
import ../../../bend/path_policy.bend as Pp
import ../../../bend/tools.bend as Tl
import ../../../laws/path_policy/policy.bend as PathPolicy
import ../../base/logic/logic.bend as LLogicLogic
import ../base.bend as LA
import ./root.bend as LAR
import ./lemmas.bend as LAE
import ../path_real_reaches_no_link.bend as PPathRealReachesNoLink

# Lists and numbers
# -----------------

def prw.app_nil(xs: List<&2, Tl.Seg>) -> {List.append(&2, Tl.Seg, xs, Nil{}) == xs : List<&2, Tl.Seg>}:
  match xs:
    case Nil{}:
      {==}
    case +h <> r:
      %prw.app_nil(r) : {h <> List.append(&2, Tl.Seg, r, Nil{}) == h <> _ : List<&2, Tl.Seg>}
      {==}

def prw.app_assoc(xs: List<&2, Tl.Seg>, +ys: List<&2, Tl.Seg>, +zs: List<&2, Tl.Seg>) -> {List.append(&2, Tl.Seg, List.append(&2, Tl.Seg, xs, ys), zs) == List.append(&2, Tl.Seg, xs, List.append(&2, Tl.Seg, ys, zs)) : List<&2, Tl.Seg>}:
  match xs:
    case Nil{}:
      {==}
    case +h <> r:
      %prw.app_assoc(r, ys, zs) : {h <> List.append(&2, Tl.Seg, List.append(&2, Tl.Seg, r, ys), zs) == h <> _ : List<&2, Tl.Seg>}
      {==}

def prw.le_refl(n: Nat) -> {Nat.is_le(n, n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+k:
      prw.le_refl(k)

def prw.le0(n: Nat) -> {Nat.is_le(0n, n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+k:
      {==}

# a <= b gives a <= 1 + b
def prw.le_step(a: Nat, b: Nat, h: {Nat.is_le(a, b) == True{} : Bool}) -> {Nat.is_le(a, 1n+b) == True{} : Bool}:
  match a:
    case 0n:
      prw.le0(1n+b)
    case 1n+i:
      match b:
        case 0n:
          LA.pp.absurdF({Nat.is_le(1n+i, 1n) == True{} : Bool}, h)
        case 1n+k:
          prw.le_step(i, k, h)

# 1 + a <= b gives a <= b
def prw.le_pred(a: Nat, b: Nat, h: {Nat.is_le(1n+a, b) == True{} : Bool}) -> {Nat.is_le(a, b) == True{} : Bool}:
  match a:
    case 0n:
      prw.le0(b)
    case 1n+i:
      match b:
        case 0n:
          h
        case 1n+k:
          prw.le_pred(i, k, h)

# i <= k and k is not i: 1 + i <= k
def prw.le_ne(i: Nat, k: Nat, h: {Nat.is_le(i, k) == True{} : Bool}, ne: {Nat.is_eq(k, i) == False{} : Bool}) -> {Nat.is_le(1n+i, k) == True{} : Bool}:
  match i:
    case 0n:
      match k:
        case 0n:
          LLogicLogic.pp.absurd({Nat.is_le(1n, 0n) == True{} : Bool}, ne)
        case 1n+j:
          prw.le0(j)
    case 1n+a:
      match k:
        case 0n:
          h
        case 1n+j:
          prw.le_ne(a, j, h, ne)

def prw.or_fl(a: Bool, -b: Bool, h: {Bool.or(a, b) == False{} : Bool}) -> {a == False{} : Bool}:
  match a:
    case True{}:
      LLogicLogic.pp.absurd({True{} == False{} : Bool}, h)
    case False{}:
      {==}

def prw.or_fr(a: Bool, -b: Bool, h: {Bool.or(a, b) == False{} : Bool}) -> {b == False{} : Bool}:
  match a:
    case True{}:
      LLogicLogic.pp.absurd({b == False{} : Bool}, h)
    case False{}:
      h

# Lookups
# -------

def prw.none_of(m: Maybe<&2, Pp.Link>, h: {Maybe.is_none(&2, Pp.Link, m) == True{} : Bool}) -> {m == None{} : Maybe<&2, Pp.Link>}:
  match m:
    case None{}:
      {==}
    case Some{v}:
      LA.pp.absurdF({Some{v} == None{} : Maybe<&2, Pp.Link>}, h)

# the spec sees no link at k: the model's lookup finds none
def prw.find_none(+ls: List<&2, Pp.Link>, +k: List<&2, Nat>, plain: {PathPolicy.pp_link_at(ls, k) == False{} : Bool}) -> {Pp.link.find(ls, k) == None{} : Maybe<&2, Pp.Link>}:
  prw.none_of(Pp.link.find(ls, k), Equal.trans(Bool, Maybe.is_none(&2, Pp.Link, Pp.link.find(ls, k)), Bool.not(PathPolicy.pp_link_at(ls, k)), True{}, PPathRealReachesNoLink.pp.find_spec(ls, k), Equal.cong(Bool, Bool, z => Bool.not(z), PathPolicy.pp_link_at(ls, k), False{}, plain)))

# a link at k after links none of which sits at k is the one found at k
def prw.find_first(ls1: List<&2, Pp.Link>, +k: List<&2, Nat>, +abs: Bool, +to: List<&2, Tl.Seg>, +ls2: List<&2, Pp.Link>, +first: {PathPolicy.pp_link_at(ls1, k) == False{} : Bool}) -> {Pp.link.find(List.append(&2, Pp.Link, ls1, Pp.Link{k, abs, to} <> ls2), k) == Some{Pp.Link{k, abs, to}} : Maybe<&2, Pp.Link>}:
  match ls1:
    case Nil{}:
      %Equal.sym(Bool, Tl.ids.eq(k, k), True{}, LAR.pc.ids_refl(k)) : {Pp.link.pick(_, Pp.Link{k, abs, to}, Pp.link.find(ls2, k)) == Some{Pp.Link{k, abs, to}} : Maybe<&2, Pp.Link>}
      {==}
    case l <> +rest:
      match l:
        case Pp.Link{+a, b, t}:
          +e1 = Equal.trans(Bool, Tl.ids.eq(a, k), PathPolicy.pp_same(a, k), False{}, LA.pp.ids_same(a, k), prw.or_fl(PathPolicy.pp_same(a, k), PathPolicy.pp_link_at(rest, k), first))
          %Equal.sym(Bool, Tl.ids.eq(a, k), False{}, e1) : {Pp.link.pick(_, Pp.Link{a, b, t}, Pp.link.find(List.append(&2, Pp.Link, rest, Pp.Link{k, abs, to} <> ls2), k)) == Some{Pp.Link{k, abs, to}} : Maybe<&2, Pp.Link>}
          prw.find_first(rest, k, abs, to, ls2, prw.or_fr(PathPolicy.pp_same(a, k), PathPolicy.pp_link_at(rest, k), first))

# The walk, split
# ---------------

# the state a walk of p reaches: the links left, then the directory and
# whether a link looped (look is the lookup of p's first name)
def prw.st(fuel: Nat, p: List<&2, Tl.Seg>, +ls: List<&2, Pp.Link>, +at: List<&2, Nat>, looped: Bool, look: Maybe<&2, Pp.Link>) -> Nat & Pp.Res:
  match fuel:
    case 0n:
      match p:
        case Nil{}:
          (0n, Pp.Res{at, looped})
        case s <> +rest:
          match s:
            case Tl.Name{+n}:
              prw.st(0n, rest, ls, n <> at, Bool.or(looped, Maybe.is_some(&2, Pp.Link, look)), Pp.look.at(ls, rest, n <> at))
            case Tl.Up{}:
              prw.st(0n, rest, ls, Pp.up(at), looped, Pp.look.at(ls, rest, Pp.up(at)))
            case Tl.Here{}:
              prw.st(0n, rest, ls, at, looped, Pp.look.at(ls, rest, at))
    case 1n+f:
      match p:
        case Nil{}:
          (1n+f, Pp.Res{at, looped})
        case s <> +rest:
          match s:
            case Tl.Name{+n}:
              match look:
                case None{}:
                  prw.st(1n+f, rest, ls, n <> at, looped, Pp.look.at(ls, rest, n <> at))
                case Some{l}:
                  match l:
                    case Pp.Link{la, abs, +to}:
                      match abs:
                        case True{}:
                          prw.st(f, List.append(&2, Tl.Seg, to, rest), ls, Nil{}, looped, Pp.look.at(ls, List.append(&2, Tl.Seg, to, rest), Nil{}))
                        case False{}:
                          prw.st(f, List.append(&2, Tl.Seg, to, rest), ls, at, looped, Pp.look.at(ls, List.append(&2, Tl.Seg, to, rest), at))
            case Tl.Up{}:
              prw.st(1n+f, rest, ls, Pp.up(at), looped, Pp.look.at(ls, rest, Pp.up(at)))
            case Tl.Here{}:
              prw.st(1n+f, rest, ls, at, looped, Pp.look.at(ls, rest, at))

# the links a state has left
def prw.fuel(t: Nat & Pp.Res) -> Nat:
  match t:
    case (f, r):
      f

# the walk of s from a state
def prw.cont(t: Nat & Pp.Res, +s: List<&2, Tl.Seg>, +ls: List<&2, Pp.Link>) -> Pp.Res:
  match t:
    case (f, r):
      match r:
        case Pp.Res{+a, b}:
          Pp.go(f, s, ls, a, b, Pp.look.at(ls, s, a))

# walking p then s is walking s from the state p reaches
def prw.split(fuel: Nat, p: List<&2, Tl.Seg>, +s: List<&2, Tl.Seg>, +ls: List<&2, Pp.Link>, +at: List<&2, Nat>, +looped: Bool, +look: Maybe<&2, Pp.Link>, lk: {look == Pp.look.at(ls, p, at) : Maybe<&2, Pp.Link>}) -> {Pp.go(fuel, List.append(&2, Tl.Seg, p, s), ls, at, looped, Pp.look.at(ls, List.append(&2, Tl.Seg, p, s), at)) == prw.cont(prw.st(fuel, p, ls, at, looped, look), s, ls) : Pp.Res}:
  match fuel:
    case 0n:
      match p:
        case Nil{}:
          {==}
        case x <> +rest:
          match x:
            case Tl.Name{+n}:
              %lk : {Pp.go(0n, List.append(&2, Tl.Seg, Tl.Name{n} <> rest, s), ls, at, looped, _) == prw.cont(prw.st(0n, Tl.Name{n} <> rest, ls, at, looped, look), s, ls) : Pp.Res}
              prw.split(0n, rest, s, ls, n <> at, Bool.or(looped, Maybe.is_some(&2, Pp.Link, look)), Pp.look.at(ls, rest, n <> at), {==})
            case Tl.Up{}:
              prw.split(0n, rest, s, ls, Pp.up(at), looped, Pp.look.at(ls, rest, Pp.up(at)), {==})
            case Tl.Here{}:
              prw.split(0n, rest, s, ls, at, looped, Pp.look.at(ls, rest, at), {==})
    case 1n+f:
      match p:
        case Nil{}:
          {==}
        case x <> +rest:
          match x:
            case Tl.Name{+n}:
              match look:
                case None{}:
                  %lk : {Pp.go(1n+f, List.append(&2, Tl.Seg, Tl.Name{n} <> rest, s), ls, at, looped, _) == prw.cont(prw.st(1n+f, Tl.Name{n} <> rest, ls, at, looped, None{}), s, ls) : Pp.Res}
                  prw.split(1n+f, rest, s, ls, n <> at, looped, Pp.look.at(ls, rest, n <> at), {==})
                case Some{l}:
                  match l:
                    case Pp.Link{la, abs, +to}:
                      match abs:
                        case True{}:
                          %lk : {Pp.go(1n+f, List.append(&2, Tl.Seg, Tl.Name{n} <> rest, s), ls, at, looped, _) == prw.cont(prw.st(1n+f, Tl.Name{n} <> rest, ls, at, looped, Some{Pp.Link{la, True{}, to}}), s, ls) : Pp.Res}
                          %prw.app_assoc(to, rest, s) : {Pp.go(f, _, ls, Nil{}, looped, Pp.look.at(ls, _, Nil{})) == prw.cont(prw.st(f, List.append(&2, Tl.Seg, to, rest), ls, Nil{}, looped, Pp.look.at(ls, List.append(&2, Tl.Seg, to, rest), Nil{})), s, ls) : Pp.Res}
                          prw.split(f, List.append(&2, Tl.Seg, to, rest), s, ls, Nil{}, looped, Pp.look.at(ls, List.append(&2, Tl.Seg, to, rest), Nil{}), {==})
                        case False{}:
                          %lk : {Pp.go(1n+f, List.append(&2, Tl.Seg, Tl.Name{n} <> rest, s), ls, at, looped, _) == prw.cont(prw.st(1n+f, Tl.Name{n} <> rest, ls, at, looped, Some{Pp.Link{la, False{}, to}}), s, ls) : Pp.Res}
                          %prw.app_assoc(to, rest, s) : {Pp.go(f, _, ls, at, looped, Pp.look.at(ls, _, at)) == prw.cont(prw.st(f, List.append(&2, Tl.Seg, to, rest), ls, at, looped, Pp.look.at(ls, List.append(&2, Tl.Seg, to, rest), at)), s, ls) : Pp.Res}
                          prw.split(f, List.append(&2, Tl.Seg, to, rest), s, ls, at, looped, Pp.look.at(ls, List.append(&2, Tl.Seg, to, rest), at), {==})
            case Tl.Up{}:
              prw.split(1n+f, rest, s, ls, Pp.up(at), looped, Pp.look.at(ls, rest, Pp.up(at)), {==})
            case Tl.Here{}:
              prw.split(1n+f, rest, s, ls, at, looped, Pp.look.at(ls, rest, at), {==})

# the links left after p are never more than at its start
def prw.le_fuel(fuel: Nat, p: List<&2, Tl.Seg>, +ls: List<&2, Pp.Link>, +at: List<&2, Nat>, +looped: Bool, look: Maybe<&2, Pp.Link>) -> {Nat.is_le(prw.fuel(prw.st(fuel, p, ls, at, looped, look)), fuel) == True{} : Bool}:
  match fuel:
    case 0n:
      match p:
        case Nil{}:
          {==}
        case s <> +rest:
          match s:
            case Tl.Name{+n}:
              prw.le_fuel(0n, rest, ls, n <> at, Bool.or(looped, Maybe.is_some(&2, Pp.Link, look)), Pp.look.at(ls, rest, n <> at))
            case Tl.Up{}:
              prw.le_fuel(0n, rest, ls, Pp.up(at), looped, Pp.look.at(ls, rest, Pp.up(at)))
            case Tl.Here{}:
              prw.le_fuel(0n, rest, ls, at, looped, Pp.look.at(ls, rest, at))
    case 1n++f:
      match p:
        case Nil{}:
          prw.le_refl(1n+f)
        case s <> +rest:
          match s:
            case Tl.Name{+n}:
              match look:
                case None{}:
                  prw.le_fuel(1n+f, rest, ls, n <> at, looped, Pp.look.at(ls, rest, n <> at))
                case Some{l}:
                  match l:
                    case Pp.Link{la, abs, +to}:
                      match abs:
                        case True{}:
                          prw.le_step(prw.fuel(prw.st(f, List.append(&2, Tl.Seg, to, rest), ls, Nil{}, looped, Pp.look.at(ls, List.append(&2, Tl.Seg, to, rest), Nil{}))), f, prw.le_fuel(f, List.append(&2, Tl.Seg, to, rest), ls, Nil{}, looped, Pp.look.at(ls, List.append(&2, Tl.Seg, to, rest), Nil{})))
                        case False{}:
                          prw.le_step(prw.fuel(prw.st(f, List.append(&2, Tl.Seg, to, rest), ls, at, looped, Pp.look.at(ls, List.append(&2, Tl.Seg, to, rest), at))), f, prw.le_fuel(f, List.append(&2, Tl.Seg, to, rest), ls, at, looped, Pp.look.at(ls, List.append(&2, Tl.Seg, to, rest), at)))
            case Tl.Up{}:
              prw.le_fuel(1n+f, rest, ls, Pp.up(at), looped, Pp.look.at(ls, rest, Pp.up(at)))
            case Tl.Here{}:
              prw.le_fuel(1n+f, rest, ls, at, looped, Pp.look.at(ls, rest, at))

# The resolution, split
# ---------------------

# the state the resolution of p reaches
def prw.T(+ls: List<&2, Pp.Link>, +p: List<&2, Tl.Seg>) -> Nat & Pp.Res:
  prw.st(40n, p, ls, Nil{}, False{}, Pp.look.at(ls, p, Nil{}))

def prw.real_split(+ls: List<&2, Pp.Link>, +p: List<&2, Tl.Seg>, +s: List<&2, Tl.Seg>) -> {Pp.real(ls, List.append(&2, Tl.Seg, p, s)) == prw.cont(prw.T(ls, p), s, ls) : Pp.Res}:
  prw.split(40n, p, s, ls, Nil{}, False{}, Pp.look.at(ls, p, Nil{}), {==})

def prw.real_end(+ls: List<&2, Pp.Link>, +p: List<&2, Tl.Seg>) -> {Pp.real(ls, p) == prw.cont(prw.T(ls, p), Nil{}, ls) : Pp.Res}:
  %prw.app_nil(p) : {Pp.go(40n, _, ls, Nil{}, False{}, Pp.look.at(ls, _, Nil{})) == prw.cont(prw.T(ls, p), Nil{}, ls) : Pp.Res}
  prw.real_split(ls, p, Nil{})

def prw.le_T(+ls: List<&2, Pp.Link>, +p: List<&2, Tl.Seg>) -> {Nat.is_le(prw.fuel(prw.T(ls, p)), 40n) == True{} : Bool}:
  prw.le_fuel(40n, p, ls, Nil{}, False{}, Pp.look.at(ls, p, Nil{}))

# Loops and fuel
# --------------

# a walk that already looped ends looped
def prw.stays(fuel: Nat, segs: List<&2, Tl.Seg>, +ls: List<&2, Pp.Link>, +at: List<&2, Nat>, look: Maybe<&2, Pp.Link>) -> {Pp.Res.looped(Pp.go(fuel, segs, ls, at, True{}, look)) == True{} : Bool}:
  match fuel:
    case 0n:
      match segs:
        case Nil{}:
          {==}
        case s <> +rest:
          match s:
            case Tl.Name{+n}:
              prw.stays(0n, rest, ls, n <> at, Pp.look.at(ls, rest, n <> at))
            case Tl.Up{}:
              prw.stays(0n, rest, ls, Pp.up(at), Pp.look.at(ls, rest, Pp.up(at)))
            case Tl.Here{}:
              prw.stays(0n, rest, ls, at, Pp.look.at(ls, rest, at))
    case 1n+f:
      match segs:
        case Nil{}:
          {==}
        case s <> +rest:
          match s:
            case Tl.Name{+n}:
              match look:
                case None{}:
                  prw.stays(1n+f, rest, ls, n <> at, Pp.look.at(ls, rest, n <> at))
                case Some{l}:
                  match l:
                    case Pp.Link{la, abs, +to}:
                      match abs:
                        case True{}:
                          prw.stays(f, List.append(&2, Tl.Seg, to, rest), ls, Nil{}, Pp.look.at(ls, List.append(&2, Tl.Seg, to, rest), Nil{}))
                        case False{}:
                          prw.stays(f, List.append(&2, Tl.Seg, to, rest), ls, at, Pp.look.at(ls, List.append(&2, Tl.Seg, to, rest), at))
            case Tl.Up{}:
              prw.stays(1n+f, rest, ls, Pp.up(at), Pp.look.at(ls, rest, Pp.up(at)))
            case Tl.Here{}:
              prw.stays(1n+f, rest, ls, at, Pp.look.at(ls, rest, at))

# a walk that already looped never ends unlooped
def prw.no_loop(-G: Type, +fuel: Nat, +segs: List<&2, Tl.Seg>, +ls: List<&2, Pp.Link>, +at: List<&2, Nat>, +look: Maybe<&2, Pp.Link>, +x: List<&2, Nat>, h: {Pp.go(fuel, segs, ls, at, True{}, look) == Pp.Res{x, False{}} : Pp.Res}) -> G:
  +c = Equal.cong(Pp.Res, Bool, z => Pp.Res.looped(z), Pp.go(fuel, segs, ls, at, True{}, look), Pp.Res{x, False{}}, h)
  LA.pp.absurdF(G, Equal.trans(Bool, False{}, Pp.Res.looped(Pp.go(fuel, segs, ls, at, True{}, look)), True{}, Equal.sym(Bool, Pp.Res.looped(Pp.go(fuel, segs, ls, at, True{}, look)), False{}, c), prw.stays(fuel, segs, ls, at, look)))

# a walk with no links left that ends unlooped met no link: it ends the
# same with any links left
def prw.past_any(d: Nat, segs: List<&2, Tl.Seg>, +ls: List<&2, Pp.Link>, +at: List<&2, Nat>, look: Maybe<&2, Pp.Link>, +x: List<&2, Nat>, h: {Pp.go(0n, segs, ls, at, False{}, look) == Pp.Res{x, False{}} : Pp.Res}) -> {Pp.go(d, segs, ls, at, False{}, look) == Pp.Res{x, False{}} : Pp.Res}:
  match d:
    case 0n:
      h
    case 1n+e:
      match segs:
        case Nil{}:
          h
        case s <> +rest:
          match s:
            case Tl.Name{+n}:
              match look:
                case None{}:
                  prw.past_any(1n+e, rest, ls, n <> at, Pp.look.at(ls, rest, n <> at), x, h)
                case Some{l}:
                  prw.no_loop({Pp.go(1n+e, Tl.Name{n} <> rest, ls, at, False{}, Some{l}) == Pp.Res{x, False{}} : Pp.Res}, 0n, rest, ls, n <> at, Pp.look.at(ls, rest, n <> at), x, h)
            case Tl.Up{}:
              prw.past_any(1n+e, rest, ls, Pp.up(at), Pp.look.at(ls, rest, Pp.up(at)), x, h)
            case Tl.Here{}:
              prw.past_any(1n+e, rest, ls, at, Pp.look.at(ls, rest, at), x, h)

# a walk that ends unlooped ends the same with one more link left
def prw.more(g: Nat, segs: List<&2, Tl.Seg>, +ls: List<&2, Pp.Link>, +at: List<&2, Nat>, look: Maybe<&2, Pp.Link>, +x: List<&2, Nat>, h: {Pp.go(g, segs, ls, at, False{}, look) == Pp.Res{x, False{}} : Pp.Res}) -> {Pp.go(1n+g, segs, ls, at, False{}, look) == Pp.Res{x, False{}} : Pp.Res}:
  match g:
    case 0n:
      prw.past_any(1n, segs, ls, at, look, x, h)
    case 1n+f:
      match segs:
        case Nil{}:
          h
        case s <> +rest:
          match s:
            case Tl.Name{+n}:
              match look:
                case None{}:
                  prw.more(1n+f, rest, ls, n <> at, Pp.look.at(ls, rest, n <> at), x, h)
                case Some{l}:
                  match l:
                    case Pp.Link{la, abs, +to}:
                      match abs:
                        case True{}:
                          prw.more(f, List.append(&2, Tl.Seg, to, rest), ls, Nil{}, Pp.look.at(ls, List.append(&2, Tl.Seg, to, rest), Nil{}), x, h)
                        case False{}:
                          prw.more(f, List.append(&2, Tl.Seg, to, rest), ls, at, Pp.look.at(ls, List.append(&2, Tl.Seg, to, rest), at), x, h)
            case Tl.Up{}:
              prw.more(1n+f, rest, ls, Pp.up(at), Pp.look.at(ls, rest, Pp.up(at)), x, h)
            case Tl.Here{}:
              prw.more(1n+f, rest, ls, at, Pp.look.at(ls, rest, at), x, h)

# the step of prw.up_to by the test b of 1 + H against g
def prw.up_pick(b: Bool, +H: Nat, +g: Nat, +segs: List<&2, Tl.Seg>, +ls: List<&2, Pp.Link>, +at: List<&2, Nat>, +look: Maybe<&2, Pp.Link>, +x: List<&2, Nat>, eb: {Nat.is_eq(1n+H, g) == b : Bool}, ih: {Nat.is_le(g, H) == True{} : Bool} -> {Pp.go(g, segs, ls, at, False{}, look) == Pp.Res{x, False{}} : Pp.Res} -> {Pp.go(H, segs, ls, at, False{}, look) == Pp.Res{x, False{}} : Pp.Res}, le: {Nat.is_le(g, 1n+H) == True{} : Bool}, h: {Pp.go(g, segs, ls, at, False{}, look) == Pp.Res{x, False{}} : Pp.Res}) -> {Pp.go(1n+H, segs, ls, at, False{}, look) == Pp.Res{x, False{}} : Pp.Res}:
  match b:
    case True{}:
      %Equal.sym(Nat, 1n+H, g, LAE.pp.eq_true(1n+H, g, eb)) : {Pp.go(_, segs, ls, at, False{}, look) == Pp.Res{x, False{}} : Pp.Res}
      h
    case False{}:
      prw.more(H, segs, ls, at, look, x, ih(prw.le_ne(g, 1n+H, le, eb), h))

# a walk that ends unlooped with g links left ends the same with G >= g
def prw.up_to(G: Nat, +g: Nat, +segs: List<&2, Tl.Seg>, +ls: List<&2, Pp.Link>, +at: List<&2, Nat>, +look: Maybe<&2, Pp.Link>, +x: List<&2, Nat>) -> {Nat.is_le(g, G) == True{} : Bool} -> {Pp.go(g, segs, ls, at, False{}, look) == Pp.Res{x, False{}} : Pp.Res} -> {Pp.go(G, segs, ls, at, False{}, look) == Pp.Res{x, False{}} : Pp.Res}:
  match G:
    case 0n:
      match g:
        case 0n:
          le => h => h
        case 1n+k:
          le => h => LA.pp.absurdF({Pp.go(0n, segs, ls, at, False{}, look) == Pp.Res{x, False{}} : Pp.Res}, le)
    case 1n++H:
      le => h => prw.up_pick(Nat.is_eq(1n+H, g), H, g, segs, ls, at, look, x, {==}, prw.up_to(H, g, segs, ls, at, look, x), le, h)
