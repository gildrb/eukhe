# proof_tiny: the S9 laws (docs/inference.md) of the tiny-model model in
# bend/tiny.bend.
#
# A pick scans its chain with the test of the head as a parameter: a hit
# gives the head, which is in the chain and available; a miss moves on
# to the rest, so the first available model wins and a chain with none
# available ends in Unavailable. Every event's need lists exactly one
# outcome and an exit none, so the outcomes count the needs. A worker's
# tag after one event is the tag of that need (a join keeps a worker of
# the same tag) or none after an exit, which carries the last tag along
# the events.

import Base
import ./tiny.bend as Tn

# Logic
# -----

def pn.BD(b: Bool, t: Type, f: Type) -> Type:
  match b:
    case True{}:
      t
    case False{}:
      f

def pn.absurd(-A: Type, e: {True{} == False{} : Bool}) -> A:
  %e : pn.BD(_, Unit, A)
  Unit{}

def pn.absurdF(-A: Type, e: {False{} == True{} : Bool}) -> A:
  %e : pn.BD(_, A, Unit)
  Unit{}

def pn.and_l(a: Bool, +b: Bool, h: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      pn.absurdF({False{} == True{} : Bool}, h)

def pn.and_r(a: Bool, +b: Bool, h: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      h
    case False{}:
      pn.absurdF({b == True{} : Bool}, h)

def pn.and_t(+a: Bool, +b: Bool, ha: {a == True{} : Bool}, hb: {b == True{} : Bool}) -> {Bool.and(a, b) == True{} : Bool}:
  %Equal.sym(Bool, a, True{}, ha) : {Bool.and(_, b) == True{} : Bool}
  hb

def pn.or_r(x: Bool, +a: Bool, h: {a == True{} : Bool}) -> {Bool.or(x, a) == True{} : Bool}:
  match x:
    case True{}:
      {==}
    case False{}:
      h

def pn.not_t(b: Bool, h: {Bool.not(b) == True{} : Bool}) -> {b == False{} : Bool}:
  match b:
    case True{}:
      pn.absurdF({True{} == False{} : Bool}, h)
    case False{}:
      {==}

# Numbers
# -------

def pn.eq_refl(k: Nat) -> {True{} == Nat.is_eq(k, k) : Bool}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      pn.eq_refl(p)

def pn.eq_true(a: Nat, b: Nat, h: {Nat.is_eq(a, b) == True{} : Bool}) -> {a == b : Nat}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      pn.absurdF({0n == 1n+q : Nat}, h)
    case 1n+p 0n:
      pn.absurdF({1n+p == 0n : Nat}, h)
    case 1n+p 1n+q:
      Equal.cong(Nat, Nat, n => 1n+n, p, q, pn.eq_true(p, q, h))

# Picks
# -----

def pn.PD(p: Tn.Pick, u: Type, n: Type) -> Type:
  match p:
    case Tn.Use{m}:
      u
    case Tn.Unavailable{}:
      n

def pn.un_use(-A: Type, -m: Nat, e: {Tn.Unavailable{} == Tn.Use{m} : Tn.Pick}) -> A:
  %e : pn.PD(_, A, Unit)
  Unit{}

def pn.use_m(p: Tn.Pick) -> Nat:
  match p:
    case Tn.Use{m}:
      m
    case Tn.Unavailable{}:
      0n

def pn.use_inj(-a: Nat, -b: Nat, e: {Tn.Use{a} == Tn.Use{b} : Tn.Pick}) -> {a == b : Nat}:
  Equal.cong(Tn.Pick, Nat, p => pn.use_m(p), Tn.Use{a}, Tn.Use{b}, e)

# a scan that uses m found it in the chain and available
def pn.go_in(chain: List<&2, Nat>, +up: List<&2, Nat>, +m: Nat, hit: Bool, eh: {Tn.up.at(chain, up) == hit : Bool}, used: {Tn.pick.go(chain, up, hit) == Tn.Use{m} : Tn.Pick}) -> {Bool.and(Tn.elem(chain, m), Tn.elem(up, m)) == True{} : Bool}:
  match chain:
    case Nil{}:
      pn.un_use({Bool.and(False{}, Tn.elem(up, m)) == True{} : Bool}, m, used)
    case +h <> +rest:
      match hit:
        case True{}:
          %pn.use_inj(h, m, used) : {Bool.and(Tn.elem(h <> rest, _), Tn.elem(up, _)) == True{} : Bool}
          %pn.eq_refl(h) : {Bool.and(Bool.or(_, Tn.elem(rest, h)), Tn.elem(up, h)) == True{} : Bool}
          eh
        case False{}:
          +ih = pn.go_in(rest, up, m, Tn.up.at(rest, up), {==}, used)
          +hr = pn.and_l(Tn.elem(rest, m), Tn.elem(up, m), ih)
          +hu = pn.and_r(Tn.elem(rest, m), Tn.elem(up, m), ih)
          pn.and_t(Bool.or(Nat.is_eq(h, m), Tn.elem(rest, m)), Tn.elem(up, m), pn.or_r(Nat.is_eq(h, m), Tn.elem(rest, m), hr), hu)

# a scan with no model of the chain available ends in Unavailable
def pn.go_un(chain: List<&2, Nat>, +up: List<&2, Nat>, hit: Bool, eh: {Tn.up.at(chain, up) == hit : Bool}, none: {Tn.none_up(chain, up) == True{} : Bool}) -> {Tn.pick.go(chain, up, hit) == Tn.Unavailable{} : Tn.Pick}:
  match chain:
    case Nil{}:
      {==}
    case +x <> +rest:
      match hit:
        case True{}:
          +nx = pn.not_t(Tn.elem(up, x), pn.and_l(Bool.not(Tn.elem(up, x)), Tn.none_up(rest, up), none))
          pn.absurd({Tn.Use{x} == Tn.Unavailable{} : Tn.Pick}, Equal.trans(Bool, True{}, Tn.elem(up, x), False{}, Equal.sym(Bool, Tn.elem(up, x), True{}, eh), nx))
        case False{}:
          pn.go_un(rest, up, Tn.up.at(rest, up), {==}, pn.and_r(Bool.not(Tn.elem(up, x)), Tn.none_up(rest, up), none))

# a scan past models that are not available reaches the next one
def pn.first(pre: List<&2, Nat>, +m: Nat, +post: List<&2, Nat>, +up: List<&2, Nat>, +before: {Tn.none_up(pre, up) == True{} : Bool}, here: {Tn.elem(up, m) == True{} : Bool}) -> {Tn.pick(List.append(&2, Nat, pre, m <> post), up) == Tn.Use{m} : Tn.Pick}:
  match pre:
    case Nil{}:
      %Equal.sym(Bool, Tn.elem(up, m), True{}, here) : {Tn.pick.go(m <> post, up, _) == Tn.Use{m} : Tn.Pick}
      {==}
    case +x <> +r:
      +nx = pn.not_t(Tn.elem(up, x), pn.and_l(Bool.not(Tn.elem(up, x)), Tn.none_up(r, up), before))
      %Equal.sym(Bool, Tn.elem(up, x), False{}, nx) : {Tn.pick.go(x <> List.append(&2, Nat, r, m <> post), up, _) == Tn.Use{m} : Tn.Pick}
      pn.first(r, m, post, up, pn.and_r(Bool.not(Tn.elem(up, x)), Tn.none_up(r, up), before), here)

# Workers
# -------

# a need leaves a worker with its own tag: a join keeps a worker of
# the same tag, a replace starts one with the need's tag
def pn.need_tag(b: Bool, +p: Nat, +tag: Nat, +o: Nat, +t: Nat, eb: {Nat.is_eq(t, tag) == b : Bool}) -> {Tn.W.tag(Tn.need.w(b, p, tag, Tn.Worker{o, t})) == Some{tag} : Maybe<&2, Nat>}:
  match b:
    case True{}:
      Equal.cong(Nat, Maybe<&2, Nat>, n => Some{n}, t, tag, pn.eq_true(t, tag, eb))
    case False{}:
      {==}

# the worker's tag after events is the last tag along them
def pn.cur(es: List<&2, Tn.Ev>, +w: Tn.W) -> {Tn.W.tag(Tn.run(es, w)) == Tn.last_tag(es, Tn.W.tag(w)) : Maybe<&2, Nat>}:
  match es:
    case Nil{}:
      {==}
    case +e <> +rest:
      match e:
        case Tn.Gone{}:
          match w:
            case Tn.NoWorker{}:
              pn.cur(rest, Tn.NoWorker{})
            case Tn.Worker{o, t}:
              pn.cur(rest, Tn.NoWorker{})
        case Tn.Need{+p, +tag}:
          match w:
            case Tn.NoWorker{}:
              pn.cur(rest, Tn.Worker{p, tag})
            case Tn.Worker{+o, +t}:
              +s = Tn.need.w(Nat.is_eq(t, tag), p, tag, Tn.Worker{o, t})
              %pn.need_tag(Nat.is_eq(t, tag), p, tag, o, t, {==}) : {Tn.W.tag(Tn.run(rest, s)) == Tn.last_tag(rest, _) : Maybe<&2, Nat>}
              pn.cur(rest, s)

# The laws
# --------

def pn.tiny_pick_in_chain(+chain: List<&2, Nat>, +up: List<&2, Nat>, +m: Nat, used: {Tn.pick(chain, up) == Tn.Use{m} : Tn.Pick}) -> {Bool.and(Tn.elem(chain, m), Tn.elem(up, m)) == True{} : Bool}:
  pn.go_in(chain, up, m, Tn.up.at(chain, up), {==}, used)

def pn.tiny_pick_first(+pre: List<&2, Nat>, +m: Nat, +post: List<&2, Nat>, +up: List<&2, Nat>, before: {Tn.none_up(pre, up) == True{} : Bool}, here: {Tn.elem(up, m) == True{} : Bool}) -> {Tn.pick(List.append(&2, Nat, pre, m <> post), up) == Tn.Use{m} : Tn.Pick}:
  pn.first(pre, m, post, up, before, here)

def pn.tiny_pick_unavailable(+chain: List<&2, Nat>, +up: List<&2, Nat>, none: {Tn.none_up(chain, up) == True{} : Bool}) -> {Tn.pick(chain, up) == Tn.Unavailable{} : Tn.Pick}:
  pn.go_un(chain, up, Tn.up.at(chain, up), {==}, none)

def pn.tiny_every_need_served(+es: List<&2, Tn.Ev>, +w: Tn.W) -> {List.length(&2, Tn.Got, Tn.gots(es, w)) == Tn.needs(es) : Nat}:
  match es:
    case Nil{}:
      {==}
    case +e <> +rest:
      match e:
        case Tn.Gone{}:
          match w:
            case Tn.NoWorker{}:
              pn.tiny_every_need_served(rest, Tn.NoWorker{})
            case Tn.Worker{o, t}:
              pn.tiny_every_need_served(rest, Tn.NoWorker{})
        case Tn.Need{+p, +tag}:
          match w:
            case Tn.NoWorker{}:
              Equal.cong(Nat, Nat, n => 1n+n, List.length(&2, Tn.Got, Tn.gots(rest, Tn.Worker{p, tag})), Tn.needs(rest), pn.tiny_every_need_served(rest, Tn.Worker{p, tag}))
            case Tn.Worker{+o, +t}:
              +s = Tn.need.w(Nat.is_eq(t, tag), p, tag, Tn.Worker{o, t})
              Equal.cong(Nat, Nat, n => 1n+n, List.length(&2, Tn.Got, Tn.gots(rest, s)), Tn.needs(rest), pn.tiny_every_need_served(rest, s))

def pn.tiny_worker_current(+es: List<&2, Tn.Ev>) -> {Tn.W.tag(Tn.run(es, Tn.NoWorker{})) == Tn.last_tag(es, None{}) : Maybe<&2, Nat>}:
  pn.cur(es, Tn.NoWorker{})

def pn.tiny_same_tag_joins(+o: Nat, +t: Nat, +p: Nat) -> {Tn.got(Tn.Worker{o, t}, Tn.Need{p, t}) == [Tn.Joined{}] : List<&2, Tn.Got>}:
  %pn.eq_refl(t) : {[Tn.need.g(_)] == [Tn.Joined{}] : List<&2, Tn.Got>}
  {==}
