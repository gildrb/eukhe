# eukhe: the proof of LAW tiny_worker_current

import Base
import ../../bend/tiny.bend as Tn
import ../../laws/tiny/pick.bend as Tiny
import ./base.bend as LA

def pn.eq_true(a: Nat, b: Nat, h: {Nat.is_eq(a, b) == True{} : Bool}) -> {a == b : Nat}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      LA.tiny.pn.absurdF({0n == 1n+q : Nat}, h)
    case 1n+p 0n:
      LA.tiny.pn.absurdF({1n+p == 0n : Nat}, h)
    case 1n+p 1n+q:
      Equal.cong(Nat, Nat, n => 1n+n, p, q, pn.eq_true(p, q, h))

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

def pn.tiny_worker_current(+es: List<&2, Tn.Ev>) -> {Tn.W.tag(Tn.run(es, Tn.NoWorker{})) == Tn.last_tag(es, None{}) : Maybe<&2, Nat>}:
  pn.cur(es, Tn.NoWorker{})

def Tiny.tiny_worker_current(es):
  pn.tiny_worker_current(es)
