# eukhe: the proof of LAW semver_next_exact
#
# PROOF of LAW semver_next_exact: Rel.top folds the tags as the spec
# does (the same series test; Num.max is Nat.max), and Rel.after is
# next_spec.

import Base
import ../../bend/semver.bend as Sv
import ../../laws/semver.bend as Semver

def pn.max(a: Nat, b: Nat) -> {Sv.Num.max(a, b) == Nat.max(a, b) : Nat}:
  match a b:
    case 0n _:
      {==}
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      Equal.cong(Nat, Nat, n => 1n+n, Sv.Num.max(p, q), Nat.max(p, q), pn.max(p, q))

def pn.keep(hit: Bool, +p: Nat, acc: Maybe<&2, Nat>) -> {Sv.Rel.keep(hit, p, acc) == Semver.top_spec.keep(hit, p, acc) : Maybe<&2, Nat>}:
  match hit:
    case True{}:
      match acc:
        case None{}:
          {==}
        case Some{q}:
          Equal.cong(Nat, Maybe<&2, Nat>, n => Some{n}, Sv.Num.max(p, q), Nat.max(p, q), pn.max(p, q))
    case False{}:
      {==}

def pn.add(m: Maybe<&2, Sv.Ver>, +a: Nat, +b: Nat, -c: Nat, acc: Maybe<&2, Nat>) -> {Sv.Rel.add(Sv.Ver{a, b, c}, m, acc) == Semver.top_spec.add(m, a, b, acc) : Maybe<&2, Nat>}:
  match m:
    case None{}:
      {==}
    case Some{v}:
      match v:
        case Sv.Ver{x, y, p}:
          pn.keep(Bool.and(Nat.is_eq(a, x), Nat.is_eq(b, y)), p, acc)

def pn.top(+a: Nat, +b: Nat, +c: Nat, tags: List<&2, String>) -> {Sv.Rel.top(Sv.Ver{a, b, c}, tags) == Semver.top_spec(a, b, tags) : Maybe<&2, Nat>}:
  match tags:
    case Nil{}:
      {==}
    case +t <> +r:
      %pn.top(a, b, c, r) : {Sv.Rel.top(Sv.Ver{a, b, c}, t <> r) == Semver.top_spec.add(Sv.Tag.ver(t), a, b, _) : Maybe<&2, Nat>}
      pn.add(Sv.Tag.ver(t), a, b, c, Sv.Rel.top(Sv.Ver{a, b, c}, r))

def pn.after(m: Maybe<&2, Nat>) -> {Sv.Rel.after(m) == Semver.next_spec(m) : Nat}:
  match m:
    case None{}:
      {==}
    case Some{p}:
      {==}

def pn.next(+a: Nat, +b: Nat, +c: Nat, +tags: List<&2, String>) -> {Sv.Rel.next(Sv.Ver{a, b, c}, tags) == Sv.Ver{a, b, Semver.next_spec(Semver.top_spec(a, b, tags))} : Sv.Ver}:
  %pn.top(a, b, c, tags) : {Sv.Rel.next(Sv.Ver{a, b, c}, tags) == Sv.Ver{a, b, Semver.next_spec(_)} : Sv.Ver}
  Equal.cong(Nat, Sv.Ver, n => Sv.Ver{a, b, n}, Sv.Rel.after(Sv.Rel.top(Sv.Ver{a, b, c}, tags)), Semver.next_spec(Sv.Rel.top(Sv.Ver{a, b, c}, tags)), pn.after(Sv.Rel.top(Sv.Ver{a, b, c}, tags)))

def Semver.semver_next_exact(a, b, c, tags):
  pn.next(a, b, c, tags)
