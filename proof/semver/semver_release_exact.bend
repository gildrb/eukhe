# eukhe: the proof of LAW semver_release_exact
#
# PROOF of LAW semver_release_exact: Rel.release reads the workspace
# version as the spec does; its next release is the spec's
# (semver_next_exact) and Rel.newest is newest_spec.

import Base
import ../../bend/semver.bend as Sv
import ../../laws/semver.bend as Semver
import ./semver_next_exact.bend as PSemverNextExact

def pr.older(m: Maybe<&2, Sv.Ver>, +n: Sv.Ver) -> {Sv.Rel.older(n, m) == Semver.newest_spec.of(m, n) : Bool}:
  match m:
    case None{}:
      {==}
    case Some{v}:
      {==}

def pr.newest(+n: Sv.Ver, tags: List<&2, String>) -> {Sv.Rel.newest(n, tags) == Semver.newest_spec(n, tags) : Bool}:
  match tags:
    case Nil{}:
      {==}
    case +t <> +r:
      %pr.newest(n, r) : {Sv.Rel.newest(n, t <> r) == Bool.and(Semver.newest_spec.of(Sv.Tag.ver(t), n), _) : Bool}
      %pr.older(Sv.Tag.ver(t), n) : {Sv.Rel.newest(n, t <> r) == Bool.and(_, Sv.Rel.newest(n, r)) : Bool}
      {==}

def pr.guard(ok: Bool, -n: Sv.Ver) -> {Sv.Rel.guard(ok, n) == Semver.release_rule.newest(ok, n) : Maybe<&2, Sv.Ver>}:
  match ok:
    case True{}:
      {==}
    case False{}:
      {==}

def pr.at(+a: Nat, +b: Nat, c: Nat, +tags: List<&2, String>) -> {Sv.Rel.release.at(a, b, c, tags) == Semver.release_rule.at(a, b, c, tags) : Maybe<&2, Sv.Ver>}:
  match c:
    case 0n:
      +n = {Sv.Ver{a, b, Semver.next_spec(Semver.top_spec(a, b, tags))} : Sv.Ver}
      %Equal.sym(Sv.Ver, Sv.Rel.next(Sv.Ver{a, b, 0n}, tags), n, PSemverNextExact.pn.next(a, b, 0n, tags)) : {Sv.Rel.guard(Sv.Rel.newest(_, tags), _) == Semver.release_rule.newest(Semver.newest_spec(n, tags), n) : Maybe<&2, Sv.Ver>}
      %pr.newest(n, tags) : {Sv.Rel.guard(Sv.Rel.newest(n, tags), n) == Semver.release_rule.newest(_, n) : Maybe<&2, Sv.Ver>}
      pr.guard(Sv.Rel.newest(n, tags), n)
    case 1n+z:
      {==}

def pr.of(m: Maybe<&2, Sv.Ver>, +tags: List<&2, String>) -> {Sv.Rel.release.of(m, tags) == Semver.release_rule(m, tags) : Maybe<&2, Sv.Ver>}:
  match m:
    case None{}:
      {==}
    case Some{v}:
      match v:
        case Sv.Ver{+a, +b, c}:
          pr.at(a, b, c, tags)

def Semver.semver_release_exact(c, tags):
  pr.of(Sv.Ver.parse(c), tags)
