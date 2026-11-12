# eukhe: the proof of LAW semver_release_is_next

import Base
import ../../bend/semver.bend as Sv
import ../../laws/semver.bend as Semver
import ../base/logic/logic.bend as LLogicLogic

# PROOF of LAW semver_release_is_next: the workspace version reads as
# X.Y.0, so Rel.release is Rel.guard of the next release n of X.Y; a guard
# answers n or nothing, so a release r is n.

# the version m holds, d for none
def rin.val(m: Maybe<&2, Sv.Ver>, d: Sv.Ver) -> Sv.Ver:
  match m:
    case None{}:
      d
    case Some{v}:
      v

def rin.If(m: Maybe<&2, Sv.Ver>, G: Type) -> Type:
  match m:
    case None{}:
      Unit
    case Some{x}:
      G

def rin.guard(ok: Bool, +n: Sv.Ver, -r: Sv.Ver, e: {Sv.Rel.guard(ok, n) == Some{r} : Maybe<&2, Sv.Ver>}) -> {r == n : Sv.Ver}:
  match ok:
    case True{}:
      Equal.sym(Sv.Ver, n, r, Equal.cong(Maybe<&2, Sv.Ver>, Sv.Ver, m => rin.val(m, n), Some{n}, Some{r}, e))
    case False{}:
      %e : rin.If(_, {r == n : Sv.Ver})
      Unit{}

def rin.main(c: String, +a: Nat, +b: Nat, +tags: List<&2, String>, parsed: {Sv.Ver.parse(c) == Some{Sv.Ver{a, b, 0n}} : Maybe<&2, Sv.Ver>}, -r: Sv.Ver, rel: {Sv.Rel.release(c, tags) == Some{r} : Maybe<&2, Sv.Ver>}) -> {r == Sv.Rel.next(Sv.Ver{a, b, 0n}, tags) : Sv.Ver}:
  +n = Sv.Rel.next(Sv.Ver{a, b, 0n}, tags)
  +e = Equal.trans(Maybe<&2, Sv.Ver>, Sv.Rel.release.of(Some{Sv.Ver{a, b, 0n}}, tags), Sv.Rel.release(c, tags), Some{r}, Equal.cong(Maybe<&2, Sv.Ver>, Maybe<&2, Sv.Ver>, m => Sv.Rel.release.of(m, tags), Some{Sv.Ver{a, b, 0n}}, Sv.Ver.parse(c), Equal.sym(Maybe<&2, Sv.Ver>, Sv.Ver.parse(c), Some{Sv.Ver{a, b, 0n}}, parsed)), rel)
  rin.guard(Sv.Rel.newest(n, tags), n, r, e)

def Semver.semver_release_is_next(c, a, b, tags, parsed, r, rel):
  rin.main(c, a, b, tags, parsed, r, rel)
