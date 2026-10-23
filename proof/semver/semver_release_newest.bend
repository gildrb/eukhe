# eukhe: the proof of LAW semver_release_newest

import Base
import ../../bend/semver.bend as Sv
import ../../LAWS.bend as Laws
import ../base.bend as L

def semver.ps.MD(m: Maybe<&2, Sv.Ver>, t: Type, f: Type) -> Type:
  match m:
    case None{}:
      t
    case Some{v}:
      f

# None is no Some
def semver.ps.none_some(-A: Type, -r: Sv.Ver, e: {None{} == Some{r} : Maybe<&2, Sv.Ver>}) -> A:
  %e : semver.ps.MD(_, Unit, A)
  Unit{}

# A release
# ---------

def ps.guard_ok(ok: Bool, -n: Sv.Ver, -r: Sv.Ver, h: {Sv.Rel.guard(ok, n) == Some{r} : Maybe<&2, Sv.Ver>}) -> {ok == True{} : Bool}:
  match ok:
    case True{}:
      {==}
    case False{}:
      semver.ps.none_some({False{} == True{} : Bool}, r, h)

def ps.guard_val(ok: Bool, +n: Sv.Ver, -r: Sv.Ver, h: {Sv.Rel.guard(ok, n) == Some{r} : Maybe<&2, Sv.Ver>}) -> {n == r : Sv.Ver}:
  match ok:
    case True{}:
      Equal.cong(Maybe<&2, Sv.Ver>, Sv.Ver, m => Maybe.default(&2, Sv.Ver, m, n), Some{n}, Some{r}, h)
    case False{}:
      semver.ps.none_some({n == r : Sv.Ver}, r, h)

def ps.newest_mid(+n: Sv.Ver, +xs: List<&2, String>, +t: String, +ys: List<&2, String>, h: {Sv.Rel.newest(n, List.append(&2, String, xs, t <> ys)) == True{} : Bool}) -> {Sv.Rel.older(n, Sv.Tag.ver(t)) == True{} : Bool}:
  match xs:
    case Nil{}:
      L.semver.ps.and_l(Sv.Rel.older(n, Sv.Tag.ver(t)), Sv.Rel.newest(n, ys), h)
    case +x <> +r:
      ps.newest_mid(n, r, t, ys, L.semver.ps.and_r(Sv.Rel.older(n, Sv.Tag.ver(x)), Sv.Rel.newest(n, List.append(&2, String, r, t <> ys)), h))

# a release is newer than every version tag
def ps.release_newest(m: Maybe<&2, Sv.Ver>, +xs: List<&2, String>, +t: String, +ys: List<&2, String>, -r: Sv.Ver, +rel: {Sv.Rel.release.of(m, List.append(&2, String, xs, t <> ys)) == Some{r} : Maybe<&2, Sv.Ver>}, +v: Sv.Ver, parsed: {Sv.Tag.ver(t) == Some{v} : Maybe<&2, Sv.Ver>}) -> {Sv.Ver.lt(v, r) == True{} : Bool}:
  match m:
    case None{}:
      semver.ps.none_some({Sv.Ver.lt(v, r) == True{} : Bool}, r, rel)
    case Some{w}:
      match w:
        case Sv.Ver{+a, +b, c}:
          match c:
            case 0n:
              +n = Sv.Rel.next(Sv.Ver{a, b, 0n}, List.append(&2, String, xs, t <> ys))
              +ok = ps.guard_ok(Sv.Rel.newest(n, List.append(&2, String, xs, t <> ys)), n, r, rel)
              %ps.guard_val(Sv.Rel.newest(n, List.append(&2, String, xs, t <> ys)), n, r, rel) : {Sv.Ver.lt(v, _) == True{} : Bool}
              %parsed : {Sv.Rel.older(n, _) == True{} : Bool}
              ps.newest_mid(n, xs, t, ys, ok)
            case 1n+p:
              semver.ps.none_some({Sv.Ver.lt(v, r) == True{} : Bool}, r, rel)

def ps.release_newest_of(c: String, +xs: List<&2, String>, +t: String, +ys: List<&2, String>, -r: Sv.Ver, rel: {Sv.Rel.release(c, List.append(&2, String, xs, t <> ys)) == Some{r} : Maybe<&2, Sv.Ver>}, +v: Sv.Ver, parsed: {Sv.Tag.ver(t) == Some{v} : Maybe<&2, Sv.Ver>}) -> {Sv.Ver.lt(v, r) == True{} : Bool}:
  ps.release_newest(Sv.Ver.parse(c), xs, t, ys, r, rel, v, parsed)

def Laws.semver_release_newest(c, xs, t, ys, r, rel, v, parsed):
  ps.release_newest_of(c, xs, t, ys, r, rel, v, parsed)
