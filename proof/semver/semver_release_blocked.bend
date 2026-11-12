# eukhe: the proof of LAW semver_release_blocked

import Base
import ../../bend/semver.bend as Sv
import ../../laws/semver.bend as Semver

# PROOF of LAW semver_release_blocked: the workspace version reads as
# X.Y.0, so Rel.release is Rel.guard of Rel.newest(n, tags), n the next
# release of X.Y; no release means Rel.newest is False (rbl.guard), so some
# tag names a version v that n is not newer than (Rel.older: not v < n),
# that is n <= v (rbl.top, by induction on the tags).

def rbl.Found(tags: List<&2, String>, n: Sv.Ver) -> Type:
  &xs: List<&2, String> -> &t: String -> &ys: List<&2, String> -> &v: Sv.Ver -> {tags == List.append(&2, String, xs, t <> ys) : List<&2, String>} & ({Sv.Tag.ver(t) == Some{v} : Maybe<&2, Sv.Ver>} & {Sv.Ver.le(n, v) == True{} : Bool})

def rbl.IfS(m: Maybe<&2, Sv.Ver>, G: Type) -> Type:
  match m:
    case None{}:
      G
    case Some{x}:
      Unit

def rbl.IfF(b: Bool, G: Type) -> Type:
  match b:
    case True{}:
      Unit
    case False{}:
      G

# a guard that answers nothing was given False
def rbl.guard(ok: Bool, -n: Sv.Ver, e: {Sv.Rel.guard(ok, n) == None{} : Maybe<&2, Sv.Ver>}) -> {ok == False{} : Bool}:
  match ok:
    case True{}:
      %e : rbl.IfS(_, {True{} == False{} : Bool})
      Unit{}
    case False{}:
      {==}

# a tag found in r is found in t <> r
def rbl.cons(+t0: String, -r: List<&2, String>, -n: Sv.Ver, f: rbl.Found(r, n)) -> rbl.Found(t0 <> r, n):
  (+xs, (+t, (+ys, (+v, (e1, e2))))) = f
  (t0 <> xs, (t, (ys, (v, (Equal.cong(List<&2, String>, List<&2, String>, l => t0 <> l, r, List.append(&2, String, xs, t <> ys), e1), e2)))))

def rbl.at_k(k: Bool, +n: Sv.Ver, +v: Sv.Ver, +t: String, +r: List<&2, String>, ek: {Sv.Ver.le(n, v) == k : Bool}, em: {Sv.Tag.ver(t) == Some{v} : Maybe<&2, Sv.Ver>}, h: {Bool.and(Bool.not(k), Sv.Rel.newest(n, r)) == False{} : Bool}, ih: {Sv.Rel.newest(n, r) == False{} : Bool} -> rbl.Found(r, n)) -> rbl.Found(t <> r, n):
  match k:
    case True{}:
      (Nil{}, (t, (r, (v, ({==}, (em, ek))))))
    case False{}:
      rbl.cons(t, r, n, ih(h))

def rbl.at(m: Maybe<&2, Sv.Ver>, +n: Sv.Ver, +t: String, +r: List<&2, String>, em: {Sv.Tag.ver(t) == m : Maybe<&2, Sv.Ver>}, h: {Bool.and(Sv.Rel.older(n, m), Sv.Rel.newest(n, r)) == False{} : Bool}, ih: {Sv.Rel.newest(n, r) == False{} : Bool} -> rbl.Found(r, n)) -> rbl.Found(t <> r, n):
  match m:
    case None{}:
      rbl.cons(t, r, n, ih(h))
    case Some{+v}:
      rbl.at_k(Sv.Ver.le(n, v), n, v, t, r, {==}, em, h, ih)

# n is not newer than every version tag: some tag names n or a newer version
def rbl.top(+n: Sv.Ver, tags: List<&2, String>, h: {Sv.Rel.newest(n, tags) == False{} : Bool}) -> rbl.Found(tags, n):
  match tags:
    case Nil{}:
      %h : rbl.IfF(_, rbl.Found(Nil{}, n))
      Unit{}
    case +t <> +r:
      rbl.at(Sv.Tag.ver(t), n, t, r, {==}, h, e => rbl.top(n, r, e))

def rbl.main(c: String, +a: Nat, +b: Nat, +tags: List<&2, String>, parsed: {Sv.Ver.parse(c) == Some{Sv.Ver{a, b, 0n}} : Maybe<&2, Sv.Ver>}, none: {Sv.Rel.release(c, tags) == None{} : Maybe<&2, Sv.Ver>}) -> rbl.Found(tags, Sv.Rel.next(Sv.Ver{a, b, 0n}, tags)):
  +n = Sv.Rel.next(Sv.Ver{a, b, 0n}, tags)
  +e = Equal.trans(Maybe<&2, Sv.Ver>, Sv.Rel.release.of(Some{Sv.Ver{a, b, 0n}}, tags), Sv.Rel.release(c, tags), None{}, Equal.cong(Maybe<&2, Sv.Ver>, Maybe<&2, Sv.Ver>, m => Sv.Rel.release.of(m, tags), Some{Sv.Ver{a, b, 0n}}, Sv.Ver.parse(c), Equal.sym(Maybe<&2, Sv.Ver>, Sv.Ver.parse(c), Some{Sv.Ver{a, b, 0n}}, parsed)), none)
  rbl.top(n, tags, rbl.guard(Sv.Rel.newest(n, tags), n, e))

def Semver.semver_release_blocked(c, a, b, tags, parsed, none):
  rbl.main(c, a, b, tags, parsed, none)
