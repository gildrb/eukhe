# eukhe: the proof of LAW semver_next_no_skip

import Base
import ../../bend/semver.bend as Sv
import ../../laws/semver.bend as Semver
import ../base/logic/bool.bend as LLogicBool
import ../base/logic/nat.bend as LLogicNat

# PROOF of LAW semver_next_no_skip: Rel.next(X.Y.Z, tags) is X.Y.P with P
# = Rel.after(Rel.top(..)); P = 1 + p means Rel.top answered p (nsk.after).
# Rel.top keeps, for each tag that names a version of the series, the
# larger of its patch and the rest's answer (Num.max is one of its two
# numbers: nsk.max), so the p it answers is the patch of some tag of the
# series (nsk.top, by induction on the tags).

def nsk.Found(tags: List<&2, String>, x: Nat, y: Nat, p: Nat) -> Type:
  &xs: List<&2, String> -> &t: String -> &ys: List<&2, String> -> {tags == List.append(&2, String, xs, t <> ys) : List<&2, String>} & {Sv.Tag.ver(t) == Some{Sv.Ver{x, y, p}} : Maybe<&2, Sv.Ver>}

def nsk.IfS(m: Maybe<&2, Nat>, G: Type) -> Type:
  match m:
    case None{}:
      Unit
    case Some{q}:
      G

def nsk.IfZ(n: Nat, G: Type) -> Type:
  match n:
    case 0n:
      Unit
    case 1n+q:
      G

def nsk.val(m: Maybe<&2, Nat>) -> Nat:
  match m:
    case None{}:
      0n
    case Some{q}:
      q

def nsk.pred(n: Nat) -> Nat:
  match n:
    case 0n:
      0n
    case 1n+q:
      q

def nsk.maj(v: Sv.Ver) -> Nat:
  match v:
    case Sv.Ver{a, b, c}:
      a

def nsk.min(v: Sv.Ver) -> Nat:
  match v:
    case Sv.Ver{a, b, c}:
      b

def nsk.unsome(-x: Nat, -y: Nat, e: {Some{x} == Some{y} : Maybe<&2, Nat>}) -> {x == y : Nat}:
  Equal.cong(Maybe<&2, Nat>, Nat, nsk.val, Some{x}, Some{y}, e)

# Num.max answers one of its two numbers
def nsk.sel(b: Bool, x: Nat, y: Nat) -> Nat:
  match b:
    case True{}:
      x
    case False{}:
      y

def nsk.sel_succ(b: Bool, -x: Nat, -y: Nat) -> {1n+nsk.sel(b, x, y) == nsk.sel(b, 1n+x, 1n+y) : Nat}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def nsk.max(x: Nat, y: Nat) -> {Sv.Num.max(x, y) == nsk.sel(Sv.Num.le(y, x), x, y) : Nat}:
  match x y:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      {==}
    case 1n+(+p) 1n+(+q):
      Equal.trans(Nat, 1n+Sv.Num.max(p, q), 1n+nsk.sel(Sv.Num.le(q, p), p, q), nsk.sel(Sv.Num.le(q, p), 1n+p, 1n+q), Equal.cong(Nat, Nat, n => 1n+n, Sv.Num.max(p, q), nsk.sel(Sv.Num.le(q, p), p, q), nsk.max(p, q)), nsk.sel_succ(Sv.Num.le(q, p), p, q))

# a tag found in r is found in t0 <> r
def nsk.cons(+t0: String, -r: List<&2, String>, -x: Nat, -y: Nat, -p: Nat, f: nsk.Found(r, x, y, p)) -> nsk.Found(t0 <> r, x, y, p):
  (+xs, (+t, (+ys, (e1, e2)))) = f
  (t0 <> xs, (t, (ys, (Equal.cong(List<&2, String>, List<&2, String>, l => t0 <> l, r, List.append(&2, String, xs, t <> ys), e1), e2))))

# the tag t names va.vb.vc, which is a.b.p
def nsk.here_eq(+t: String, -a: Nat, -b: Nat, -p: Nat, -va: Nat, -vb: Nat, -vc: Nat, em: {Sv.Tag.ver(t) == Some{Sv.Ver{va, vb, vc}} : Maybe<&2, Sv.Ver>}, ea: {a == va : Nat}, eb: {b == vb : Nat}, ep: {vc == p : Nat}) -> {Sv.Tag.ver(t) == Some{Sv.Ver{a, b, p}} : Maybe<&2, Sv.Ver>}:
  %Equal.sym(Nat, a, va, ea) : {Sv.Tag.ver(t) == Some{Sv.Ver{_, b, p}} : Maybe<&2, Sv.Ver>}
  %Equal.sym(Nat, b, vb, eb) : {Sv.Tag.ver(t) == Some{Sv.Ver{va, _, p}} : Maybe<&2, Sv.Ver>}
  %ep : {Sv.Tag.ver(t) == Some{Sv.Ver{va, vb, _}} : Maybe<&2, Sv.Ver>}
  em

# the tag t names a.b.p: found at the head
def nsk.here(+t: String, +r: List<&2, String>, -a: Nat, -b: Nat, -p: Nat, -va: Nat, -vb: Nat, -vc: Nat, em: {Sv.Tag.ver(t) == Some{Sv.Ver{va, vb, vc}} : Maybe<&2, Sv.Ver>}, ea: {a == va : Nat}, eb: {b == vb : Nat}, ep: {vc == p : Nat}) -> nsk.Found(t <> r, a, b, p):
  (Nil{}, (t, (r, ({==}, nsk.here_eq(t, a, b, p, va, vb, vc, em, ea, eb, ep)))))

# the larger of the tag's patch vc and the rest's answer q is p
def nsk.pick(sb: Bool, +t: String, +r: List<&2, String>, +a: Nat, +b: Nat, +c: Nat, +p: Nat, -va: Nat, -vb: Nat, +vc: Nat, +q: Nat, em: {Sv.Tag.ver(t) == Some{Sv.Ver{va, vb, vc}} : Maybe<&2, Sv.Ver>}, ea: {a == va : Nat}, eb: {b == vb : Nat}, er: {Sv.Rel.top(Sv.Ver{a, b, c}, r) == Some{q} : Maybe<&2, Nat>}, hs: {nsk.sel(sb, vc, q) == p : Nat}, ih: {Sv.Rel.top(Sv.Ver{a, b, c}, r) == Some{p} : Maybe<&2, Nat>} -> nsk.Found(r, a, b, p)) -> nsk.Found(t <> r, a, b, p):
  match sb:
    case True{}:
      nsk.here(t, r, a, b, p, va, vb, vc, em, ea, eb, hs)
    case False{}:
      nsk.cons(t, r, a, b, p, ih(Equal.trans(Maybe<&2, Nat>, Sv.Rel.top(Sv.Ver{a, b, c}, r), Some{q}, Some{p}, er, Equal.cong(Nat, Maybe<&2, Nat>, n => Some{n}, q, p, hs))))

# the tag names va.vb.vc; it is of the series a.b exactly when k
def nsk.keep(k: Bool, +t: String, +r: List<&2, String>, +a: Nat, +b: Nat, +c: Nat, +p: Nat, +va: Nat, +vb: Nat, +vc: Nat, em: {Sv.Tag.ver(t) == Some{Sv.Ver{va, vb, vc}} : Maybe<&2, Sv.Ver>}, +ek: {Bool.and(Nat.is_eq(a, va), Nat.is_eq(b, vb)) == k : Bool}, acc: Maybe<&2, Nat>, ea: {Sv.Rel.top(Sv.Ver{a, b, c}, r) == acc : Maybe<&2, Nat>}, h: {Sv.Rel.keep(k, vc, acc) == Some{p} : Maybe<&2, Nat>}, ih: {Sv.Rel.top(Sv.Ver{a, b, c}, r) == Some{p} : Maybe<&2, Nat>} -> nsk.Found(r, a, b, p)) -> nsk.Found(t <> r, a, b, p):
  match k:
    case True{}:
      match acc:
        case None{}:
          +e1 = LLogicNat.semver.ps.eq_true(a, va, LLogicBool.semver.ps.and_l(Nat.is_eq(a, va), Nat.is_eq(b, vb), ek))
          +e2 = LLogicNat.semver.ps.eq_true(b, vb, LLogicBool.semver.ps.and_r(Nat.is_eq(a, va), Nat.is_eq(b, vb), ek))
          nsk.here(t, r, a, b, p, va, vb, vc, em, e1, e2, nsk.unsome(vc, p, h))
        case Some{+q}:
          +e1 = LLogicNat.semver.ps.eq_true(a, va, LLogicBool.semver.ps.and_l(Nat.is_eq(a, va), Nat.is_eq(b, vb), ek))
          +e2 = LLogicNat.semver.ps.eq_true(b, vb, LLogicBool.semver.ps.and_r(Nat.is_eq(a, va), Nat.is_eq(b, vb), ek))
          +hm = Equal.trans(Nat, nsk.sel(Sv.Num.le(q, vc), vc, q), Sv.Num.max(vc, q), p, Equal.sym(Nat, Sv.Num.max(vc, q), nsk.sel(Sv.Num.le(q, vc), vc, q), nsk.max(vc, q)), nsk.unsome(Sv.Num.max(vc, q), p, h))
          nsk.pick(Sv.Num.le(q, vc), t, r, a, b, c, p, va, vb, vc, q, em, e1, e2, ea, hm, ih)
    case False{}:
      nsk.cons(t, r, a, b, p, ih(Equal.trans(Maybe<&2, Nat>, Sv.Rel.top(Sv.Ver{a, b, c}, r), acc, Some{p}, ea, h)))

def nsk.add(m: Maybe<&2, Sv.Ver>, +t: String, +r: List<&2, String>, +a: Nat, +b: Nat, +c: Nat, +p: Nat, em: {Sv.Tag.ver(t) == m : Maybe<&2, Sv.Ver>}, acc: Maybe<&2, Nat>, ea: {Sv.Rel.top(Sv.Ver{a, b, c}, r) == acc : Maybe<&2, Nat>}, h: {Sv.Rel.add(Sv.Ver{a, b, c}, m, acc) == Some{p} : Maybe<&2, Nat>}, ih: {Sv.Rel.top(Sv.Ver{a, b, c}, r) == Some{p} : Maybe<&2, Nat>} -> nsk.Found(r, a, b, p)) -> nsk.Found(t <> r, a, b, p):
  match m:
    case None{}:
      nsk.cons(t, r, a, b, p, ih(Equal.trans(Maybe<&2, Nat>, Sv.Rel.top(Sv.Ver{a, b, c}, r), acc, Some{p}, ea, h)))
    case Some{v}:
      match v:
        case Sv.Ver{+va, +vb, +vc}:
          nsk.keep(Bool.and(Nat.is_eq(a, va), Nat.is_eq(b, vb)), t, r, a, b, c, p, va, vb, vc, em, {==}, acc, ea, h, ih)

# the highest patch Rel.top answers is the patch of a tag of the series
def nsk.top(+a: Nat, +b: Nat, +c: Nat, +p: Nat, tags: List<&2, String>, h: {Sv.Rel.top(Sv.Ver{a, b, c}, tags) == Some{p} : Maybe<&2, Nat>}) -> nsk.Found(tags, a, b, p):
  match tags:
    case Nil{}:
      %h : nsk.IfS(_, nsk.Found(Nil{}, a, b, p))
      Unit{}
    case +t <> +r:
      nsk.add(Sv.Tag.ver(t), t, r, a, b, c, p, {==}, Sv.Rel.top(Sv.Ver{a, b, c}, r), {==}, h, e => nsk.top(a, b, c, p, r, e))

# a next patch 1 + p is the answer p of Rel.top
def nsk.after(m: Maybe<&2, Nat>, +p: Nat, e: {Sv.Rel.after(m) == 1n+p : Nat}) -> {m == Some{p} : Maybe<&2, Nat>}:
  match m:
    case None{}:
      %e : nsk.IfZ(_, {None{} == Some{p} : Maybe<&2, Nat>})
      Unit{}
    case Some{q}:
      Equal.cong(Nat, Maybe<&2, Nat>, n => Some{n}, q, p, Equal.cong(Nat, Nat, nsk.pred, 1n+q, 1n+p, e))

def nsk.main(+s: Sv.Ver, +tags: List<&2, String>, +x: Nat, +y: Nat, +p: Nat, +nx: {Sv.Rel.next(s, tags) == Sv.Ver{x, y, 1n+p} : Sv.Ver}) -> nsk.Found(tags, x, y, p):
  match s:
    case Sv.Ver{+a, +b, +c}:
      +ex = Equal.cong(Sv.Ver, Nat, nsk.maj, Sv.Rel.next(Sv.Ver{a, b, c}, tags), Sv.Ver{x, y, 1n+p}, nx)
      +ey = Equal.cong(Sv.Ver, Nat, nsk.min, Sv.Rel.next(Sv.Ver{a, b, c}, tags), Sv.Ver{x, y, 1n+p}, nx)
      +ep = Equal.cong(Sv.Ver, Nat, Sv.Ver.patch, Sv.Rel.next(Sv.Ver{a, b, c}, tags), Sv.Ver{x, y, 1n+p}, nx)
      %ex : nsk.Found(tags, _, y, p)
      %ey : nsk.Found(tags, a, _, p)
      nsk.top(a, b, c, p, tags, nsk.after(Sv.Rel.top(Sv.Ver{a, b, c}, tags), p, ep))

def Semver.semver_next_no_skip(s, tags, x, y, p, nx):
  nsk.main(s, tags, x, y, p, nx)
