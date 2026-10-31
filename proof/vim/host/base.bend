# eukhe.com's Neovim: lemmas for the host laws (honest, urls)
# ===========================================================
#
# Strings: append and reverse. Sub(u, s): u is a run of s's characters
# (s = a ++ u ++ b), so Spec.within(u, s). The WORD gx reads, and the
# link target cut from it, are runs of the cursor's line.

import Base
import ../../../vim/types.bend as T
import ../../../vim/text.bend as X
import ../../../vim/ex.bend as E
import ../../../laws/vim/base.bend as Laws
import ../../base.bend as L
import ../../base/text.bend as Tx

# Strings
# -------

def Str.app_nil(s: String) -> {String.append(s, SNil{}) == s : String}:
  match s:
    case SNil{}:
      {==}
    case SCon{h, t}:
      Equal.cong(String, String, x => SCon{h, x}, String.append(t, SNil{}), t, Str.app_nil(t))

def Str.assoc(x: String, -y: String, -z: String) -> {String.append(String.append(x, y), z) == String.append(x, String.append(y, z)) : String}:
  match x:
    case SNil{}:
      {==}
    case SCon{h, t}:
      Equal.cong(String, String, v => SCon{h, v}, String.append(String.append(t, y), z), String.append(t, String.append(y, z)), Str.assoc(t, y, z))

def Str.rev_go(s: String, -acc: String) -> {String.reverse.go(s, acc) == String.append(String.reverse.go(s, SNil{}), acc) : String}:
  match s:
    case SNil{}:
      {==}
    case SCon{+h, +t}:
      -r = String.reverse.go(t, SNil{})
      e1 = Str.rev_go(t, SCon{h, acc})
      e2 = Str.rev_go(t, SCon{h, SNil{}})
      e3 = Str.assoc(String.reverse.go(t, SNil{}), SCon{h, SNil{}}, acc)
      %Equal.sym(String, String.reverse.go(t, SCon{h, SNil{}}), String.append(r, SCon{h, SNil{}}), e2) : {String.reverse.go(t, SCon{h, acc}) == String.append(_, acc) : String}
      Equal.trans(String, String.reverse.go(t, SCon{h, acc}), String.append(r, SCon{h, acc}), String.append(String.append(r, SCon{h, SNil{}}), acc), e1, Equal.sym(String, String.append(String.append(r, SCon{h, SNil{}}), acc), String.append(r, SCon{h, acc}), e3))

def Str.rev_app(x: String, +y: String) -> {String.reverse(String.append(x, y)) == String.append(String.reverse(y), String.reverse(x)) : String}:
  match x:
    case SNil{}:
      Equal.sym(String, String.append(String.reverse(y), SNil{}), String.reverse(y), Str.app_nil(String.reverse(y)))
    case SCon{+h, +t}:
      -one = {SCon{h, SNil{}} : String}
      -ry = String.reverse(y)
      -rt = String.reverse(t)
      -rty = String.reverse(String.append(t, y))
      a1 = Str.rev_go(String.append(t, y), one)
      a2 = Equal.cong(String, String, v => String.append(v, one), rty, String.append(ry, rt), Str.rev_app(t, y))
      a3 = Str.assoc(String.reverse(y), String.reverse(t), SCon{h, SNil{}})
      a4 = Equal.cong(String, String, v => String.append(ry, v), String.reverse.go(t, one), String.append(rt, one), Str.rev_go(t, one))
      Equal.trans(String, String.reverse.go(String.append(t, y), one), String.append(rty, one), String.append(ry, String.reverse.go(t, one)), a1,
        Equal.trans(String, String.append(rty, one), String.append(String.append(ry, rt), one), String.append(ry, String.reverse.go(t, one)), a2,
          Equal.trans(String, String.append(String.append(ry, rt), one), String.append(ry, String.append(rt, one)), String.append(ry, String.reverse.go(t, one)), a3,
            Equal.sym(String, String.append(ry, String.reverse.go(t, one)), String.append(ry, String.append(rt, one)), a4))))

def Str.rev_rev(x: String) -> {String.reverse(String.reverse(x)) == x : String}:
  match x:
    case SNil{}:
      {==}
    case SCon{+h, +t}:
      -one = {SCon{h, SNil{}} : String}
      -rt = String.reverse(t)
      b1 = Equal.cong(String, String, v => String.reverse(v), String.reverse.go(t, one), String.append(rt, one), Str.rev_go(t, one))
      b2 = Str.rev_app(String.reverse(t), SCon{h, SNil{}})
      b3 = Equal.cong(String, String, v => SCon{h, v}, String.reverse(rt), t, Str.rev_rev(t))
      Equal.trans(String, String.reverse(String.reverse.go(t, one)), String.reverse(String.append(rt, one)), SCon{h, t}, b1,
        Equal.trans(String, String.reverse(String.append(rt, one)), SCon{h, String.reverse(rt)}, SCon{h, t}, b2, b3))

# Runs
# ----

# u is a run of s: s = a ++ u ++ b
def Sub(u: String, s: String) -> Data:
  Sigma<&2, &2, String, a => Sigma<&2, &2, String, b => {String.append(a, String.append(u, b)) == s : String}>>

def Sub.refl(+s: String) -> Sub(s, s):
  (SNil{}, (SNil{}, Str.app_nil(s)))

def Sub.nil(+s: String) -> Sub(SNil{}, s):
  (SNil{}, (s, {==}))

def Sub.pre(-u: String, +b: String) -> Sub(u, String.append(u, b)):
  (SNil{}, (b, {==}))

def Sub.suf(+a: String, u: String) -> Sub(u, String.append(a, u)):
  (a, (SNil{}, Equal.cong(String, String, x => String.append(a, x), String.append(u, SNil{}), u, Str.app_nil(u))))

def Sub.cons(h: Char, -u: String, -t: String, p: Sub(u, t)) -> Sub(u, SCon{h, t}):
  (a, r) = p
  (b, e) = r
  (SCon{h, a}, (b, Equal.cong(String, String, x => SCon{h, x}, String.append(a, String.append(u, b)), t, e)))

def Sub.cast_l(-u1: String, -u2: String, -s: String, e: {u1 == u2 : String}, p: Sub(u1, s)) -> Sub(u2, s):
  %e : Sub(_, s)
  p

def Sub.cast_r(-u: String, -s1: String, -s2: String, e: {s1 == s2 : String}, p: Sub(u, s1)) -> Sub(u, s2):
  %e : Sub(u, _)
  p

def Sub.trans(u: String, -v: String, -w: String, p: Sub(u, v), q: Sub(v, w)) -> Sub(u, w):
  (+a, r) = p
  (+b, e1) = r
  (+c, r2) = q
  (+d, e2) = r2
  -ub = String.append(u, b)
  -x = String.append(u, String.append(b, d))
  f1 = Str.assoc(c, a, x)
  g1 = Equal.cong(String, String, y => String.append(a, y), String.append(ub, d), x, Str.assoc(u, b, d))
  g2 = Str.assoc(a, ub, d)
  f2 = Equal.trans(String, String.append(a, x), String.append(a, String.append(ub, d)), String.append(String.append(a, ub), d), Equal.sym(String, String.append(a, String.append(ub, d)), String.append(a, x), g1), Equal.sym(String, String.append(String.append(a, ub), d), String.append(a, String.append(ub, d)), g2))
  f3 = Equal.cong(String, String, y => String.append(c, String.append(y, d)), String.append(a, ub), v, e1)
  f4 = Equal.cong(String, String, y => String.append(c, y), String.append(a, x), String.append(String.append(a, ub), d), f2)
  (String.append(c, a), (String.append(b, d),
    Equal.trans(String, String.append(String.append(c, a), x), String.append(c, String.append(a, x)), w, f1,
      Equal.trans(String, String.append(c, String.append(a, x)), String.append(c, String.append(String.append(a, ub), d)), w, f4,
        Equal.trans(String, String.append(c, String.append(String.append(a, ub), d)), String.append(c, String.append(v, d)), w, f3, e2)))))

def Sub.rev(+u: String, -s: String, p: Sub(u, s)) -> Sub(String.reverse(u), String.reverse(s)):
  (+a, r) = p
  (+b, e) = r
  -ra = String.reverse(a)
  -rb = String.reverse(b)
  -ru = String.reverse(u)
  -ub = String.append(u, b)
  g1 = Str.rev_app(a, String.append(u, b))
  g2 = Equal.cong(String, String, y => String.append(y, ra), String.reverse(ub), String.append(rb, ru), Str.rev_app(u, b))
  g3 = Str.assoc(String.reverse(b), String.reverse(u), String.reverse(a))
  g4 = Equal.cong(String, String, y => String.reverse(y), String.append(a, ub), s, e)
  (String.reverse(b), (String.reverse(a),
    Equal.trans(String, String.append(rb, String.append(ru, ra)), String.append(String.append(rb, ru), ra), String.reverse(s), Equal.sym(String, String.append(String.append(rb, ru), ra), String.append(rb, String.append(ru, ra)), g3),
      Equal.trans(String, String.append(String.append(rb, ru), ra), String.append(String.reverse(ub), ra), String.reverse(s), Equal.sym(String, String.append(String.reverse(ub), ra), String.append(String.append(rb, ru), ra), g2),
        Equal.trans(String, String.append(String.reverse(ub), ra), String.reverse(String.append(a, ub)), String.reverse(s), Equal.sym(String, String.reverse(String.append(a, ub)), String.append(String.reverse(ub), ra), g1), g4)))))

# a run of a reversed string, reversed, is a run of the string
def Sub.unrev(u: String, +s: String, p: Sub(u, String.reverse(s))) -> Sub(String.reverse(u), s):
  Sub.cast_r(String.reverse(u), String.reverse(String.reverse(s)), s, Str.rev_rev(s), Sub.rev(u, String.reverse(s), p))

# Within
# ------

def Char.eq_refl(c: Char) -> {Char.is_eq(c, c) == True{} : Bool}:
  match c:
    case Chr{+x}:
      %Equal.sym(Cmp, U32.cmp(x, x), EQ{}, Tx.U32.cmp_refl(x)) : {Cmp.is_eq(_) == True{} : Bool}
      {==}

def Prefix.app(u: String, -b: String) -> {Laws.Spec.prefix(u, String.append(u, b)) == True{} : Bool}:
  match u:
    case SNil{}:
      {==}
    case SCon{+h, t}:
      L.And.intro(Char.is_eq(h, h), Laws.Spec.prefix(t, String.append(t, b)), Char.eq_refl(h), Prefix.app(t, b))

# only the empty string starts the empty string
def Within.nil(u: String, hp: {Laws.Spec.prefix(u, SNil{}) == True{} : Bool}) -> {Laws.Spec.within(u, SNil{}) == True{} : Bool}:
  match u:
    case SNil{}:
      {==}
    case SCon{h, t}:
      L.Bool.false_true({String.is_empty(SCon{h, t}) == True{} : Bool}, hp)

def Within.pre(+u: String, s: String, hp: {Laws.Spec.prefix(u, s) == True{} : Bool}) -> {Laws.Spec.within(u, s) == True{} : Bool}:
  match s:
    case SNil{}:
      Within.nil(u, hp)
    case SCon{+h, +t}:
      L.Or.l(Laws.Spec.prefix(u, SCon{h, t}), Laws.Spec.within(u, t), hp)

def Within.app(a: String, +u: String, +b: String) -> {Laws.Spec.within(u, String.append(a, String.append(u, b))) == True{} : Bool}:
  match a:
    case SNil{}:
      Within.pre(u, String.append(u, b), Prefix.app(u, b))
    case SCon{+h, +t}:
      L.Or.r(Laws.Spec.prefix(u, SCon{h, String.append(t, String.append(u, b))}), Laws.Spec.within(u, String.append(t, String.append(u, b))), Within.app(t, u, b))

def Sub.within(+u: String, -s: String, p: Sub(u, s)) -> {Laws.Spec.within(u, s) == True{} : Bool}:
  (a, r) = p
  (b, e) = r
  %e : {Laws.Spec.within(u, _) == True{} : Bool}
  Within.app(a, u, b)

# Choices
# -------

def When.both(-R: Type, -P: R -> Type, b: Bool, -f: Unit -> R, -g: Unit -> R, pf: P(f(Unit{})), pg: P(g(Unit{}))) -> P(X.Bool.when(R, b, f, g)):
  match b:
    case True{}:
      pg
    case False{}:
      pf

def Pick.both(-R: Type, -P: R -> Type, b: Bool, -x: R, -y: R, px: P(x), py: P(y)) -> P(Bool.pick(R, b, x, y)):
  match b:
    case True{}:
      px
    case False{}:
      py

# The link under the cursor
# -------------------------

# rev(h : acc) ++ t is rev(acc) ++ (h : t)
def Str.rev_step(+acc: String, -h: Char, -t: String) -> {String.append(String.reverse(SCon{h, acc}), t) == String.append(String.reverse(acc), SCon{h, t}) : String}:
  -one = {SCon{h, SNil{}} : String}
  -ra = String.reverse(acc)
  e1 = Equal.cong(String, String, v => String.append(v, t), String.reverse.go(acc, one), String.append(ra, one), Str.rev_go(acc, one))
  Equal.trans(String, String.append(String.reverse.go(acc, one), t), String.append(String.append(ra, one), t), String.append(ra, SCon{h, t}), e1, Str.assoc(String.reverse(acc), one, t))

# t is a run of a ++ (h : t)
def Sub.tail(+a: String, +h: Char, +t: String) -> Sub(t, String.append(a, SCon{h, t})):
  Sub.trans(t, SCon{h, t}, String.append(a, SCon{h, t}), Sub.cons(h, t, t, Sub.refl(t)), Sub.suf(a, SCon{h, t}))

# the WORD Link.big cuts is a run of the line
def Big.go(s: String, +c: Nat, +i: Nat, +acc: String, +ended: Bool, -line: String, +hs: Sub(String.append(String.reverse(acc), s), line)) -> Sub(E.Link.big.go(s, c, i, acc, ended), line):
  match s:
    case SNil{}:
      Sub.cast_l(String.append(String.reverse(acc), SNil{}), String.reverse(acc), line, Str.app_nil(String.reverse(acc)), hs)
    case SCon{+h, +t}:
      -ra = String.reverse(acc)
      -ht = {SCon{h, t} : String}
      pf = Big.go(t, c, 1n+i, SCon{h, acc}, False{}, line, Sub.cast_l(String.append(ra, ht), String.append(String.reverse(SCon{h, acc}), t), line, Equal.sym(String, String.append(String.reverse(SCon{h, acc}), t), String.append(ra, ht), Str.rev_step(acc, h, t)), hs))
      pa = Big.go(t, c, 1n+i, SNil{}, False{}, line, Sub.trans(t, String.append(ra, ht), line, Sub.tail(String.reverse(acc), h, t), hs))
      pb = Sub.trans(String.reverse(acc), String.append(ra, ht), line, Sub.pre(ra, SCon{h, t}), hs)
      pg = When.both(String, r => Sub(r, line), Nat.is_gt(i, c), u => E.Link.big.go(t, c, 1n+i, SNil{}, False{}), u => String.reverse(acc), pa, pb)
      When.both(String, r => Sub(r, line), Nat.is_eq(X.Char.cls(h, True{}), 0n), u => E.Link.big.go(t, c, 1n+i, SCon{h, acc}, False{}), u => X.Bool.when(String, Nat.is_gt(i, c), u => E.Link.big.go(t, c, 1n+i, SNil{}, False{}), u => String.reverse(acc)), pf, pg)

# what Link.inner.go has read: open, rev(acc) ++ s is a run of w; else s
# and rev(acc) are
def Inner.inv(w: String, s: String, acc: String, open: Bool) -> Data:
  match open:
    case True{}:
      Sub(String.append(String.reverse(acc), s), w)
    case False{}:
      Sigma<&2, &2, Sub(s, w), _ => Sub(String.reverse(acc), w)>

# the text inside a Markdown link's "(..)" is a run of the WORD
def Inner.go(s: String, +acc: String, +open: Bool, -w: String, +hs: Inner.inv(w, s, acc, open)) -> Sub(E.Link.inner.go(s, acc, open), w):
  match s:
    case SNil{}:
      match open:
        case True{}:
          Sub.cast_l(String.append(String.reverse(acc), SNil{}), String.reverse(acc), w, Str.app_nil(String.reverse(acc)), hs)
        case False{}:
          (h1, h2) = hs
          h2
    case SCon{+h, +t}:
      match open:
        case True{}:
          -ra = String.reverse(acc)
          -ht = {SCon{h, t} : String}
          pf = Inner.go(t, SCon{h, acc}, True{}, w, Sub.cast_l(String.append(ra, ht), String.append(String.reverse(SCon{h, acc}), t), w, Equal.sym(String, String.append(String.reverse(SCon{h, acc}), t), String.append(ra, ht), Str.rev_step(acc, h, t)), hs))
          pg = Sub.trans(String.reverse(acc), String.append(ra, ht), w, Sub.pre(ra, SCon{h, t}), hs)
          When.both(String, r => Sub(r, w), Char.is_eq(h, ')'), u => E.Link.inner.go(t, SCon{h, acc}, True{}), u => String.reverse(acc), pf, pg)
        case False{}:
          (+h1, +h2) = hs
          +st = Sub.trans(t, SCon{h, t}, w, Sub.cons(h, t, t, Sub.refl(t)), h1)
          pf = Inner.go(t, acc, False{}, w, (st, h2))
          pg = Inner.go(t, SNil{}, True{}, w, st)
          When.both(String, r => Sub(r, w), Char.is_eq(h, '('), u => E.Link.inner.go(t, acc, False{}), u => E.Link.inner.go(t, SNil{}, True{}), pf, pg)

# trimming brackets and punctuation keeps a run
def Trim.l(s: String) -> Sub(E.Link.trim.l(s), s):
  match s:
    case SNil{}:
      Sub.refl(SNil{})
    case SCon{+h, +t}:
      When.both(String, r => Sub(r, SCon{h, t}), E.Link.opens(h), u => SCon{h, t}, u => E.Link.trim.l(t), Sub.refl(SCon{h, t}), Sub.cons(h, E.Link.trim.l(t), t, Trim.l(t)))

def Trim.rl(s: String) -> Sub(E.Link.trim.rl(s), s):
  match s:
    case SNil{}:
      Sub.refl(SNil{})
    case SCon{+h, +t}:
      When.both(String, r => Sub(r, SCon{h, t}), E.Link.closes(h), u => SCon{h, t}, u => E.Link.trim.rl(t), Sub.refl(SCon{h, t}), Sub.cons(h, E.Link.trim.rl(t), t, Trim.rl(t)))

def Trim.all(+w: String) -> Sub(E.Link.trim(w), w):
  +a = E.Link.trim.l(w)
  +b = E.Link.trim.r(a)
  +c = E.Link.trim.l(String.reverse(b))
  p1 = Trim.l(w)
  p2 = Sub.unrev(E.Link.trim.rl(String.reverse(a)), a, Trim.rl(String.reverse(a)))
  p3 = Sub.unrev(c, b, Trim.l(String.reverse(b)))
  Sub.trans(String.reverse(c), b, w, p3, Sub.trans(b, a, w, p2, p1))

def Target.sub(+w: String) -> Sub(E.Link.target(w), w):
  +inner = E.Link.inner.go(w, SNil{}, False{})
  Pick.both(String, r => Sub(r, w), String.is_empty(inner), E.Link.trim(w), inner, Trim.all(w), Inner.go(w, SNil{}, False{}, w, (Sub.refl(w), Sub.nil(w))))

# what gx opens is a run of the cursor's line
def Gx.sub(+line: String, +c: Nat) -> Sub(E.Link.target(E.Link.big(line, c)), line):
  +big = E.Link.big(line, c)
  Sub.trans(E.Link.target(big), big, line, Target.sub(big), Big.go(line, c, 0n, SNil{}, False{}, line, Sub.refl(line)))
