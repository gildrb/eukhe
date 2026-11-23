# eukhe.com's Neovim: what an Oil listing holds
# =============================================

import Base
import ../../../vim/types.bend as T
import ../../../vim/text.bend as X
import ../../../vim/buf.bend as B
import ../../../laws/vim/base.bend as Laws
import ../../base.bend as L
import ../../base/text.bend as Tx
import ../buffers/real.bend as Rb
import ../screen/base.bend as Sb
import ./str.bend as Str

# Bool algebra
# ------------

def Bag.and_t(a: Bool) -> {Bool.and(a, True{}) == a : Bool}:
  match a:
    case False{}:
      {==}
    case True{}:
      {==}

def Bag.and_f(a: Bool, -b: Bool, e: {b == False{} : Bool}) -> {Bool.and(a, b) == False{} : Bool}:
  match a:
    case False{}:
      {==}
    case True{}:
      e

def Bag.assoc(a: Bool, b: Bool, c: Bool) -> {Bool.and(Bool.and(a, b), c) == Bool.and(a, Bool.and(b, c)) : Bool}:
  match a b:
    case False{} _:
      {==}
    case True{} False{}:
      {==}
    case True{} True{}:
      {==}

# a & (b & c) == (b & a) & c
def Bag.rot(a: Bool, b: Bool, c: Bool) -> {Bool.and(a, Bool.and(b, c)) == Bool.and(Bool.and(b, a), c) : Bool}:
  match a b:
    case False{} False{}:
      {==}
    case False{} True{}:
      {==}
    case True{} False{}:
      {==}
    case True{} True{}:
      {==}

def Bag.idem(a: Bool, c: Bool) -> {Bool.and(a, Bool.and(a, c)) == Bool.and(a, c) : Bool}:
  match a:
    case False{}:
      {==}
    case True{}:
      {==}

def Bag.swap4(a: Bool, b: Bool, c: Bool, d: Bool) -> {Bool.and(Bool.and(a, b), Bool.and(c, d)) == Bool.and(Bool.and(a, c), Bool.and(b, d)) : Bool}:
  match a b c:
    case False{} False{} False{}:
      {==}
    case False{} False{} True{}:
      {==}
    case False{} True{} False{}:
      {==}
    case False{} True{} True{}:
      {==}
    case True{} False{} False{}:
      {==}
    case True{} False{} True{}:
      {==}
    case True{} True{} False{}:
      {==}
    case True{} True{} True{}:
      {==}

# merge step, y first: (y & a) & (X & t) == a & (X & (y & t))
def Bag.mfalse(y: Bool, a: Bool, x: Bool, t: Bool) -> {Bool.and(Bool.and(y, a), Bool.and(x, t)) == Bool.and(a, Bool.and(x, Bool.and(y, t))) : Bool}:
  match y a x:
    case False{} False{} _:
      {==}
    case False{} True{} False{}:
      {==}
    case False{} True{} True{}:
      {==}
    case True{} False{} _:
      {==}
    case True{} True{} False{}:
      {==}
    case True{} True{} True{}:
      {==}

# merge step, x first: (x & a) & (xt & Y) == a & ((x & xt) & Y)
def Bag.mtrue(x: Bool, a: Bool, xt: Bool, y: Bool) -> {Bool.and(Bool.and(x, a), Bool.and(xt, y)) == Bool.and(a, Bool.and(Bool.and(x, xt), y)) : Bool}:
  match x a:
    case False{} False{}:
      {==}
    case False{} True{}:
      {==}
    case True{} False{}:
      {==}
    case True{} True{}:
      {==}

def Bag.or_not(e: Bool, a: Bool) -> {Bool.or(e, Bool.not(a)) == Bool.not(Bool.and(Bool.not(e), a)) : Bool}:
  match e:
    case False{}:
      {==}
    case True{}:
      {==}

def Bag.not_true(b: Bool, e: {Bool.not(b) == True{} : Bool}) -> {b == False{} : Bool}:
  match b:
    case False{}:
      {==}
    case True{}:
      L.Bool.false_true({True{} == False{} : Bool}, e)

# Predicates over entries
# -----------------------

type Bag.Q is Data:
  QChild{d: String, fs: List<&2, T.Buf>}
  QNe{x: String}
  QOpt{q: Bag.Q}

def Bag.ok(q: Bag.Q, +h: String) -> Bool:
  match q:
    case QChild{d, fs}:
      Laws.Spec.is_child(d, h, fs)
    case QNe{x}:
      Bool.not(String.eq(h, x))
    case QOpt{r}:
      Bool.or(String.is_empty(h), Bag.ok(r, h))

def Bag.All(+q: Bag.Q, xs: List<&2, String>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{h, t}:
      Bool.and(Bag.ok(q, h), Bag.All(q, t))

# Sorting keeps what holds of every entry
# ---------------------------------------

def Bag.app(+q: Bag.Q, xs: List<&2, String>, +ys: List<&2, String>) -> {Bag.All(q, List.append(&2, String, xs, ys)) == Bool.and(Bag.All(q, xs), Bag.All(q, ys)) : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      %Equal.sym(Bool, Bag.All(q, List.append(&2, String, t, ys)), Bool.and(Bag.All(q, t), Bag.All(q, ys)), Bag.app(q, t, ys)) : {Bool.and(Bag.ok(q, h), _) == Bool.and(Bool.and(Bag.ok(q, h), Bag.All(q, t)), Bag.All(q, ys)) : Bool}
      Equal.sym(Bool, Bool.and(Bool.and(Bag.ok(q, h), Bag.All(q, t)), Bag.All(q, ys)), Bool.and(Bag.ok(q, h), Bool.and(Bag.All(q, t), Bag.All(q, ys))), Bag.assoc(Bag.ok(q, h), Bag.All(q, t), Bag.All(q, ys)))

def Bag.rev(+q: Bag.Q, xs: List<&2, String>, +acc: List<&2, String>) -> {Bag.All(q, List.reverse.go(&2, String, xs, acc)) == Bool.and(Bag.All(q, xs), Bag.All(q, acc)) : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      Equal.trans(Bool, Bag.All(q, List.reverse.go(&2, String, t, h <> acc)), Bool.and(Bag.All(q, t), Bool.and(Bag.ok(q, h), Bag.All(q, acc))), Bool.and(Bool.and(Bag.ok(q, h), Bag.All(q, t)), Bag.All(q, acc)), Bag.rev(q, t, h <> acc), Bag.rot(Bag.All(q, t), Bag.ok(q, h), Bag.All(q, acc)))

def Bag.tri(+q: Bag.Q, st: List<&2, String> & List<&2, String> & List<&2, String>) -> Bool:
  (acc, xs, ys) = st
  Bool.and(Bag.All(q, acc), Bool.and(Bag.All(q, xs), Bag.All(q, ys)))

def Bag.and2(-a: Bool, -b: Bool, -c: Bool, -d: Bool, e1: {a == b : Bool}, e2: {c == d : Bool}) -> {Bool.and(a, c) == Bool.and(b, d) : Bool}:
  %e1 : {Bool.and(a, c) == Bool.and(_, d) : Bool}
  %e2 : {Bool.and(a, c) == Bool.and(a, _) : Bool}
  {==}

def Bag.step(+q: Bag.Q, +acc: List<&2, String>, +x: String, +xt: List<&2, String>, +y: String, +yt: List<&2, String>, b: Bool)
  -> {Bag.tri(q, List.merge.step(String, acc, x, xt, y, yt, b)) == Bool.and(Bag.All(q, acc), Bool.and(Bag.All(q, x <> xt), Bag.All(q, y <> yt))) : Bool}:
  match b:
    case False{}:
      Bag.mfalse(Bag.ok(q, y), Bag.All(q, acc), Bool.and(Bag.ok(q, x), Bag.All(q, xt)), Bag.All(q, yt))
    case True{}:
      Bag.mtrue(Bag.ok(q, x), Bag.All(q, acc), Bag.All(q, xt), Bool.and(Bag.ok(q, y), Bag.All(q, yt)))

def Bag.merge0(+q: Bag.Q, +acc: List<&2, String>, +xs: List<&2, String>, +ys: List<&2, String>)
  -> {Bag.All(q, List.reverse.go(&2, String, acc, List.append(&2, String, xs, ys))) == Bool.and(Bag.All(q, acc), Bool.and(Bag.All(q, xs), Bag.All(q, ys))) : Bool}:
  Equal.trans(Bool, Bag.All(q, List.reverse.go(&2, String, acc, List.append(&2, String, xs, ys))), Bool.and(Bag.All(q, acc), Bag.All(q, List.append(&2, String, xs, ys))), Bool.and(Bag.All(q, acc), Bool.and(Bag.All(q, xs), Bag.All(q, ys))), Bag.rev(q, acc, List.append(&2, String, xs, ys)), Bag.and2(Bag.All(q, acc), Bag.All(q, acc), Bag.All(q, List.append(&2, String, xs, ys)), Bool.and(Bag.All(q, xs), Bag.All(q, ys)), {==}, Bag.app(q, xs, ys)))

def Bag.merge(+q: Bag.Q, fuel: Nat, st: List<&2, String> & List<&2, String> & List<&2, String>)
  -> {Bag.All(q, List.merge.go(~String, ~B.Oil.le, fuel, st)) == Bag.tri(q, st) : Bool}:
  match fuel:
    case 0n:
      (acc, xs, ys) = st
      Bag.merge0(q, acc, xs, ys)
    case 1n+f:
      (acc, xs, ys) = st
      match xs ys:
        case Nil{} Nil{}:
          Bag.rev(q, acc, Nil{})
        case Nil{} Con{+y, +yt}:
          Bag.rev(q, acc, y <> yt)
        case Con{+x, +xt} Nil{}:
          Equal.trans(Bool, Bag.All(q, List.reverse.go(&2, String, acc, x <> xt)), Bool.and(Bag.All(q, acc), Bag.All(q, x <> xt)), Bool.and(Bag.All(q, acc), Bool.and(Bag.All(q, x <> xt), True{})), Bag.rev(q, acc, x <> xt), Bag.and2(Bag.All(q, acc), Bag.All(q, acc), Bag.All(q, x <> xt), Bool.and(Bag.All(q, x <> xt), True{}), {==}, Equal.sym(Bool, Bool.and(Bag.All(q, x <> xt), True{}), Bag.All(q, x <> xt), Bag.and_t(Bag.All(q, x <> xt)))))
        case Con{+x, +xt} Con{+y, +yt}:
          +ac = acc
          Equal.trans(Bool, Bag.All(q, List.merge.go(~String, ~B.Oil.le, f, List.merge.step(String, ac, x, xt, y, yt, B.Oil.le(x, y)))), Bag.tri(q, List.merge.step(String, ac, x, xt, y, yt, B.Oil.le(x, y))), Bool.and(Bag.All(q, ac), Bool.and(Bag.All(q, x <> xt), Bag.All(q, y <> yt))), Bag.merge(q, f, List.merge.step(String, ac, x, xt, y, yt, B.Oil.le(x, y))), Bag.step(q, ac, x, xt, y, yt, B.Oil.le(x, y)))

def Bag.AllL(+q: Bag.Q, rs: List<&2, List<&2, String>>) -> Bool:
  match rs:
    case Nil{}:
      True{}
    case Con{r, t}:
      Bool.and(Bag.All(q, r), Bag.AllL(q, t))

def Bag.pass(+q: Bag.Q, +n: Nat, rs: List<&2, List<&2, String>>) -> {Bag.AllL(q, List.sort.pass(~String, ~B.Oil.le, n, rs)) == Bag.AllL(q, rs) : Bool}:
  match rs:
    case Nil{}:
      {==}
    case Con{+r1, t}:
      match t:
        case Nil{}:
          {==}
        case Con{+r2, +rest}:
          +m = Bag.All(q, List.merge.go(~String, ~B.Oil.le, n, (Nil{}, r1, r2)))
          +p = Bag.AllL(q, List.sort.pass(~String, ~B.Oil.le, n, rest))
          +a1 = Bag.All(q, r1)
          +a2 = Bag.All(q, r2)
          +rr = Bag.AllL(q, rest)
          Equal.trans(Bool, Bool.and(m, p), Bool.and(Bool.and(a1, a2), rr), Bool.and(a1, Bool.and(a2, rr)), Bag.and2(m, Bool.and(a1, a2), p, rr, Bag.merge(q, n, (Nil{}, r1, r2)), Bag.pass(q, n, rest)), Bag.assoc(a1, a2, rr))

def Bag.cat(+q: Bag.Q, rs: List<&2, List<&2, String>>) -> {Bag.All(q, List.concat(&2, String, rs)) == Bag.AllL(q, rs) : Bool}:
  match rs:
    case Nil{}:
      {==}
    case Con{+r, +t}:
      Equal.trans(Bool, Bag.All(q, List.append(&2, String, r, List.concat(&2, String, t))), Bool.and(Bag.All(q, r), Bag.All(q, List.concat(&2, String, t))), Bool.and(Bag.All(q, r), Bag.AllL(q, t)), Bag.app(q, r, List.concat(&2, String, t)), Bag.and2(Bag.All(q, r), Bag.All(q, r), Bag.All(q, List.concat(&2, String, t)), Bag.AllL(q, t), {==}, Bag.cat(q, t)))

def Bag.go(+q: Bag.Q, fuel: Nat, +n: Nat, rs: List<&2, List<&2, String>>) -> {Bag.All(q, List.sort.go(~String, ~B.Oil.le, fuel, n, rs)) == Bag.AllL(q, rs) : Bool}:
  match fuel:
    case 0n:
      Bag.cat(q, rs)
    case 1n+f:
      match rs:
        case Nil{}:
          {==}
        case Con{+r1, t}:
          match t:
            case Nil{}:
              Equal.sym(Bool, Bool.and(Bag.All(q, r1), True{}), Bag.All(q, r1), Bag.and_t(Bag.All(q, r1)))
            case Con{+r2, +rest}:
              +rs2 = {r1 <> r2 <> rest : List<&2, List<&2, String>>}
              Equal.trans(Bool, Bag.All(q, List.sort.go(~String, ~B.Oil.le, f, n, List.sort.pass(~String, ~B.Oil.le, n, rs2))), Bag.AllL(q, List.sort.pass(~String, ~B.Oil.le, n, rs2)), Bag.AllL(q, rs2), Bag.go(q, f, n, List.sort.pass(~String, ~B.Oil.le, n, rs2)), Bag.pass(q, n, rs2))

def Bag.pair(+q: Bag.Q, +x: String, +y: String, b: Bool) -> {Bag.All(q, List.sort.pair(String, x, y, b)) == Bool.and(Bag.ok(q, x), Bool.and(Bag.ok(q, y), True{})) : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      Equal.trans(Bool, Bool.and(Bag.ok(q, y), Bool.and(Bag.ok(q, x), True{})), Bool.and(Bool.and(Bag.ok(q, x), Bag.ok(q, y)), True{}), Bool.and(Bag.ok(q, x), Bool.and(Bag.ok(q, y), True{})), Bag.rot(Bag.ok(q, y), Bag.ok(q, x), True{}), Bag.assoc(Bag.ok(q, x), Bag.ok(q, y), True{}))

def Bag.pairs(+q: Bag.Q, xs: List<&2, String>) -> {Bag.AllL(q, List.sort.pairs(~String, ~B.Oil.le, xs)) == Bag.All(q, xs) : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, t}:
      match t:
        case Nil{}:
          Bag.and_t(Bool.and(Bag.ok(q, x), True{}))
        case Con{+y, +rest}:
          +a = Bag.ok(q, x)
          +b = Bag.ok(q, y)
          +p = Bag.All(q, List.sort.pair(String, x, y, B.Oil.le(x, y)))
          +ps = Bag.AllL(q, List.sort.pairs(~String, ~B.Oil.le, rest))
          +r = Bag.All(q, rest)
          +bt = Bool.and(b, True{})
          Equal.trans(Bool, Bool.and(p, ps), Bool.and(Bool.and(a, bt), r), Bool.and(a, Bool.and(b, r)), Bag.and2(p, Bool.and(a, bt), ps, r, Bag.pair(q, x, y, B.Oil.le(x, y)), Bag.pairs(q, rest)), Equal.trans(Bool, Bool.and(Bool.and(a, bt), r), Bool.and(a, Bool.and(bt, r)), Bool.and(a, Bool.and(b, r)), Bag.assoc(a, bt, r), Bag.and2(a, a, Bool.and(bt, r), Bool.and(b, r), {==}, Bag.and2(bt, b, r, r, Bag.and_t(b), {==}))))

def Bag.sort(+q: Bag.Q, xs: List<&2, String>) -> {Bag.All(q, List.sort(~String, ~B.Oil.le, xs)) == Bag.All(q, xs) : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      +ys = {h <> t : List<&2, String>}
      +n = List.length(&2, String, ys)
      Equal.trans(Bool, Bag.All(q, List.sort.go(~String, ~B.Oil.le, n, n, List.sort.pairs(~String, ~B.Oil.le, ys))), Bag.AllL(q, List.sort.pairs(~String, ~B.Oil.le, ys)), Bag.All(q, ys), Bag.go(q, n, n, List.sort.pairs(~String, ~B.Oil.le, ys)), Bag.pairs(q, ys))

# Oil.add, Oil.uniq and Oil.collect
# ---------------------------------

def Bag.add.hit(+q: Bag.Q, +e: String, +h: String, +t: List<&2, String>, b: Bool, eb: {String.eq(h, e) == b : Bool})
  -> {Bag.All(q, X.Bool.when(List<&2, String>, b, u => e <> h <> t, u => h <> t)) == Bool.and(Bag.ok(q, e), Bool.and(Bag.ok(q, h), Bag.All(q, t))) : Bool}:
  match b:
    case False{}:
      {==}
    case True{}:
      %Str.Str.eq_true(h, e, eb) : {Bool.and(Bag.ok(q, h), Bag.All(q, t)) == Bool.and(Bag.ok(q, _), Bool.and(Bag.ok(q, h), Bag.All(q, t))) : Bool}
      Equal.sym(Bool, Bool.and(Bag.ok(q, h), Bool.and(Bag.ok(q, h), Bag.All(q, t))), Bool.and(Bag.ok(q, h), Bag.All(q, t)), Bag.idem(Bag.ok(q, h), Bag.All(q, t)))

def Bag.add(+q: Bag.Q, +e: String, out: List<&2, String>) -> {Bag.All(q, B.Oil.add(e, out)) == Bool.and(Bag.ok(QOpt{q}, e), Bag.All(q, out)) : Bool}:
  match e out:
    case SNil{} Nil{}:
      {==}
    case SNil{} Con{h, t}:
      {==}
    case SCon{c, s} Nil{}:
      {==}
    case SCon{+c, +s} Con{+h, +t}:
      Bag.add.hit(q, SCon{c, s}, h, t, String.eq(h, SCon{c, s}), {==})

def Bag.uniq(+q: Bag.Q, xs: List<&2, String>, +out: List<&2, String>) -> {Bag.All(q, B.Oil.uniq(xs, out)) == Bool.and(Bag.All(QOpt{q}, xs), Bag.All(q, out)) : Bool}:
  match xs:
    case Nil{}:
      Equal.trans(Bool, Bag.All(q, List.reverse.go(&2, String, out, Nil{})), Bool.and(Bag.All(q, out), True{}), Bag.All(q, out), Bag.rev(q, out, Nil{}), Bag.and_t(Bag.All(q, out)))
    case Con{+x, +t}:
      +ox = Bag.ok(QOpt{q}, x)
      +at = Bag.All(QOpt{q}, t)
      +ao = Bag.All(q, out)
      Equal.trans(Bool, Bag.All(q, B.Oil.uniq(t, B.Oil.add(x, out))), Bool.and(at, Bool.and(ox, ao)), Bool.and(Bool.and(ox, at), ao), Equal.trans(Bool, Bag.All(q, B.Oil.uniq(t, B.Oil.add(x, out))), Bool.and(at, Bag.All(q, B.Oil.add(x, out))), Bool.and(at, Bool.and(ox, ao)), Bag.uniq(q, t, B.Oil.add(x, out)), Bag.and2(at, at, Bag.All(q, B.Oil.add(x, out)), Bool.and(ox, ao), {==}, Bag.add(q, x, out))), Bag.rot(at, ox, ao))

# what the entries kept from fs must satisfy
def Bag.Kept(+q: Bag.Q, fs: List<&2, T.Buf>, +d: String, +flag: Bool) -> Bool:
  match fs:
    case Nil{}:
      True{}
    case Con{T.Buf{p, ls}, t}:
      +e = B.Path.child(d, p)
      Bool.and(Bool.pick(Bool, Bool.not(Bool.xor(B.Path.is_dir(e), flag)), Bag.ok(QOpt{q}, e), True{}), Bag.Kept(q, t, d, flag))

def Bag.pick(+q: Bag.Q, +e: String, +out: List<&2, String>, keep: Bool)
  -> {Bag.All(q, Bool.pick(List<&2, String>, keep, B.Oil.add(e, out), out)) == Bool.and(Bool.pick(Bool, keep, Bag.ok(QOpt{q}, e), True{}), Bag.All(q, out)) : Bool}:
  match keep:
    case False{}:
      {==}
    case True{}:
      Bag.add(q, e, out)

def Bag.coll(+q: Bag.Q, fs: List<&2, T.Buf>, +d: String, +flag: Bool, +out: List<&2, String>)
  -> {Bag.All(q, B.Oil.collect(fs, d, flag, out)) == Bool.and(Bag.Kept(q, fs, d, flag), Bag.All(q, out)) : Bool}:
  match fs:
    case Nil{}:
      {==}
    case Con{b, +t}:
      match b:
        case T.Buf{+p, ls}:
          +e = B.Path.child(d, p)
          +keep = Bool.not(Bool.xor(B.Path.is_dir(e), flag))
          +o2 = Bool.pick(List<&2, String>, keep, B.Oil.add(e, out), out)
          +k = Bool.pick(Bool, keep, Bag.ok(QOpt{q}, e), True{})
          +kt = Bag.Kept(q, t, d, flag)
          +ao = Bag.All(q, out)
          Equal.trans(Bool, Bag.All(q, B.Oil.collect(t, d, flag, o2)), Bool.and(kt, Bool.and(k, ao)), Bool.and(Bool.and(k, kt), ao), Equal.trans(Bool, Bag.All(q, B.Oil.collect(t, d, flag, o2)), Bool.and(kt, Bag.All(q, o2)), Bool.and(kt, Bool.and(k, ao)), Bag.coll(q, t, d, flag, o2), Bag.and2(kt, kt, Bag.All(q, o2), Bool.and(k, ao), {==}, Bag.pick(q, e, out, keep))), Bag.rot(kt, k, ao))

# every entry of folder d over fs satisfies r
def Bag.AllF(+r: Bag.Q, fs: List<&2, T.Buf>, +d: String) -> Bool:
  match fs:
    case Nil{}:
      True{}
    case Con{T.Buf{p, ls}, t}:
      Bool.and(Bag.ok(r, B.Path.child(d, p)), Bag.AllF(r, t, d))

def Bag.flags(b: Bool, v: Bool) -> {Bool.and(Bool.pick(Bool, Bool.not(Bool.xor(b, True{})), v, True{}), Bool.pick(Bool, Bool.not(Bool.xor(b, False{})), v, True{})) == v : Bool}:
  match b:
    case False{}:
      {==}
    case True{}:
      Bag.and_t(v)

def Bag.both(+q: Bag.Q, fs: List<&2, T.Buf>, +d: String) -> {Bool.and(Bag.Kept(q, fs, d, True{}), Bag.Kept(q, fs, d, False{})) == Bag.AllF(QOpt{q}, fs, d) : Bool}:
  match fs:
    case Nil{}:
      {==}
    case Con{b, +t}:
      match b:
        case T.Buf{+p, ls}:
          +e = B.Path.child(d, p)
          +v = Bag.ok(QOpt{q}, e)
          +kT = Bool.pick(Bool, Bool.not(Bool.xor(B.Path.is_dir(e), True{})), v, True{})
          +kF = Bool.pick(Bool, Bool.not(Bool.xor(B.Path.is_dir(e), False{})), v, True{})
          +tT = Bag.Kept(q, t, d, True{})
          +tF = Bag.Kept(q, t, d, False{})
          Equal.trans(Bool, Bool.and(Bool.and(kT, tT), Bool.and(kF, tF)), Bool.and(Bool.and(kT, kF), Bool.and(tT, tF)), Bool.and(v, Bag.AllF(QOpt{q}, t, d)), Bag.swap4(kT, tT, kF, tF), Bag.and2(Bool.and(kT, kF), v, Bool.and(tT, tF), Bag.AllF(QOpt{q}, t, d), Bag.flags(B.Path.is_dir(e), v), Bag.both(q, t, d)))

def Bag.half(+q: Bag.Q, +fs: List<&2, T.Buf>, +d: String, +flag: Bool)
  -> {Bag.All(q, B.Oil.uniq(List.sort(~String, ~B.Oil.le, B.Oil.collect(fs, d, flag, Nil{})), Nil{})) == Bag.Kept(QOpt{q}, fs, d, flag) : Bool}:
  +c = B.Oil.collect(fs, d, flag, Nil{})
  +s = List.sort(~String, ~B.Oil.le, c)
  +k = Bag.Kept(QOpt{q}, fs, d, flag)
  +e1 = Equal.trans(Bool, Bag.All(q, B.Oil.uniq(s, Nil{})), Bool.and(Bag.All(QOpt{q}, s), True{}), Bag.All(QOpt{q}, s), Bag.uniq(q, s, Nil{}), Bag.and_t(Bag.All(QOpt{q}, s)))
  +e2 = Equal.trans(Bool, Bag.All(q, B.Oil.uniq(s, Nil{})), Bag.All(QOpt{q}, s), Bag.All(QOpt{q}, c), e1, Bag.sort(QOpt{q}, c))
  +e3 = Equal.trans(Bool, Bag.All(QOpt{q}, c), Bool.and(k, True{}), k, Bag.coll(QOpt{q}, fs, d, flag, Nil{}), Bag.and_t(k))
  Equal.trans(Bool, Bag.All(q, B.Oil.uniq(s, Nil{})), Bag.All(QOpt{q}, c), k, e2, e3)

# what holds of every entry of a listing past "../"
def Bag.listing(+q: Bag.Q, +fs: List<&2, T.Buf>, +d: String) -> {Bag.All(q, Laws.Spec.tail(B.Oil.list(fs, d))) == Bag.AllF(QOpt{QOpt{q}}, fs, d) : Bool}:
  +uT = B.Oil.uniq(List.sort(~String, ~B.Oil.le, B.Oil.collect(fs, d, True{}, Nil{})), Nil{})
  +uF = B.Oil.uniq(List.sort(~String, ~B.Oil.le, B.Oil.collect(fs, d, False{}, Nil{})), Nil{})
  +kT = Bag.Kept(QOpt{q}, fs, d, True{})
  +kF = Bag.Kept(QOpt{q}, fs, d, False{})
  +e1 = Equal.trans(Bool, Bag.All(q, List.append(&2, String, uT, uF)), Bool.and(Bag.All(q, uT), Bag.All(q, uF)), Bool.and(kT, kF), Bag.app(q, uT, uF), Bag.and2(Bag.All(q, uT), kT, Bag.All(q, uF), kF, Bag.half(q, fs, d, True{}), Bag.half(q, fs, d, False{})))
  Equal.trans(Bool, Bag.All(q, List.append(&2, String, uT, uF)), Bool.and(kT, kF), Bag.AllF(QOpt{QOpt{q}}, fs, d), e1, Bag.both(QOpt{q}, fs, d))

# B.Path.child is the spec's child
# --------------------------------

def Bag.sapp_nil(a: String) -> {String.append(a, SNil{}) == a : String}:
  match a:
    case SNil{}:
      {==}
    case SCon{+h, +t}:
      %Bag.sapp_nil(t) : {SCon{h, String.append(t, SNil{})} == SCon{h, _} : String}
      {==}

def Bag.sapp_assoc(a: String, +b: String, +c: String) -> {String.append(String.append(a, b), c) == String.append(a, String.append(b, c)) : String}:
  match a:
    case SNil{}:
      {==}
    case SCon{+h, +t}:
      %Bag.sapp_assoc(t, b, c) : {SCon{h, String.append(String.append(t, b), c)} == SCon{h, _} : String}
      {==}

# the first n characters of s
def Bag.first(n: Nat, s: String) -> String:
  match n:
    case 0n:
      SNil{}
    case 1n+p:
      match s:
        case SNil{}:
          SNil{}
        case SCon{h, t}:
          SCon{h, Bag.first(p, t)}

def Bag.take_go(s: String, n: Nat, +acc: String) -> {X.Text.take.go(s, n, acc) == X.Text.rest(String.append(acc, Bag.first(n, s))) : String}:
  match s n:
    case SNil{} 0n:
      Equal.cong(String, String, z => X.Text.rest(z), acc, String.append(acc, SNil{}), Equal.sym(String, String.append(acc, SNil{}), acc, Bag.sapp_nil(acc)))
    case SNil{} 1n+p:
      Equal.cong(String, String, z => X.Text.rest(z), acc, String.append(acc, SNil{}), Equal.sym(String, String.append(acc, SNil{}), acc, Bag.sapp_nil(acc)))
    case SCon{h, t} 0n:
      Equal.cong(String, String, z => X.Text.rest(z), acc, String.append(acc, SNil{}), Equal.sym(String, String.append(acc, SNil{}), acc, Bag.sapp_nil(acc)))
    case SCon{+h, +t} 1n++p:
      +a2 = String.append(acc, SCon{h, SNil{}})
      Equal.trans(String, X.Text.take.go(t, p, a2), X.Text.rest(String.append(a2, Bag.first(p, t))), X.Text.rest(String.append(acc, SCon{h, Bag.first(p, t)})), Bag.take_go(t, p, a2), Equal.cong(String, String, z => X.Text.rest(z), String.append(a2, Bag.first(p, t)), String.append(acc, SCon{h, Bag.first(p, t)}), Bag.sapp_assoc(acc, SCon{h, SNil{}}, Bag.first(p, t))))

def Bag.take(+s: String, +n: Nat) -> {X.Text.take(s, n) == Bag.first(n, s) : String}:
  Bag.take_go(s, n, " ")

def Bag.shift(m: Maybe<&2, Nat>) -> Maybe<&2, Nat>:
  match m:
    case None{}:
      None{}
    case Some{k}:
      Some{1n+k}

def Bag.slash.hit(b: Bool, -t: String, -n: Nat, -i: Nat, ih: {B.Path.slash.go(t, n, 1n+1n+i) == Bag.shift(B.Path.slash.go(t, n, 1n+i)) : Maybe<&2, Nat>})
  -> {X.Bool.when(Maybe<&2, Nat>, b, u => B.Path.slash.go(t, n, 1n+1n+i), u => Some{1n+i}) == Bag.shift(X.Bool.when(Maybe<&2, Nat>, b, u => B.Path.slash.go(t, n, 1n+i), u => Some{i})) : Maybe<&2, Nat>}:
  match b:
    case False{}:
      ih
    case True{}:
      {==}

def Bag.slash(s: String, n: Nat, +i: Nat) -> {B.Path.slash.go(s, n, 1n+i) == Bag.shift(B.Path.slash.go(s, n, i)) : Maybe<&2, Nat>}:
  match s:
    case SNil{}:
      {==}
    case SCon{h, +t}:
      Bag.slash.hit(Char.is_eq(h, '/'), t, n, i, Bag.slash(t, n, 1n+i))

def Bag.name_sh(+h: Char, +t: String, m: Maybe<&2, Nat>) -> {B.Path.name.at(SCon{h, t}, Bag.shift(m)) == SCon{h, B.Path.name.at(t, m)} : String}:
  match m:
    case None{}:
      {==}
    case Some{+k}:
      Equal.trans(String, X.Text.take(SCon{h, t}, 1n+1n+k), Bag.first(1n+1n+k, SCon{h, t}), SCon{h, X.Text.take(t, 1n+k)}, Bag.take(SCon{h, t}, 1n+1n+k), Equal.cong(String, String, z => SCon{h, z}, Bag.first(1n+k, t), X.Text.take(t, 1n+k), Equal.sym(String, X.Text.take(t, 1n+k), Bag.first(1n+k, t), Bag.take(t, 1n+k))))

def Bag.pick_cons(b: Bool, -h: Char, -x: String, -y: String) -> {SCon{h, Bool.pick(String, b, x, y)} == Bool.pick(String, b, SCon{h, x}, SCon{h, y}) : String}:
  match b:
    case False{}:
      {==}
    case True{}:
      {==}

def Bag.name.hit(b: Bool, +h: Char, +t: String, ih: {B.Path.name(t) == Bool.pick(String, Laws.Spec.has_slash(t), Laws.Spec.upto_slash(t), t) : String})
  -> {B.Path.name.at(SCon{h, t}, X.Bool.when(Maybe<&2, Nat>, b, u => B.Path.slash.go(t, 0n, 1n), u => Some{0n})) == Bool.pick(String, Bool.or(b, Laws.Spec.has_slash(t)), Bool.pick(String, b, SCon{h, SNil{}}, SCon{h, Laws.Spec.upto_slash(t)}), SCon{h, t}) : String}:
  match b:
    case True{}:
      Bag.take(SCon{h, t}, 1n)
    case False{}:
      +m = B.Path.slash.go(t, 0n, 0n)
      +e1 = Equal.cong(Maybe<&2, Nat>, String, z => B.Path.name.at(SCon{h, t}, z), B.Path.slash.go(t, 0n, 1n), Bag.shift(m), Bag.slash(t, 0n, 0n))
      +e2 = Equal.trans(String, B.Path.name.at(SCon{h, t}, B.Path.slash.go(t, 0n, 1n)), B.Path.name.at(SCon{h, t}, Bag.shift(m)), SCon{h, B.Path.name.at(t, m)}, e1, Bag.name_sh(h, t, m))
      +e3 = Equal.cong(String, String, z => SCon{h, z}, B.Path.name(t), Bool.pick(String, Laws.Spec.has_slash(t), Laws.Spec.upto_slash(t), t), ih)
      +e4 = Equal.trans(String, B.Path.name.at(SCon{h, t}, B.Path.slash.go(t, 0n, 1n)), SCon{h, B.Path.name(t)}, SCon{h, Bool.pick(String, Laws.Spec.has_slash(t), Laws.Spec.upto_slash(t), t)}, e2, e3)
      Equal.trans(String, B.Path.name.at(SCon{h, t}, B.Path.slash.go(t, 0n, 1n)), SCon{h, Bool.pick(String, Laws.Spec.has_slash(t), Laws.Spec.upto_slash(t), t)}, Bool.pick(String, Laws.Spec.has_slash(t), SCon{h, Laws.Spec.upto_slash(t)}, SCon{h, t}), e4, Bag.pick_cons(Laws.Spec.has_slash(t), h, Laws.Spec.upto_slash(t), t))

def Bag.name(+r: String) -> {B.Path.name(r) == Bool.pick(String, Laws.Spec.has_slash(r), Laws.Spec.upto_slash(r), r) : String}:
  match r:
    case SNil{}:
      {==}
    case SCon{+h, +t}:
      Bag.name.hit(Char.is_eq(h, '/'), h, t, Bag.name(t))

def Bag.drop(d: String, p: String) -> {X.Text.drop(p, Laws.Spec.chars(d)) == Laws.Spec.drop_prefix(d, p) : String}:
  match d p:
    case SNil{} SNil{}:
      {==}
    case SNil{} SCon{b, st}:
      {==}
    case SCon{a, pt} SNil{}:
      {==}
    case SCon{a, pt} SCon{b, st}:
      Bag.drop(pt, st)

def Bag.dself(d: String) -> {Laws.Spec.drop_prefix(d, d) == SNil{} : String}:
  match d:
    case SNil{}:
      {==}
    case SCon{a, t}:
      Bag.dself(t)

# what B.Path.name reads past folder d
def Bag.rest(+d: String, +p: String) -> {X.Text.drop(p, X.Text.len(d)) == Laws.Spec.drop_prefix(d, p) : String}:
  Equal.trans(String, X.Text.drop(p, X.Text.len(d)), X.Text.drop(p, Laws.Spec.chars(d)), Laws.Spec.drop_prefix(d, p), Equal.cong(Nat, String, z => X.Text.drop(p, z), X.Text.len(d), Laws.Spec.chars(d), Tx.Chars.eq(d)), Bag.drop(d, p))

def Bag.child.at(b: Bool, +d: String, +p: String, h: {b == True{} : Bool})
  -> {X.Bool.when(String, b, u => "", u => B.Path.name(X.Text.drop(p, X.Text.len(d)))) == Laws.Spec.child(d, p) : String}:
  match b:
    case False{}:
      L.Bool.false_true({"" == Laws.Spec.child(d, p) : String}, h)
    case True{}:
      +r = Laws.Spec.drop_prefix(d, p)
      Equal.trans(String, B.Path.name(X.Text.drop(p, X.Text.len(d))), B.Path.name(r), Bool.pick(String, Laws.Spec.has_slash(r), Laws.Spec.upto_slash(r), r), Equal.cong(String, String, z => B.Path.name(z), X.Text.drop(p, X.Text.len(d)), r, Bag.rest(d, p)), Bag.name(r))

# inside folder d, B.Path.child is the spec's child
def Bag.spec_child(+d: String, +p: String, h: {X.Text.prefix(d, p) == True{} : Bool}) -> {B.Path.child(d, p) == Laws.Spec.child(d, p) : String}:
  Bag.child.at(X.Text.prefix(d, p), d, p, h)

def Bag.pre.at(b: Bool, -d: String, -p: String, h: {String.is_empty(X.Bool.when(String, b, u => "", u => B.Path.name(X.Text.drop(p, X.Text.len(d))))) == False{} : Bool}) -> {b == True{} : Bool}:
  match b:
    case False{}:
      L.Bool.true_false({False{} == True{} : Bool}, h)
    case True{}:
      {==}

# a nonempty child lies inside the folder
def Bag.ne_pre(+d: String, +p: String, h: {String.is_empty(B.Path.child(d, p)) == False{} : Bool}) -> {X.Text.prefix(d, p) == True{} : Bool}:
  Bag.pre.at(X.Text.prefix(d, p), d, p, h)

def Bag.self.at(b: Bool, +d: String) -> {String.is_empty(X.Bool.when(String, b, u => "", u => B.Path.name(X.Text.drop(d, X.Text.len(d))))) == True{} : Bool}:
  match b:
    case False{}:
      {==}
    case True{}:
      Equal.cong(String, Bool, z => String.is_empty(B.Path.name(z)), X.Text.drop(d, X.Text.len(d)), SNil{}, Equal.trans(String, X.Text.drop(d, X.Text.len(d)), Laws.Spec.drop_prefix(d, d), SNil{}, Bag.rest(d, d), Bag.dself(d)))

# a folder is no child of itself
def Bag.self(+d: String) -> {String.is_empty(B.Path.child(d, d)) == True{} : Bool}:
  Bag.self.at(X.Text.prefix(d, d), d)

def Bag.ne_eq.at(b: Bool, +d: String, +p: String, eb: {String.eq(d, p) == b : Bool}, h: {String.is_empty(B.Path.child(d, p)) == False{} : Bool}) -> {b == False{} : Bool}:
  match b:
    case False{}:
      {==}
    case True{}:
      +c = Equal.cong(String, Bool, z => String.is_empty(B.Path.child(d, z)), d, p, Str.Str.eq_true(d, p, eb))
      Equal.trans(Bool, True{}, String.is_empty(B.Path.child(d, p)), False{}, Equal.trans(Bool, True{}, String.is_empty(B.Path.child(d, d)), String.is_empty(B.Path.child(d, p)), Equal.sym(Bool, String.is_empty(B.Path.child(d, d)), True{}, Bag.self(d)), c), h)

# a nonempty child is not the folder itself
def Bag.ne_eq(+d: String, +p: String, h: {String.is_empty(B.Path.child(d, p)) == False{} : Bool}) -> {String.eq(d, p) == False{} : Bool}:
  Bag.ne_eq.at(String.eq(d, p), d, p, {==}, h)

# the root's path has no child
def Bag.root(d: String) -> {String.is_empty(B.Path.child(d, "")) == True{} : Bool}:
  match d:
    case SNil{}:
      {==}
    case SCon{a, t}:
      {==}

def Bag.dp_empty(d: String, p: String, +hp: {Laws.Spec.prefix(d, p) == True{} : Bool}, he: {String.is_empty(Laws.Spec.drop_prefix(d, p)) == True{} : Bool}) -> {String.eq(d, p) == True{} : Bool}:
  match d p:
    case SNil{} SNil{}:
      {==}
    case SNil{} SCon{b, st}:
      L.Bool.false_true({String.eq(SNil{}, SCon{b, st}) == True{} : Bool}, he)
    case SCon{a, pt} SNil{}:
      L.Bool.false_true({String.eq(SCon{a, pt}, SNil{}) == True{} : Bool}, hp)
    case SCon{+a, +pt} SCon{+b, +st}:
      +ea = Str.Char.eq_true(a, b, L.And.l(Char.is_eq(a, b), Laws.Spec.prefix(pt, st), hp))
      +es = Str.Str.eq_true(pt, st, Bag.dp_empty(pt, st, L.And.r(Char.is_eq(a, b), Laws.Spec.prefix(pt, st), hp), he))
      %ea : {String.eq(SCon{a, pt}, SCon{_, st}) == True{} : Bool}
      %es : {String.eq(SCon{a, pt}, SCon{a, _}) == True{} : Bool}
      Tx.String.eq_refl(SCon{a, pt})

def Bag.pick_ne2(b1: Bool, b2: Bool, -c: Char, -t: String)
  -> {String.is_empty(Bool.pick(String, Bool.or(b1, b2), Bool.pick(String, b1, SCon{c, SNil{}}, SCon{c, Laws.Spec.upto_slash(t)}), SCon{c, t})) == False{} : Bool}:
  match b1 b2:
    case False{} False{}:
      {==}
    case False{} True{}:
      {==}
    case True{} _:
      {==}

def Bag.pick_ne(r: String, h: {String.is_empty(r) == False{} : Bool})
  -> {String.is_empty(Bool.pick(String, Laws.Spec.has_slash(r), Laws.Spec.upto_slash(r), r)) == False{} : Bool}:
  match r:
    case SNil{}:
      h
    case SCon{+c, +t}:
      Bag.pick_ne2(Char.is_eq(c, '/'), Laws.Spec.has_slash(t), c, t)

def Bag.here.at(b: Bool, +d: String, +p: String, hp: {Laws.Spec.prefix(d, p) == True{} : Bool}, hn: {String.eq(d, p) == False{} : Bool}, eb: {String.is_empty(Laws.Spec.drop_prefix(d, p)) == b : Bool})
  -> {String.is_empty(Laws.Spec.child(d, p)) == False{} : Bool}:
  match b:
    case True{}:
      L.Bool.false_true({String.is_empty(Laws.Spec.child(d, p)) == False{} : Bool}, Equal.trans(Bool, False{}, String.eq(d, p), True{}, Equal.sym(Bool, String.eq(d, p), False{}, hn), Bag.dp_empty(d, p, hp, eb)))
    case False{}:
      Bag.pick_ne(Laws.Spec.drop_prefix(d, p), eb)

# a path strictly inside folder d has a nonempty child
def Bag.here(+d: String, +p: String, hp: {Laws.Spec.prefix(d, p) == True{} : Bool}, hn: {String.eq(d, p) == False{} : Bool}) -> {String.is_empty(Laws.Spec.child(d, p)) == False{} : Bool}:
  Bag.here.at(String.is_empty(Laws.Spec.drop_prefix(d, p)), d, p, hp, hn, {==})

# Listings against the spec
# -------------------------

def Bag.norm(+r: Bag.Q, fs: List<&2, T.Buf>, +d: String) -> {Bag.AllF(r, Sb.Files.norm(fs), d) == Bag.AllF(r, fs, d) : Bool}:
  match fs:
    case Nil{}:
      {==}
    case Con{b, +t}:
      match b:
        case T.Buf{+p, ls}:
          Bag.and2(Bag.ok(r, B.Path.child(d, p)), Bag.ok(r, B.Path.child(d, p)), Bag.AllF(r, Sb.Files.norm(t), d), Bag.AllF(r, t, d), {==}, Bag.norm(r, t, d))

def Bag.only_all(+d: String, ls: List<&2, String>, +fs: List<&2, T.Buf>) -> {Laws.Spec.only(d, ls, fs) == Bag.All(QChild{d, fs}, ls) : Bool}:
  match ls:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      Bag.and2(Laws.Spec.is_child(d, h, fs), Laws.Spec.is_child(d, h, fs), Laws.Spec.only(d, t, fs), Bag.All(QChild{d, fs}, t), {==}, Bag.only_all(d, t, fs))

def Bag.has_all(+x: String, ls: List<&2, String>) -> {Laws.Spec.has_line(x, ls) == Bool.not(Bag.All(QNe{x}, ls)) : Bool}:
  match ls:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      Equal.trans(Bool, Bool.or(String.eq(h, x), Laws.Spec.has_line(x, t)), Bool.or(String.eq(h, x), Bool.not(Bag.All(QNe{x}, t))), Bool.not(Bool.and(Bool.not(String.eq(h, x)), Bag.All(QNe{x}, t))), Equal.cong(Bool, Bool, z => Bool.or(String.eq(h, x), z), Laws.Spec.has_line(x, t), Bool.not(Bag.All(QNe{x}, t)), Bag.has_all(x, t)), Bag.or_not(String.eq(h, x), Bag.All(QNe{x}, t)))

def Bag.fapp(pre: List<&2, T.Buf>, +b: T.Buf, +t: List<&2, T.Buf>) -> {List.append(&2, T.Buf, List.append(&2, T.Buf, pre, [b]), t) == List.append(&2, T.Buf, pre, b <> t) : List<&2, T.Buf>}:
  match pre:
    case Nil{}:
      {==}
    case Con{+h, +u}:
      Equal.cong(List<&2, T.Buf>, List<&2, T.Buf>, z => h <> z, List.append(&2, T.Buf, List.append(&2, T.Buf, u, [b]), t), List.append(&2, T.Buf, u, b <> t), Bag.fapp(u, b, t))

# (B): every entry is some file's child
# -------------------------------------

def Bag.ischild_app(+d: String, +x: String, pre: List<&2, T.Buf>, +rest: List<&2, T.Buf>, h: {Laws.Spec.is_child(d, x, rest) == True{} : Bool})
  -> {Laws.Spec.is_child(d, x, List.append(&2, T.Buf, pre, rest)) == True{} : Bool}:
  match pre:
    case Nil{}:
      h
    case Con{b, +u}:
      match b:
        case T.Buf{+p, ls}:
          L.Or.r(Bool.and(Bool.and(Laws.Spec.prefix(d, p), Bool.not(String.eq(d, p))), String.eq(Laws.Spec.child(d, p), x)), Laws.Spec.is_child(d, x, List.append(&2, T.Buf, u, rest)), Bag.ischild_app(d, x, u, rest, h))

def Bag.headchild(+d: String, +p: String, -ls: List<&2, String>, -t: List<&2, T.Buf>, +h: {String.is_empty(B.Path.child(d, p)) == False{} : Bool})
  -> {Laws.Spec.is_child(d, B.Path.child(d, p), Con{T.Buf{p, ls}, t}) == True{} : Bool}:
  +e = B.Path.child(d, p)
  +hx = Bag.ne_pre(d, p, h)
  +hp = Equal.trans(Bool, Laws.Spec.prefix(d, p), X.Text.prefix(d, p), True{}, Equal.sym(Bool, X.Text.prefix(d, p), Laws.Spec.prefix(d, p), Rb.Prefix.eq(d, p)), hx)
  +hn = L.Not.of(String.eq(d, p), Bag.ne_eq(d, p, h))
  +hq = Tx.String.eq_same(Laws.Spec.child(d, p), e, Equal.sym(String, e, Laws.Spec.child(d, p), Bag.spec_child(d, p, hx)))
  +here = Bool.and(Laws.Spec.prefix(d, p), Bool.not(String.eq(d, p)))
  L.Or.l(Bool.and(here, String.eq(Laws.Spec.child(d, p), e)), Laws.Spec.is_child(d, e, t), L.And.intro(here, String.eq(Laws.Spec.child(d, p), e), L.And.intro(Laws.Spec.prefix(d, p), Bool.not(String.eq(d, p)), hp, hn), hq))

def Bag.oo(b: Bool, +d: String, +p: String, +ls: List<&2, String>, +t: List<&2, T.Buf>, +pre: List<&2, T.Buf>, eb: {String.is_empty(B.Path.child(d, p)) == b : Bool})
  -> {Bool.or(b, Bool.or(b, Laws.Spec.is_child(d, B.Path.child(d, p), List.append(&2, T.Buf, pre, Con{T.Buf{p, ls}, t})))) == True{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      Bag.ischild_app(d, B.Path.child(d, p), pre, Con{T.Buf{p, ls}, t}, Bag.headchild(d, p, ls, t, eb))

def Bag.gen(+d: String, fs: List<&2, T.Buf>, +pre: List<&2, T.Buf>) -> {Bag.AllF(QOpt{QOpt{QChild{d, List.append(&2, T.Buf, pre, fs)}}}, fs, d) == True{} : Bool}:
  match fs:
    case Nil{}:
      {==}
    case Con{b, +t}:
      match b:
        case T.Buf{+p, +ls}:
          +bf = {T.Buf{p, ls} : T.Buf}
          +c = Equal.cong(List<&2, T.Buf>, Bool, z => Bag.AllF(QOpt{QOpt{QChild{d, z}}}, t, d), List.append(&2, T.Buf, List.append(&2, T.Buf, pre, [bf]), t), List.append(&2, T.Buf, pre, bf <> t), Bag.fapp(pre, bf, t))
          +g = List.append(&2, T.Buf, pre, bf <> t)
          +tl = Equal.trans(Bool, Bag.AllF(QOpt{QOpt{QChild{d, g}}}, t, d), Bag.AllF(QOpt{QOpt{QChild{d, List.append(&2, T.Buf, List.append(&2, T.Buf, pre, [bf]), t)}}}, t, d), True{}, Equal.sym(Bool, Bag.AllF(QOpt{QOpt{QChild{d, List.append(&2, T.Buf, List.append(&2, T.Buf, pre, [bf]), t)}}}, t, d), Bag.AllF(QOpt{QOpt{QChild{d, g}}}, t, d), c), Bag.gen(d, t, List.append(&2, T.Buf, pre, [bf])))
          L.And.intro(Bag.ok(QOpt{QOpt{QChild{d, g}}}, B.Path.child(d, p)), Bag.AllF(QOpt{QOpt{QChild{d, g}}}, t, d), Bag.oo(String.is_empty(B.Path.child(d, p)), d, p, ls, t, pre, {==}), tl)

def Bag.only(+d: String, +fs: List<&2, T.Buf>) -> {Laws.Spec.only(d, Laws.Spec.tail(B.Oil.list(Sb.Files.norm(fs), d)), fs) == True{} : Bool}:
  +ls = Laws.Spec.tail(B.Oil.list(Sb.Files.norm(fs), d))
  +q = {QChild{d, fs} : Bag.Q}
  +e1 = Equal.trans(Bool, Laws.Spec.only(d, ls, fs), Bag.All(q, ls), Bag.AllF(QOpt{QOpt{q}}, Sb.Files.norm(fs), d), Bag.only_all(d, ls, fs), Bag.listing(q, Sb.Files.norm(fs), d))
  +e2 = Equal.trans(Bool, Laws.Spec.only(d, ls, fs), Bag.AllF(QOpt{QOpt{q}}, Sb.Files.norm(fs), d), Bag.AllF(QOpt{QOpt{q}}, fs, d), e1, Bag.norm(QOpt{QOpt{q}}, fs, d))
  Equal.trans(Bool, Laws.Spec.only(d, ls, fs), Bag.AllF(QOpt{QOpt{q}}, fs, d), True{}, e2, Bag.gen(d, fs, Nil{}))

# (C): every file's child is listed
# ---------------------------------

def Bag.hit_head(e: Bool, q: Bool, -r: Bool, he: {e == False{} : Bool}, hq: {q == True{} : Bool}) -> {Bool.and(Bool.or(e, Bool.or(e, Bool.not(q))), r) == False{} : Bool}:
  match e q:
    case True{} _:
      L.Bool.true_false({Bool.and(Bool.or(True{}, Bool.or(True{}, Bool.not(q))), r) == False{} : Bool}, he)
    case False{} False{}:
      L.Bool.false_true({Bool.and(Bool.or(False{}, Bool.or(False{}, Bool.not(False{}))), r) == False{} : Bool}, hq)
    case False{} True{}:
      {==}

def Bag.hit(+x: String, +d: String, fs: List<&2, T.Buf>, i: Nat, hx: {String.is_empty(B.Path.child(d, B.Buf.path(B.Files.at(fs, i)))) == False{} : Bool}, he: {B.Path.child(d, B.Buf.path(B.Files.at(fs, i))) == x : String})
  -> {Bag.AllF(QOpt{QOpt{QNe{x}}}, fs, d) == False{} : Bool}:
  match fs i:
    case Nil{} _:
      L.Bool.both({Bag.AllF(QOpt{QOpt{QNe{x}}}, Nil{}, d) == False{} : Bool}, String.is_empty(B.Path.child(d, "")), Bag.root(d), hx)
    case Con{T.Buf{+p, ls}, t} 0n:
      +e = B.Path.child(d, p)
      Bag.hit_head(String.is_empty(e), String.eq(e, x), Bag.AllF(QOpt{QOpt{QNe{x}}}, t, d), hx, Tx.String.eq_same(e, x, he))
    case Con{T.Buf{+p, ls}, +t} 1n+j:
      Bag.and_f(Bag.ok(QOpt{QOpt{QNe{x}}}, B.Path.child(d, p)), Bag.AllF(QOpt{QOpt{QNe{x}}}, t, d), Bag.hit(x, d, t, j, hx, he))

# x is a line past "../" when some file of fs has child x
def Bag.listed(+x: String, +fs: List<&2, T.Buf>, +d: String, hf: {Bag.AllF(QOpt{QOpt{QNe{x}}}, fs, d) == False{} : Bool})
  -> {Laws.Spec.has_line(x, B.Oil.list(fs, d)) == True{} : Bool}:
  +ls = Laws.Spec.tail(B.Oil.list(fs, d))
  +e1 = Equal.trans(Bool, Bag.All(QNe{x}, ls), Bag.AllF(QOpt{QOpt{QNe{x}}}, fs, d), False{}, Bag.listing(QNe{x}, fs, d), hf)
  +e2 = Equal.trans(Bool, Laws.Spec.has_line(x, ls), Bool.not(Bag.All(QNe{x}, ls)), True{}, Bag.has_all(x, ls), Equal.cong(Bool, Bool, z => Bool.not(z), Bag.All(QNe{x}, ls), False{}, e1))
  L.Or.r(String.eq("../", x), Laws.Spec.has_line(x, ls), e2)

def Bag.mem(+d: String, +files: List<&2, T.Buf>, +i: Nat, hi: {Nat.is_lt(i, B.Files.len(files)) == True{} : Bool}, hx: {String.is_empty(B.Path.child(d, B.Buf.path(B.Files.at(files, i)))) == False{} : Bool})
  -> {Laws.Spec.has_line(B.Path.child(d, B.Buf.path(B.Files.at(files, i))), B.Oil.list(files, d)) == True{} : Bool}:
  +x = B.Path.child(d, B.Buf.path(B.Files.at(files, i)))
  Bag.listed(x, files, d, Bag.hit(x, d, files, i, hx, {==}))

# (A): every file inside d has its child listed
# ---------------------------------------------

def Bag.hit2(+x: String, +d: String, pre: List<&2, T.Buf>, +p: String, -ls: List<&2, String>, -t: List<&2, T.Buf>, hx: {String.is_empty(B.Path.child(d, p)) == False{} : Bool}, he: {B.Path.child(d, p) == x : String})
  -> {Bag.AllF(QOpt{QOpt{QNe{x}}}, List.append(&2, T.Buf, pre, Con{T.Buf{p, ls}, t}), d) == False{} : Bool}:
  match pre:
    case Nil{}:
      +e = B.Path.child(d, p)
      Bag.hit_head(String.is_empty(e), String.eq(e, x), Bag.AllF(QOpt{QOpt{QNe{x}}}, t, d), hx, Tx.String.eq_same(e, x, he))
    case Con{b, +u}:
      match b:
        case T.Buf{+p2, ls2}:
          Bag.and_f(Bag.ok(QOpt{QOpt{QNe{x}}}, B.Path.child(d, p2)), Bag.AllF(QOpt{QOpt{QNe{x}}}, List.append(&2, T.Buf, u, Con{T.Buf{p, ls}, t}), d), Bag.hit2(x, d, u, p, ls, t, hx, he))

def Bag.cov_head(hb: Bool, +d: String, +p: String, +ls: List<&2, String>, +t: List<&2, T.Buf>, +pre: List<&2, T.Buf>, +eh: {Bool.and(Laws.Spec.prefix(d, p), Bool.not(String.eq(d, p))) == hb : Bool})
  -> {Laws.Spec.implies(hb, Laws.Spec.has_line(Laws.Spec.child(d, p), B.Oil.list(Sb.Files.norm(List.append(&2, T.Buf, pre, Con{T.Buf{p, ls}, t})), d))) == True{} : Bool}:
  match hb:
    case False{}:
      {==}
    case True{}:
      +hp = L.And.l(Laws.Spec.prefix(d, p), Bool.not(String.eq(d, p)), eh)
      +hn = Bag.not_true(String.eq(d, p), L.And.r(Laws.Spec.prefix(d, p), Bool.not(String.eq(d, p)), eh))
      +x = Laws.Spec.child(d, p)
      +sc = Bag.spec_child(d, p, Equal.trans(Bool, X.Text.prefix(d, p), Laws.Spec.prefix(d, p), True{}, Rb.Prefix.eq(d, p), hp))
      +ne = Equal.trans(Bool, String.is_empty(B.Path.child(d, p)), String.is_empty(x), False{}, Equal.cong(String, Bool, z => String.is_empty(z), B.Path.child(d, p), x, sc), Bag.here(d, p, hp, hn))
      +g = List.append(&2, T.Buf, pre, Con{T.Buf{p, ls}, t})
      +hf = Equal.trans(Bool, Bag.AllF(QOpt{QOpt{QNe{x}}}, Sb.Files.norm(g), d), Bag.AllF(QOpt{QOpt{QNe{x}}}, g, d), False{}, Bag.norm(QOpt{QOpt{QNe{x}}}, g, d), Bag.hit2(x, d, pre, p, ls, t, ne, sc))
      Bag.listed(x, Sb.Files.norm(g), d, hf)

def Bag.cov(+d: String, fs: List<&2, T.Buf>, +pre: List<&2, T.Buf>) -> {Laws.Spec.covers(d, fs, B.Oil.list(Sb.Files.norm(List.append(&2, T.Buf, pre, fs)), d)) == True{} : Bool}:
  match fs:
    case Nil{}:
      {==}
    case Con{b, +t}:
      match b:
        case T.Buf{+p, +ls}:
          +bf = {T.Buf{p, ls} : T.Buf}
          +g = List.append(&2, T.Buf, pre, bf <> t)
          +g2 = List.append(&2, T.Buf, List.append(&2, T.Buf, pre, [bf]), t)
          +c = Equal.cong(List<&2, T.Buf>, Bool, z => Laws.Spec.covers(d, t, B.Oil.list(Sb.Files.norm(z), d)), g2, g, Bag.fapp(pre, bf, t))
          +tl = Equal.trans(Bool, Laws.Spec.covers(d, t, B.Oil.list(Sb.Files.norm(g), d)), Laws.Spec.covers(d, t, B.Oil.list(Sb.Files.norm(g2), d)), True{}, Equal.sym(Bool, Laws.Spec.covers(d, t, B.Oil.list(Sb.Files.norm(g2), d)), Laws.Spec.covers(d, t, B.Oil.list(Sb.Files.norm(g), d)), c), Bag.cov(d, t, List.append(&2, T.Buf, pre, [bf])))
          +here = Bool.and(Laws.Spec.prefix(d, p), Bool.not(String.eq(d, p)))
          +hd = Laws.Spec.implies(here, Laws.Spec.has_line(Laws.Spec.child(d, p), B.Oil.list(Sb.Files.norm(g), d)))
          L.And.intro(hd, Laws.Spec.covers(d, t, B.Oil.list(Sb.Files.norm(g), d)), Bag.cov_head(here, d, p, ls, t, pre, {==}), tl)

def Bag.covers(+d: String, +fs: List<&2, T.Buf>) -> {Laws.Spec.covers(d, fs, B.Oil.list(Sb.Files.norm(fs), d)) == True{} : Bool}:
  Bag.cov(d, fs, Nil{})
