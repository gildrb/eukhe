# eukhe: what the glob core keeps is the head of the spec's ranking
#
# The core keeps only the first c ranked hits (c = S + K + 1). Putting a
# hit into those and keeping c is putting it into the whole ranking and
# keeping c (put_first). A hit the entry does not want (c kept, all newer)
# changes nothing of the first c (filter). The code's cut (fin) is the
# spec's First with its length and oldest time.

import Base
import ../../../bend/doc_glob.bend as Gb
import ../../../laws/doc_glob.bend as DocGlob
import ./rank.bend as GR

# First and Unsame
# ----------------

# keeping k of the first k
def gp.ff(L: List<&2, DocGlob.glob.Hit>, k: Nat) -> {DocGlob.glob.First(DocGlob.glob.First(L, k), k) == DocGlob.glob.First(L, k) : List<&2, DocGlob.glob.Hit>}:
  match L:
    case Nil{}:
      {==}
    case +r <> t:
      match k:
        case 0n:
          {==}
        case 1n+d:
          Equal.cong(List<&2, DocGlob.glob.Hit>, List<&2, DocGlob.glob.Hit>, l => r <> l, DocGlob.glob.First(DocGlob.glob.First(t, d), d), DocGlob.glob.First(t, d), gp.ff(t, d))

# keeping k of the first k + 1
def gp.ff1(L: List<&2, DocGlob.glob.Hit>, k: Nat) -> {DocGlob.glob.First(DocGlob.glob.First(L, 1n+k), k) == DocGlob.glob.First(L, k) : List<&2, DocGlob.glob.Hit>}:
  match L:
    case Nil{}:
      {==}
    case +r <> t:
      match k:
        case 0n:
          {==}
        case 1n+d:
          Equal.cong(List<&2, DocGlob.glob.Hit>, List<&2, DocGlob.glob.Hit>, l => r <> l, DocGlob.glob.First(DocGlob.glob.First(t, 1n+d), d), DocGlob.glob.First(t, d), gp.ff1(t, d))

def gp.first0(L: List<&2, DocGlob.glob.Hit>) -> {DocGlob.glob.First(L, 0n) == Nil{} : List<&2, DocGlob.glob.Hit>}:
  match L:
    case Nil{}:
      {==}
    case r <> t:
      {==}

# after z (b: z is x's path), keeping e + 1
def gp.us_b(b: Bool, +x: DocGlob.glob.Hit, +z: DocGlob.glob.Hit, +w: List<&2, DocGlob.glob.Hit>, +e: Nat, ih: {DocGlob.glob.First(DocGlob.glob.Unsame(x, DocGlob.glob.First(w, 1n+e)), e) == DocGlob.glob.First(DocGlob.glob.Unsame(x, w), e) : List<&2, DocGlob.glob.Hit>}) -> {DocGlob.glob.First(DocGlob.glob.If(List<&2, DocGlob.glob.Hit>, b, DocGlob.glob.First(w, 1n+e), z <> DocGlob.glob.Unsame(x, DocGlob.glob.First(w, 1n+e))), 1n+e) == DocGlob.glob.First(DocGlob.glob.If(List<&2, DocGlob.glob.Hit>, b, w, z <> DocGlob.glob.Unsame(x, w)), 1n+e) : List<&2, DocGlob.glob.Hit>}:
  match b:
    case True{}:
      gp.ff(w, 1n+e)
    case False{}:
      Equal.cong(List<&2, DocGlob.glob.Hit>, List<&2, DocGlob.glob.Hit>, l => z <> l, DocGlob.glob.First(DocGlob.glob.Unsame(x, DocGlob.glob.First(w, 1n+e)), e), DocGlob.glob.First(DocGlob.glob.Unsame(x, w), e), ih)

# dropping x's path from the first d + 1 keeps the first d of dropping it
# from all
def gp.unsame_first(+x: DocGlob.glob.Hit, L: List<&2, DocGlob.glob.Hit>, d: Nat) -> {DocGlob.glob.First(DocGlob.glob.Unsame(x, DocGlob.glob.First(L, 1n+d)), d) == DocGlob.glob.First(DocGlob.glob.Unsame(x, L), d) : List<&2, DocGlob.glob.Hit>}:
  match L:
    case Nil{}:
      {==}
    case +z <> +w:
      match d:
        case 0n:
          Equal.trans(List<&2, DocGlob.glob.Hit>, DocGlob.glob.First(DocGlob.glob.Unsame(x, DocGlob.glob.First(z <> w, 1n)), 0n), Nil{}, DocGlob.glob.First(DocGlob.glob.Unsame(x, z <> w), 0n), gp.first0(DocGlob.glob.Unsame(x, DocGlob.glob.First(z <> w, 1n))), Equal.sym(List<&2, DocGlob.glob.Hit>, DocGlob.glob.First(DocGlob.glob.Unsame(x, z <> w), 0n), Nil{}, gp.first0(DocGlob.glob.Unsame(x, z <> w))))
        case 1n++e:
          gp.us_b(DocGlob.glob.Same(x, z), x, z, w, e, gp.unsame_first(x, w, e))

# Putting into the kept head
# --------------------------

def gp.pf_b(bf: Bool, sm: Bool, +x: DocGlob.glob.Hit, +y: DocGlob.glob.Hit, +t: List<&2, DocGlob.glob.Hit>, +d: Nat, ih: {DocGlob.glob.First(DocGlob.glob.Put(x, DocGlob.glob.First(t, d)), d) == DocGlob.glob.First(DocGlob.glob.Put(x, t), d) : List<&2, DocGlob.glob.Hit>}) -> {DocGlob.glob.First(DocGlob.glob.If(List<&2, DocGlob.glob.Hit>, bf, x <> DocGlob.glob.Unsame(x, y <> DocGlob.glob.First(t, d)), DocGlob.glob.If(List<&2, DocGlob.glob.Hit>, sm, y <> DocGlob.glob.First(t, d), y <> DocGlob.glob.Put(x, DocGlob.glob.First(t, d)))), 1n+d) == DocGlob.glob.First(DocGlob.glob.If(List<&2, DocGlob.glob.Hit>, bf, x <> DocGlob.glob.Unsame(x, y <> t), DocGlob.glob.If(List<&2, DocGlob.glob.Hit>, sm, y <> t, y <> DocGlob.glob.Put(x, t))), 1n+d) : List<&2, DocGlob.glob.Hit>}:
  match bf:
    case True{}:
      Equal.cong(List<&2, DocGlob.glob.Hit>, List<&2, DocGlob.glob.Hit>, l => x <> l, DocGlob.glob.First(DocGlob.glob.Unsame(x, DocGlob.glob.First(y <> t, 1n+d)), d), DocGlob.glob.First(DocGlob.glob.Unsame(x, y <> t), d), gp.unsame_first(x, y <> t, d))
    case False{}:
      match sm:
        case True{}:
          Equal.cong(List<&2, DocGlob.glob.Hit>, List<&2, DocGlob.glob.Hit>, l => y <> l, DocGlob.glob.First(DocGlob.glob.First(t, d), d), DocGlob.glob.First(t, d), gp.ff(t, d))
        case False{}:
          Equal.cong(List<&2, DocGlob.glob.Hit>, List<&2, DocGlob.glob.Hit>, l => y <> l, DocGlob.glob.First(DocGlob.glob.Put(x, DocGlob.glob.First(t, d)), d), DocGlob.glob.First(DocGlob.glob.Put(x, t), d), ih)

# putting x into the first c ranked hits and keeping c is putting it into
# all of them and keeping c
def gp.put_first(+x: DocGlob.glob.Hit, R: List<&2, DocGlob.glob.Hit>, c: Nat) -> {DocGlob.glob.First(DocGlob.glob.Put(x, DocGlob.glob.First(R, c)), c) == DocGlob.glob.First(DocGlob.glob.Put(x, R), c) : List<&2, DocGlob.glob.Hit>}:
  match R:
    case Nil{}:
      {==}
    case +y <> +t:
      match c:
        case 0n:
          Equal.sym(List<&2, DocGlob.glob.Hit>, DocGlob.glob.First(DocGlob.glob.Put(x, y <> t), 0n), Nil{}, gp.first0(DocGlob.glob.Put(x, y <> t)))
        case 1n++d:
          gp.pf_b(DocGlob.glob.Before(x, y), DocGlob.glob.Same(x, y), x, y, t, d, gp.put_first(x, t, d))

# A hit the entry does not want
# -----------------------------

def gp.lt_min_l(m: Nat, a: Nat, b: Nat, h: {Nat.is_lt(m, Nat.min(a, b)) == True{} : Bool}) -> {Nat.is_lt(m, a) == True{} : Bool}:
  match m a b:
    case m 0n b:
      GR.gp.absurd({Nat.is_lt(m, 0n) == True{} : Bool}, h)
    case m 1n+ap 0n:
      GR.gp.absurd({Nat.is_lt(m, 1n+ap) == True{} : Bool}, h)
    case 0n 1n+ap 1n+bp:
      {==}
    case 1n+mp 1n+ap 1n+bp:
      gp.lt_min_l(mp, ap, bp, h)

def gp.lt_min_r(m: Nat, a: Nat, b: Nat, h: {Nat.is_lt(m, Nat.min(a, b)) == True{} : Bool}) -> {Nat.is_lt(m, b) == True{} : Bool}:
  match m a b:
    case m 0n b:
      GR.gp.absurd({Nat.is_lt(m, b) == True{} : Bool}, h)
    case m 1n+ap 0n:
      GR.gp.absurd({Nat.is_lt(m, 0n) == True{} : Bool}, h)
    case 0n 1n+ap 1n+bp:
      {==}
    case 1n+mp 1n+ap 1n+bp:
      gp.lt_min_r(mp, ap, bp, h)

# older than the oldest of y (at a) and F: older than y
def gp.low_head(+m: Nat, F: List<&2, DocGlob.glob.Hit>, +a: Nat, h: {Nat.is_lt(m, DocGlob.glob.Low.go(F, a)) == True{} : Bool}) -> {Nat.is_lt(m, a) == True{} : Bool}:
  match F:
    case Nil{}:
      h
    case z <> u:
      match z:
        case DocGlob.glob.Hit{az, qz}:
          gp.lt_min_l(m, a, DocGlob.glob.Low.go(u, az), h)

# older than the oldest of y and the first e + 1 of t: older than the
# oldest of those (there is one: c of them are kept)
def gp.old_tail(+m: Nat, y: DocGlob.glob.Hit, t: List<&2, DocGlob.glob.Hit>, +e: Nat, old: {Nat.is_lt(m, DocGlob.glob.Low(y <> DocGlob.glob.First(t, 1n+e))) == True{} : Bool}, full: {Nat.is_le(1n+e, DocGlob.glob.Len(DocGlob.glob.First(t, 1n+e))) == True{} : Bool}) -> {Nat.is_lt(m, DocGlob.glob.Low(DocGlob.glob.First(t, 1n+e))) == True{} : Bool}:
  match y:
    case DocGlob.glob.Hit{my, py}:
      match t:
        case Nil{}:
          GR.gp.absurd({Nat.is_lt(m, 0n) == True{} : Bool}, full)
        case z <> u:
          match z:
            case DocGlob.glob.Hit{az, qz}:
              gp.lt_min_r(m, my, DocGlob.glob.Low.go(DocGlob.glob.First(u, e), az), old)

# a hit older than y does not rank before it
def gp.nb(c: Cmp, l: Bool, lt: {Cmp.is_lt(c) == True{} : Bool}) -> {Bool.or(Cmp.is_gt(c), Bool.and(Cmp.is_eq(c), l)) == False{} : Bool}:
  match c:
    case LT{}:
      {==}
    case EQ{}:
      GR.gp.absurd({Bool.and(True{}, l) == False{} : Bool}, lt)
    case GT{}:
      GR.gp.absurd({True{} == False{} : Bool}, lt)

def gp.filter_sm(sm: Bool, +x: DocGlob.glob.Hit, +y: DocGlob.glob.Hit, +t: List<&2, DocGlob.glob.Hit>, +d: Nat, ih: {DocGlob.glob.First(DocGlob.glob.Put(x, t), d) == DocGlob.glob.First(t, d) : List<&2, DocGlob.glob.Hit>}) -> {DocGlob.glob.First(DocGlob.glob.If(List<&2, DocGlob.glob.Hit>, sm, y <> t, y <> DocGlob.glob.Put(x, t)), 1n+d) == DocGlob.glob.First(y <> t, 1n+d) : List<&2, DocGlob.glob.Hit>}:
  match sm:
    case True{}:
      {==}
    case False{}:
      Equal.cong(List<&2, DocGlob.glob.Hit>, List<&2, DocGlob.glob.Hit>, l => y <> l, DocGlob.glob.First(DocGlob.glob.Put(x, t), d), DocGlob.glob.First(t, d), ih)

# x (at m) older than y and every kept hit after it
def gp.filter_cons(+m: Nat, +p: String, y: DocGlob.glob.Hit, +t: List<&2, DocGlob.glob.Hit>, +d: Nat, old: {Nat.is_lt(m, DocGlob.glob.Low(y <> DocGlob.glob.First(t, d))) == True{} : Bool}, ih: {DocGlob.glob.First(DocGlob.glob.Put(DocGlob.glob.Hit{m, p}, t), d) == DocGlob.glob.First(t, d) : List<&2, DocGlob.glob.Hit>}) -> {DocGlob.glob.First(DocGlob.glob.Put(DocGlob.glob.Hit{m, p}, y <> t), 1n+d) == DocGlob.glob.First(y <> t, 1n+d) : List<&2, DocGlob.glob.Hit>}:
  match y:
    case DocGlob.glob.Hit{+my, +py}:
      +nb = gp.nb(Nat.cmp(m, my), DocGlob.glob.Lt(p, py), gp.low_head(m, DocGlob.glob.First(t, d), my, old))
      %Equal.sym(Bool, Bool.or(Nat.is_gt(m, my), Bool.and(Nat.is_eq(m, my), DocGlob.glob.Lt(p, py))), False{}, nb) : {DocGlob.glob.First(DocGlob.glob.If(List<&2, DocGlob.glob.Hit>, _, DocGlob.glob.Hit{m, p} <> DocGlob.glob.Unsame(DocGlob.glob.Hit{m, p}, DocGlob.glob.Hit{my, py} <> t), DocGlob.glob.If(List<&2, DocGlob.glob.Hit>, DocGlob.glob.Same(DocGlob.glob.Hit{m, p}, DocGlob.glob.Hit{my, py}), DocGlob.glob.Hit{my, py} <> t, DocGlob.glob.Hit{my, py} <> DocGlob.glob.Put(DocGlob.glob.Hit{m, p}, t))), 1n+d) == DocGlob.glob.First(DocGlob.glob.Hit{my, py} <> t, 1n+d) : List<&2, DocGlob.glob.Hit>}
      gp.filter_sm(DocGlob.glob.Same(DocGlob.glob.Hit{m, p}, DocGlob.glob.Hit{my, py}), DocGlob.glob.Hit{m, p}, DocGlob.glob.Hit{my, py}, t, d, ih)

# a hit the entry does not want (c kept, all newer) changes nothing of
# the first c
def gp.filter(+m: Nat, +p: String, R: List<&2, DocGlob.glob.Hit>, c: Nat, +full: {Nat.is_le(c, DocGlob.glob.Len(DocGlob.glob.First(R, c))) == True{} : Bool}, +old: {Nat.is_lt(m, DocGlob.glob.Low(DocGlob.glob.First(R, c))) == True{} : Bool}) -> {DocGlob.glob.First(DocGlob.glob.Put(DocGlob.glob.Hit{m, p}, R), c) == DocGlob.glob.First(R, c) : List<&2, DocGlob.glob.Hit>}:
  match R:
    case Nil{}:
      match c:
        case 0n:
          {==}
        case 1n+d:
          GR.gp.absurd({DocGlob.glob.First([DocGlob.glob.Hit{m, p}], 1n+d) == Nil{} : List<&2, DocGlob.glob.Hit>}, full)
    case +y <> +t:
      match c:
        case 0n:
          gp.first0(DocGlob.glob.Put(DocGlob.glob.Hit{m, p}, y <> t))
        case 1n+d:
          match d:
            case 0n:
              gp.filter_cons(m, p, y, t, 0n, old, Equal.trans(List<&2, DocGlob.glob.Hit>, DocGlob.glob.First(DocGlob.glob.Put(DocGlob.glob.Hit{m, p}, t), 0n), Nil{}, DocGlob.glob.First(t, 0n), gp.first0(DocGlob.glob.Put(DocGlob.glob.Hit{m, p}, t)), Equal.sym(List<&2, DocGlob.glob.Hit>, DocGlob.glob.First(t, 0n), Nil{}, gp.first0(t))))
            case 1n++e:
              gp.filter_cons(m, p, y, t, 1n+e, old, gp.filter(m, p, t, 1n+e, full, gp.old_tail(m, y, t, e, old, full)))
