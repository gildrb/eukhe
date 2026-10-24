# eukhe: the ranking of bend/doc_glob.bend is the spec's (laws/doc_glob.bend)
#
# The code compares paths in one flat loop that carries the order of the
# chars before (cmp.go), tests that two paths differ by their hashes first
# (a path's hash is a function of its chars), and puts a path into the
# ranked list in one pass that also drops the older copy of its path
# (ins.go, rm.go). Each is shown equal to the spec's Lt, Eq, Before, Same,
# Unsame and Put, on the list of the spec's hits with their hashes (its).

import Base
import ../../../bend/doc_glob.bend as Gb
import ../../../laws/doc_glob.bend as DocGlob

# Logic
# -----

def gp.BIf(b: Bool, G: Type) -> Type:
  match b:
    case True{}:
      Unit
    case False{}:
      G

# no proof of False == True
def gp.absurd(-G: Type, e: {False{} == True{} : Bool}) -> G:
  %Equal.sym(Bool, False{}, True{}, e) : gp.BIf(_, G)
  Unit{}

def gp.and_t(a: Bool, b: Bool, ea: {a == True{} : Bool}, eb: {b == True{} : Bool}) -> {Bool.and(a, b) == True{} : Bool}:
  %Equal.sym(Bool, a, True{}, ea) : {Bool.and(_, b) == True{} : Bool}
  eb

def gp.and_l(a: Bool, -b: Bool, e: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      gp.absurd({False{} == True{} : Bool}, e)

def gp.and_r(a: Bool, -b: Bool, e: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      e
    case False{}:
      gp.absurd({b == True{} : Bool}, e)

# Nat
# ---

def gp.eq_refl(n: Nat) -> {Nat.is_eq(n, n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      gp.eq_refl(p)

def gp.eq_true(a: Nat, b: Nat, e: {Nat.is_eq(a, b) == True{} : Bool}) -> {a == b : Nat}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      gp.absurd({0n == 1n+q : Nat}, e)
    case 1n+p 0n:
      gp.absurd({1n+p == 0n : Nat}, e)
    case 1n+p 1n+q:
      Equal.cong(Nat, Nat, x => 1n+x, p, q, gp.eq_true(p, q, e))

# Strings
# -------

# a decided order stays
def gp.cmp_lt(a: String, b: String) -> {Gb.cmp.go(a, b, LT{}) == LT{} : Cmp}:
  match a b:
    case SNil{} SNil{}:
      {==}
    case SNil{} SCon{y, u}:
      {==}
    case SCon{x, t} SNil{}:
      {==}
    case SCon{x, t} SCon{y, u}:
      {==}

def gp.cmp_gt(a: String, b: String) -> {Gb.cmp.go(a, b, GT{}) == GT{} : Cmp}:
  match a b:
    case SNil{} SNil{}:
      {==}
    case SNil{} SCon{y, u}:
      {==}
    case SCon{x, t} SNil{}:
      {==}
    case SCon{x, t} SCon{y, u}:
      {==}

# the order of the spec: EQ for one path, else LT when a comes first
def gp.cmpOf(e: Bool, l: Bool) -> Cmp:
  match e:
    case True{}:
      EQ{}
    case False{}:
      match l:
        case True{}:
          LT{}
        case False{}:
          GT{}

# the tails after chars that compared c
def gp.cmp_c(c: Cmp, t: String, u: String, ih: {Gb.cmp.go(t, u, EQ{}) == gp.cmpOf(DocGlob.glob.Eq(t, u), DocGlob.glob.Lt(t, u)) : Cmp}) -> {Gb.cmp.go(t, u, c) == gp.cmpOf(Bool.and(Cmp.is_eq(c), DocGlob.glob.Eq(t, u)), Bool.or(Cmp.is_lt(c), Bool.and(Cmp.is_eq(c), DocGlob.glob.Lt(t, u)))) : Cmp}:
  match c:
    case LT{}:
      gp.cmp_lt(t, u)
    case EQ{}:
      ih
    case GT{}:
      gp.cmp_gt(t, u)

# cmp.go from no decided order is the spec's order
def gp.cmp(a: String, b: String) -> {Gb.cmp.go(a, b, EQ{}) == gp.cmpOf(DocGlob.glob.Eq(a, b), DocGlob.glob.Lt(a, b)) : Cmp}:
  match a b:
    case SNil{} SNil{}:
      {==}
    case SNil{} SCon{y, u}:
      {==}
    case SCon{x, t} SNil{}:
      {==}
    case SCon{Chr{+xv}, +t} SCon{Chr{+yv}, +u}:
      gp.cmp_c(Nat.cmp(U32.to_nat(xv), U32.to_nat(yv)), t, u, gp.cmp(t, u))

# one path does not come before itself
def gp.lt_eq_c(c: Cmp, t: String, u: String, e: {Bool.and(Cmp.is_eq(c), DocGlob.glob.Eq(t, u)) == True{} : Bool}, ih: {DocGlob.glob.Eq(t, u) == True{} : Bool} -> {DocGlob.glob.Lt(t, u) == False{} : Bool}) -> {Bool.or(Cmp.is_lt(c), Bool.and(Cmp.is_eq(c), DocGlob.glob.Lt(t, u))) == False{} : Bool}:
  match c:
    case LT{}:
      gp.absurd({True{} == False{} : Bool}, e)
    case EQ{}:
      ih(e)
    case GT{}:
      gp.absurd({False{} == False{} : Bool}, e)

def gp.lt_eq(a: String, b: String, e: {DocGlob.glob.Eq(a, b) == True{} : Bool}) -> {DocGlob.glob.Lt(a, b) == False{} : Bool}:
  match a b:
    case SNil{} SNil{}:
      {==}
    case SNil{} SCon{y, u}:
      gp.absurd({True{} == False{} : Bool}, e)
    case SCon{x, t} SNil{}:
      gp.absurd({False{} == False{} : Bool}, e)
    case SCon{Chr{+xv}, +t} SCon{Chr{+yv}, +u}:
      gp.lt_eq_c(Nat.cmp(U32.to_nat(xv), U32.to_nat(yv)), t, u, e, e2 => gp.lt_eq(t, u, e2))

# Hashes
# ------

def gp.code_eq(+x: U32, +y: U32, e: {Nat.is_eq(U32.to_nat(x), U32.to_nat(y)) == True{} : Bool}) -> {U32.to_nat(x) == U32.to_nat(y) : Nat}:
  gp.eq_true(U32.to_nat(x), U32.to_nat(y), e)

# one path (the same chars) has one hash
def gp.hash_eq(a: String, b: String, +acc: Nat, +e: {DocGlob.glob.Eq(a, b) == True{} : Bool}) -> {Gb.hash.go(a, acc) == Gb.hash.go(b, acc) : Nat}:
  match a b:
    case SNil{} SNil{}:
      {==}
    case SNil{} SCon{y, u}:
      gp.absurd({acc == Gb.hash.go(SCon{y, u}, acc) : Nat}, e)
    case SCon{x, t} SNil{}:
      gp.absurd({Gb.hash.go(SCon{x, t}, acc) == acc : Nat}, e)
    case SCon{Chr{+xv}, +t} SCon{Chr{+yv}, +u}:
      +ec = gp.code_eq(xv, yv, gp.and_l(Nat.is_eq(U32.to_nat(xv), U32.to_nat(yv)), DocGlob.glob.Eq(t, u), e))
      %ec : {Gb.hash.go(t, Nat.mod(Nat.add(Nat.mul(acc, 31n), U32.to_nat(xv)), 63001n)) == Gb.hash.go(u, Nat.mod(Nat.add(Nat.mul(acc, 31n), _), 63001n)) : Nat}
      gp.hash_eq(t, u, Nat.mod(Nat.add(Nat.mul(acc, 31n), U32.to_nat(xv)), 63001n), gp.and_r(Nat.is_eq(U32.to_nat(xv), U32.to_nat(yv)), DocGlob.glob.Eq(t, u), e))

def gp.true_eq(+x: Nat, +y: Nat, hq: {x == y : Nat}) -> {True{} == Nat.is_eq(x, y) : Bool}:
  %hq : {True{} == Nat.is_eq(x, _) : Bool}
  Equal.sym(Bool, Nat.is_eq(x, x), True{}, gp.eq_refl(x))

def gp.neq.go(q: Bool, +a: String, +b: String, eq: {DocGlob.glob.Eq(a, b) == q : Bool}, e: {Nat.is_eq(Gb.hash(a), Gb.hash(b)) == False{} : Bool}) -> {q == False{} : Bool}:
  match q:
    case True{}:
      Equal.trans(Bool, True{}, Nat.is_eq(Gb.hash(a), Gb.hash(b)), False{}, gp.true_eq(Gb.hash(a), Gb.hash(b), gp.hash_eq(a, b, 0n, eq)), e)
    case False{}:
      {==}

# paths whose hashes differ are not one path
def gp.neq(+a: String, +b: String, e: {Nat.is_eq(Gb.hash(a), Gb.hash(b)) == False{} : Bool}) -> {DocGlob.glob.Eq(a, b) == False{} : Bool}:
  gp.neq.go(DocGlob.glob.Eq(a, b), a, b, {==}, e)

# Hits as kept paths
# ------------------

# a hit as the code keeps it: with the hash of its path
def gp.it(h: DocGlob.glob.Hit) -> Gb.It:
  match h:
    case DocGlob.glob.Hit{m, p}:
      Gb.it(m, p)

def gp.its(hs: List<&2, DocGlob.glob.Hit>) -> List<&2, Gb.It>:
  match hs:
    case Nil{}:
      Nil{}
    case h <> t:
      gp.it(h) <> gp.its(t)

# how x stands to y in the spec: before it; else a hit of its path; else
# behind it
def gp.relOf(b: Bool, s: Bool) -> Gb.Rel:
  match b:
    case True{}:
      Gb.Ahead{}
    case False{}:
      match s:
        case True{}:
          Gb.Twin{}
        case False{}:
          Gb.Behind{}

# same time: the order of the paths (e: one path; l: x's first)
def gp.path_of(e: Bool, l: Bool, ex: {e == True{} : Bool} -> {l == False{} : Bool}) -> {Gb.rel.path(gp.cmpOf(e, l)) == gp.relOf(l, e) : Gb.Rel}:
  match e:
    case True{}:
      match l:
        case True{}:
          gp.absurd({Gb.Twin{} == Gb.Ahead{} : Gb.Rel}, Equal.sym(Bool, True{}, False{}, ex({==})))
        case False{}:
          {==}
    case False{}:
      match l:
        case True{}:
          {==}
        case False{}:
          {==}

# x older: one path or not
def gp.same_of(e: Bool, l: Bool) -> {Gb.rel.same(gp.cmpOf(e, l)) == gp.relOf(False{}, e) : Gb.Rel}:
  match e:
    case True{}:
      {==}
    case False{}:
      match l:
        case True{}:
          {==}
        case False{}:
          {==}

def gp.path(+xp: String, +yp: String) -> {Gb.rel.path(Gb.cmp.go(xp, yp, EQ{})) == gp.relOf(DocGlob.glob.Lt(xp, yp), DocGlob.glob.Eq(xp, yp)) : Gb.Rel}:
  %Equal.sym(Cmp, Gb.cmp.go(xp, yp, EQ{}), gp.cmpOf(DocGlob.glob.Eq(xp, yp), DocGlob.glob.Lt(xp, yp)), gp.cmp(xp, yp)) : {Gb.rel.path(_) == gp.relOf(DocGlob.glob.Lt(xp, yp), DocGlob.glob.Eq(xp, yp)) : Gb.Rel}
  gp.path_of(DocGlob.glob.Eq(xp, yp), DocGlob.glob.Lt(xp, yp), e => gp.lt_eq(xp, yp, e))

def gp.same(+xp: String, +yp: String) -> {Gb.rel.same(Gb.cmp.go(xp, yp, EQ{})) == gp.relOf(False{}, DocGlob.glob.Eq(xp, yp)) : Gb.Rel}:
  %Equal.sym(Cmp, Gb.cmp.go(xp, yp, EQ{}), gp.cmpOf(DocGlob.glob.Eq(xp, yp), DocGlob.glob.Lt(xp, yp)), gp.cmp(xp, yp)) : {Gb.rel.same(_) == gp.relOf(False{}, DocGlob.glob.Eq(xp, yp)) : Gb.Rel}
  gp.same_of(DocGlob.glob.Eq(xp, yp), DocGlob.glob.Lt(xp, yp))

# x older, q: the hashes are equal
def gp.older(q: Bool, +xp: String, +yp: String, eq: {Nat.is_eq(Gb.hash(xp), Gb.hash(yp)) == q : Bool}) -> {Gb.rel.older(q, xp, yp) == gp.relOf(False{}, DocGlob.glob.Eq(xp, yp)) : Gb.Rel}:
  match q:
    case True{}:
      gp.same(xp, yp)
    case False{}:
      %Equal.sym(Bool, DocGlob.glob.Eq(xp, yp), False{}, gp.neq(xp, yp, eq)) : {Gb.Behind{} == gp.relOf(False{}, _) : Gb.Rel}
      {==}

def gp.rel_c(c: Cmp, +xp: String, +yp: String) -> {Gb.rel.time(c, xp, Gb.hash(xp), yp, Gb.hash(yp)) == gp.relOf(Bool.or(Cmp.is_gt(c), Bool.and(Cmp.is_eq(c), DocGlob.glob.Lt(xp, yp))), DocGlob.glob.Eq(xp, yp)) : Gb.Rel}:
  match c:
    case LT{}:
      gp.older(Nat.is_eq(Gb.hash(xp), Gb.hash(yp)), xp, yp, {==})
    case EQ{}:
      gp.path(xp, yp)
    case GT{}:
      {==}

# the code's rel of two hits is the spec's
def gp.rel(x: DocGlob.glob.Hit, y: DocGlob.glob.Hit) -> {Gb.rel(gp.it(x), gp.it(y)) == gp.relOf(DocGlob.glob.Before(x, y), DocGlob.glob.Same(x, y)) : Gb.Rel}:
  match x y:
    case DocGlob.glob.Hit{+xm, +xp} DocGlob.glob.Hit{+ym, +yp}:
      gp.rel_c(Nat.cmp(xm, ym), xp, yp)

def gp.named_of(e: Bool, l: Bool) -> {Cmp.is_eq(gp.cmpOf(e, l)) == e : Bool}:
  match e:
    case True{}:
      {==}
    case False{}:
      match l:
        case True{}:
          {==}
        case False{}:
          {==}

def gp.named_h(q: Bool, +xp: String, +yp: String, eq: {Nat.is_eq(Gb.hash(xp), Gb.hash(yp)) == q : Bool}) -> {Gb.named.h(q, xp, yp) == DocGlob.glob.Eq(xp, yp) : Bool}:
  match q:
    case True{}:
      %Equal.sym(Cmp, Gb.cmp.go(xp, yp, EQ{}), gp.cmpOf(DocGlob.glob.Eq(xp, yp), DocGlob.glob.Lt(xp, yp)), gp.cmp(xp, yp)) : {Cmp.is_eq(_) == DocGlob.glob.Eq(xp, yp) : Bool}
      gp.named_of(DocGlob.glob.Eq(xp, yp), DocGlob.glob.Lt(xp, yp))
    case False{}:
      Equal.sym(Bool, DocGlob.glob.Eq(xp, yp), False{}, gp.neq(xp, yp, eq))

# the code's named of two hits is the spec's Same
def gp.named(x: DocGlob.glob.Hit, y: DocGlob.glob.Hit) -> {Gb.named(gp.it(x), gp.it(y)) == DocGlob.glob.Same(x, y) : Bool}:
  match x y:
    case DocGlob.glob.Hit{xm, +xp} DocGlob.glob.Hit{ym, +yp}:
      gp.named_h(Nat.is_eq(Gb.hash(xp), Gb.hash(yp)), xp, yp, {==})

# Putting a hit in
# ----------------

# rm.go after y, on t: the spec's Unsame of y <> t (b: y is x's path)
def gp.rm_go(t: List<&2, DocGlob.glob.Hit>, +x: DocGlob.glob.Hit, +y: DocGlob.glob.Hit, b: Bool) -> {Gb.rm.go(gp.its(t), gp.it(x), gp.it(y), b) == gp.its(DocGlob.glob.If(List<&2, DocGlob.glob.Hit>, b, t, y <> DocGlob.glob.Unsame(x, t))) : List<&2, Gb.It>}:
  match t:
    case Nil{}:
      match b:
        case True{}:
          {==}
        case False{}:
          {==}
    case +z <> +u:
      match b:
        case True{}:
          {==}
        case False{}:
          %Equal.sym(Bool, Gb.named(gp.it(x), gp.it(z)), DocGlob.glob.Same(x, z), gp.named(x, z)) : {gp.it(y) <> Gb.rm.go(gp.its(u), gp.it(x), gp.it(z), _) == gp.its(y <> DocGlob.glob.Unsame(x, z <> u)) : List<&2, Gb.It>}
          Equal.cong(List<&2, Gb.It>, List<&2, Gb.It>, l => gp.it(y) <> l, Gb.rm.go(gp.its(u), gp.it(x), gp.it(z), DocGlob.glob.Same(x, z)), gp.its(DocGlob.glob.If(List<&2, DocGlob.glob.Hit>, DocGlob.glob.Same(x, z), u, z <> DocGlob.glob.Unsame(x, u))), gp.rm_go(u, x, z, DocGlob.glob.Same(x, z)))

# the code drops the first older copy of x's path as the spec does
def gp.rm(+t: List<&2, DocGlob.glob.Hit>, +x: DocGlob.glob.Hit, +y: DocGlob.glob.Hit) -> {Gb.rm.go(gp.its(t), gp.it(x), gp.it(y), Gb.named(gp.it(x), gp.it(y))) == gp.its(DocGlob.glob.Unsame(x, y <> t)) : List<&2, Gb.It>}:
  %Equal.sym(Bool, Gb.named(gp.it(x), gp.it(y)), DocGlob.glob.Same(x, y), gp.named(x, y)) : {Gb.rm.go(gp.its(t), gp.it(x), gp.it(y), _) == gp.its(DocGlob.glob.Unsame(x, y <> t)) : List<&2, Gb.It>}
  gp.rm_go(t, x, y, DocGlob.glob.Same(x, y))

# ins.go on Nil after y, as x stands to y (bf: before; sm: one path)
def gp.ins_nil(bf: Bool, sm: Bool, +x: DocGlob.glob.Hit, +y: DocGlob.glob.Hit) -> {Gb.ins.go(Nil{}, gp.it(x), gp.it(y), gp.relOf(bf, sm)) == gp.its(DocGlob.glob.If(List<&2, DocGlob.glob.Hit>, bf, x <> DocGlob.glob.Unsame(x, [y]), DocGlob.glob.If(List<&2, DocGlob.glob.Hit>, sm, [y], y <> DocGlob.glob.Put(x, Nil{})))) : List<&2, Gb.It>}:
  match bf:
    case True{}:
      Equal.cong(List<&2, Gb.It>, List<&2, Gb.It>, l => gp.it(x) <> l, Gb.rm.go(Nil{}, gp.it(x), gp.it(y), Gb.named(gp.it(x), gp.it(y))), gp.its(DocGlob.glob.Unsame(x, [y])), gp.rm(Nil{}, x, y))
    case False{}:
      match sm:
        case True{}:
          {==}
        case False{}:
          {==}

# ins.go on z <> u after y, as x stands to y
def gp.ins_cons(bf: Bool, sm: Bool, +x: DocGlob.glob.Hit, +y: DocGlob.glob.Hit, +z: DocGlob.glob.Hit, +u: List<&2, DocGlob.glob.Hit>, ih: {Gb.ins.go(gp.its(u), gp.it(x), gp.it(z), Gb.rel(gp.it(x), gp.it(z))) == gp.its(DocGlob.glob.Put(x, z <> u)) : List<&2, Gb.It>}) -> {Gb.ins.go(gp.it(z) <> gp.its(u), gp.it(x), gp.it(y), gp.relOf(bf, sm)) == gp.its(DocGlob.glob.If(List<&2, DocGlob.glob.Hit>, bf, x <> DocGlob.glob.Unsame(x, y <> z <> u), DocGlob.glob.If(List<&2, DocGlob.glob.Hit>, sm, y <> z <> u, y <> DocGlob.glob.Put(x, z <> u)))) : List<&2, Gb.It>}:
  match bf:
    case True{}:
      Equal.cong(List<&2, Gb.It>, List<&2, Gb.It>, l => gp.it(x) <> l, Gb.rm.go(gp.it(z) <> gp.its(u), gp.it(x), gp.it(y), Gb.named(gp.it(x), gp.it(y))), gp.its(DocGlob.glob.Unsame(x, y <> z <> u)), gp.rm(z <> u, x, y))
    case False{}:
      match sm:
        case True{}:
          {==}
        case False{}:
          Equal.cong(List<&2, Gb.It>, List<&2, Gb.It>, l => gp.it(y) <> l, Gb.ins.go(gp.its(u), gp.it(x), gp.it(z), Gb.rel(gp.it(x), gp.it(z))), gp.its(DocGlob.glob.Put(x, z <> u)), ih)

# ins.go after y, on t: the spec's Put of x into y <> t
def gp.ins_go(t: List<&2, DocGlob.glob.Hit>, +x: DocGlob.glob.Hit, +y: DocGlob.glob.Hit) -> {Gb.ins.go(gp.its(t), gp.it(x), gp.it(y), Gb.rel(gp.it(x), gp.it(y))) == gp.its(DocGlob.glob.Put(x, y <> t)) : List<&2, Gb.It>}:
  match t:
    case Nil{}:
      %Equal.sym(Gb.Rel, Gb.rel(gp.it(x), gp.it(y)), gp.relOf(DocGlob.glob.Before(x, y), DocGlob.glob.Same(x, y)), gp.rel(x, y)) : {Gb.ins.go(Nil{}, gp.it(x), gp.it(y), _) == gp.its(DocGlob.glob.Put(x, [y])) : List<&2, Gb.It>}
      gp.ins_nil(DocGlob.glob.Before(x, y), DocGlob.glob.Same(x, y), x, y)
    case +z <> +u:
      %Equal.sym(Gb.Rel, Gb.rel(gp.it(x), gp.it(y)), gp.relOf(DocGlob.glob.Before(x, y), DocGlob.glob.Same(x, y)), gp.rel(x, y)) : {Gb.ins.go(gp.it(z) <> gp.its(u), gp.it(x), gp.it(y), _) == gp.its(DocGlob.glob.Put(x, y <> z <> u)) : List<&2, Gb.It>}
      gp.ins_cons(DocGlob.glob.Before(x, y), DocGlob.glob.Same(x, y), x, y, z, u, gp.ins_go(u, x, z))

# the code puts a hit into the kept paths as the spec does
def gp.ins(+x: DocGlob.glob.Hit, ys: List<&2, DocGlob.glob.Hit>) -> {Gb.ins(gp.it(x), gp.its(ys)) == gp.its(DocGlob.glob.Put(x, ys)) : List<&2, Gb.It>}:
  match ys:
    case Nil{}:
      {==}
    case +y <> +t:
      gp.ins_go(t, x, y)
