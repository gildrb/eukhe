# eukhe: lemmas of area listing: the order of the rows
#
# A row is before another by three compares, read in turn: the times
# (newer first), the ids (char codes, item by item), the places. Each
# compare is a Cmp (lo.lcmp on Nat lists, Nat.cmp on places); lo.F reads
# the three. The code's Ls.before and the spec's sp_before are both lo.F
# (lo.before_code, lo.before_spec), and lo.F is a strict order: never both
# ways (lo.F_asym), one way when the places differ (lo.F_total), and
# transitive (lo.F_trans) because each compare is: EQ only on equal
# items (lo.leq, lo.neq), LT transitive (lo.llt, lo.nlt), flipped when
# read the other way (lo.lflip, lo.nflip).

import Base
import ../../../bend/staging.bend as Sg
import ../../../bend/listing.bend as Ls
import ../../../laws/listing.bend as Listing

# Cmp
# ---

def lo.flip(c: Cmp) -> Cmp:
  match c:
    case LT{}:
      GT{}
    case EQ{}:
      EQ{}
    case GT{}:
      LT{}

def lo.WhenLt(c: Cmp, G: Type) -> Type:
  match c:
    case LT{}:
      G
    case EQ{}:
      Unit
    case GT{}:
      Unit

def lo.WhenEq(c: Cmp, G: Type) -> Type:
  match c:
    case LT{}:
      Unit
    case EQ{}:
      G
    case GT{}:
      Unit

def lo.WhenGt(c: Cmp, G: Type) -> Type:
  match c:
    case LT{}:
      Unit
    case EQ{}:
      Unit
    case GT{}:
      G

def lo.eq_lt(-G: Type, e: {EQ{} == LT{} : Cmp}) -> G:
  %e : lo.WhenLt(_, G)
  Unit{}

def lo.gt_lt(-G: Type, e: {GT{} == LT{} : Cmp}) -> G:
  %e : lo.WhenLt(_, G)
  Unit{}

def lo.lt_eq(-G: Type, e: {LT{} == EQ{} : Cmp}) -> G:
  %e : lo.WhenEq(_, G)
  Unit{}

def lo.gt_eq(-G: Type, e: {GT{} == EQ{} : Cmp}) -> G:
  %e : lo.WhenEq(_, G)
  Unit{}

def lo.lt_gt(-G: Type, e: {LT{} == GT{} : Cmp}) -> G:
  %e : lo.WhenGt(_, G)
  Unit{}

def lo.eq_gt(-G: Type, e: {EQ{} == GT{} : Cmp}) -> G:
  %e : lo.WhenGt(_, G)
  Unit{}

# Nat.cmp
# -------

def lo.nrefl(x: Nat) -> {Nat.cmp(x, x) == EQ{} : Cmp}:
  match x:
    case 0n:
      {==}
    case 1n+p:
      lo.nrefl(p)

def lo.nflip(x: Nat, y: Nat) -> {lo.flip(Nat.cmp(x, y)) == Nat.cmp(y, x) : Cmp}:
  match x y:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      lo.nflip(p, q)

def lo.neq(x: Nat, y: Nat, e: {Nat.cmp(x, y) == EQ{} : Cmp}) -> {x == y : Nat}:
  match x y:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      lo.lt_eq({0n == 1n+q : Nat}, e)
    case 1n+p 0n:
      lo.gt_eq({1n+p == 0n : Nat}, e)
    case 1n+p 1n+q:
      Equal.cong(Nat, Nat, n => 1n+n, p, q, lo.neq(p, q, e))

def lo.nlt(x: Nat, y: Nat, z: Nat, e1: {Nat.cmp(x, y) == LT{} : Cmp}, e2: {Nat.cmp(y, z) == LT{} : Cmp}) -> {Nat.cmp(x, z) == LT{} : Cmp}:
  match x y z:
    case 0n 0n _:
      lo.eq_lt({Nat.cmp(0n, z) == LT{} : Cmp}, e1)
    case 0n 1n+q 0n:
      lo.gt_lt({Nat.cmp(0n, 0n) == LT{} : Cmp}, e2)
    case 0n 1n+q 1n+r:
      {==}
    case 1n+p 0n _:
      lo.gt_lt({Nat.cmp(1n+p, z) == LT{} : Cmp}, e1)
    case 1n+p 1n+q 0n:
      lo.gt_lt({Nat.cmp(1n+p, 0n) == LT{} : Cmp}, e2)
    case 1n+p 1n+q 1n+r:
      lo.nlt(p, q, r, e1, e2)

# Nat lists
# ---------

def lo.pick(c: Cmp, r: Cmp) -> Cmp:
  match c:
    case LT{}:
      LT{}
    case EQ{}:
      r
    case GT{}:
      GT{}

# two Nat lists, item by item, a prefix first
def lo.lcmp(a: List<&2, Nat>, b: List<&2, Nat>) -> Cmp:
  match a b:
    case Nil{} Nil{}:
      EQ{}
    case Nil{} Con{y, v}:
      LT{}
    case Con{x, u} Nil{}:
      GT{}
    case Con{x, u} Con{y, v}:
      lo.pick(Nat.cmp(x, y), lo.lcmp(u, v))

def lo.lrefl(a: List<&2, Nat>) -> {lo.lcmp(a, a) == EQ{} : Cmp}:
  match a:
    case Nil{}:
      {==}
    case Con{+x, u}:
      %Equal.sym(Cmp, Nat.cmp(x, x), EQ{}, lo.nrefl(x)) : {lo.pick(_, lo.lcmp(u, u)) == EQ{} : Cmp}
      lo.lrefl(u)

def lo.pick_flip(c: Cmp, r: Cmp) -> {lo.pick(lo.flip(c), lo.flip(r)) == lo.flip(lo.pick(c, r)) : Cmp}:
  match c:
    case LT{}:
      {==}
    case EQ{}:
      {==}
    case GT{}:
      {==}

def lo.lflip(a: List<&2, Nat>, b: List<&2, Nat>) -> {lo.flip(lo.lcmp(a, b)) == lo.lcmp(b, a) : Cmp}:
  match a b:
    case Nil{} Nil{}:
      {==}
    case Nil{} Con{y, v}:
      {==}
    case Con{x, u} Nil{}:
      {==}
    case Con{+x, +u} Con{+y, +v}:
      %lo.nflip(x, y) : {lo.flip(lo.pick(Nat.cmp(x, y), lo.lcmp(u, v))) == lo.pick(_, lo.lcmp(v, u)) : Cmp}
      %lo.lflip(u, v) : {lo.flip(lo.pick(Nat.cmp(x, y), lo.lcmp(u, v))) == lo.pick(lo.flip(Nat.cmp(x, y)), _) : Cmp}
      Equal.sym(Cmp, lo.pick(lo.flip(Nat.cmp(x, y)), lo.flip(lo.lcmp(u, v))), lo.flip(lo.pick(Nat.cmp(x, y), lo.lcmp(u, v))), lo.pick_flip(Nat.cmp(x, y), lo.lcmp(u, v)))

def lo.leq.at(c: Cmp, +x: Nat, +y: Nat, -u: List<&2, Nat>, -v: List<&2, Nat>, ec: {Nat.cmp(x, y) == c : Cmp}, e: {lo.pick(c, lo.lcmp(u, v)) == EQ{} : Cmp},
  ih: {lo.lcmp(u, v) == EQ{} : Cmp} -> {u == v : List<&2, Nat>}) -> {Con{x, u} == Con{y, v} : List<&2, Nat>}:
  match c:
    case LT{}:
      lo.lt_eq({Con{x, u} == Con{y, v} : List<&2, Nat>}, e)
    case EQ{}:
      +exy = lo.neq(x, y, ec)
      %ih(e) : {Con{x, u} == Con{y, _} : List<&2, Nat>}
      Equal.cong(Nat, List<&2, Nat>, n => Con{n, u}, x, y, exy)
    case GT{}:
      lo.gt_eq({Con{x, u} == Con{y, v} : List<&2, Nat>}, e)

# lists that compare EQ are equal
def lo.leq(a: List<&2, Nat>, b: List<&2, Nat>, e: {lo.lcmp(a, b) == EQ{} : Cmp}) -> {a == b : List<&2, Nat>}:
  match a b:
    case Nil{} Nil{}:
      {==}
    case Nil{} Con{y, v}:
      lo.lt_eq({Nil{} == Con{y, v} : List<&2, Nat>}, e)
    case Con{x, u} Nil{}:
      lo.gt_eq({Con{x, u} == Nil{} : List<&2, Nat>}, e)
    case Con{+x, +u} Con{+y, +v}:
      lo.leq.at(Nat.cmp(x, y), x, y, u, v, {==}, e, h => lo.leq(u, v, h))

def lo.pick_lt(-c: Cmp, -r: Cmp, e: {c == LT{} : Cmp}) -> {lo.pick(c, r) == LT{} : Cmp}:
  %Equal.sym(Cmp, c, LT{}, e) : {lo.pick(_, r) == LT{} : Cmp}
  {==}

def lo.llt.at(c1: Cmp, c2: Cmp, +x: Nat, +y: Nat, +z: Nat, -u: List<&2, Nat>, -v: List<&2, Nat>, -w: List<&2, Nat>,
  ec1: {Nat.cmp(x, y) == c1 : Cmp}, ec2: {Nat.cmp(y, z) == c2 : Cmp},
  e1: {lo.pick(c1, lo.lcmp(u, v)) == LT{} : Cmp}, e2: {lo.pick(c2, lo.lcmp(v, w)) == LT{} : Cmp},
  ih: {lo.lcmp(u, v) == LT{} : Cmp} -> {lo.lcmp(v, w) == LT{} : Cmp} -> {lo.lcmp(u, w) == LT{} : Cmp}) ->
  {lo.pick(Nat.cmp(x, z), lo.lcmp(u, w)) == LT{} : Cmp}:
  match c1 c2:
    case LT{} LT{}:
      lo.pick_lt(Nat.cmp(x, z), lo.lcmp(u, w), lo.nlt(x, y, z, ec1, ec2))
    case LT{} EQ{}:
      +exz = {(%lo.neq(y, z, ec2) : {Nat.cmp(x, _) == LT{} : Cmp}
        ec1) : {Nat.cmp(x, z) == LT{} : Cmp}}
      lo.pick_lt(Nat.cmp(x, z), lo.lcmp(u, w), exz)
    case LT{} GT{}:
      lo.gt_lt({lo.pick(Nat.cmp(x, z), lo.lcmp(u, w)) == LT{} : Cmp}, e2)
    case EQ{} LT{}:
      +exz = {(%Equal.sym(Nat, x, y, lo.neq(x, y, ec1)) : {Nat.cmp(_, z) == LT{} : Cmp}
        ec2) : {Nat.cmp(x, z) == LT{} : Cmp}}
      lo.pick_lt(Nat.cmp(x, z), lo.lcmp(u, w), exz)
    case EQ{} EQ{}:
      +exz = {(%Equal.sym(Nat, x, y, lo.neq(x, y, ec1)) : {Nat.cmp(_, z) == EQ{} : Cmp}
        ec2) : {Nat.cmp(x, z) == EQ{} : Cmp}}
      %Equal.sym(Cmp, Nat.cmp(x, z), EQ{}, exz) : {lo.pick(_, lo.lcmp(u, w)) == LT{} : Cmp}
      ih(e1, e2)
    case EQ{} GT{}:
      lo.gt_lt({lo.pick(Nat.cmp(x, z), lo.lcmp(u, w)) == LT{} : Cmp}, e2)
    case GT{} _:
      lo.gt_lt({lo.pick(Nat.cmp(x, z), lo.lcmp(u, w)) == LT{} : Cmp}, e1)

# LT on lists is transitive
def lo.llt(a: List<&2, Nat>, b: List<&2, Nat>, c: List<&2, Nat>, e1: {lo.lcmp(a, b) == LT{} : Cmp}, e2: {lo.lcmp(b, c) == LT{} : Cmp}) -> {lo.lcmp(a, c) == LT{} : Cmp}:
  match a b c:
    case Nil{} Nil{} _:
      lo.eq_lt({lo.lcmp(Nil{}, c) == LT{} : Cmp}, e1)
    case Nil{} Con{y, v} Nil{}:
      lo.gt_lt({lo.lcmp(Nil{}, Nil{}) == LT{} : Cmp}, e2)
    case Nil{} Con{y, v} Con{z, w}:
      {==}
    case Con{x, u} Nil{} _:
      lo.gt_lt({lo.lcmp(Con{x, u}, c) == LT{} : Cmp}, e1)
    case Con{x, u} Con{y, v} Nil{}:
      lo.gt_lt({lo.lcmp(Con{x, u}, Nil{}) == LT{} : Cmp}, e2)
    case Con{+x, +u} Con{+y, +v} Con{+z, +w}:
      lo.llt.at(Nat.cmp(x, y), Nat.cmp(y, z), x, y, z, u, v, w, {==}, {==}, e1, e2, h1 => h2 => lo.llt(u, v, w, h1, h2))

# The code's and the spec's list order are lcmp's LT, equality its EQ
def lo.lex.at(c: Cmp, -u: List<&2, Nat>, -v: List<&2, Nat>, ih: {Ls.lex(u, v) == Cmp.is_lt(lo.lcmp(u, v)) : Bool}) -> {Bool.or(Cmp.is_lt(c), Bool.and(Cmp.is_eq(c), Ls.lex(u, v))) == Cmp.is_lt(lo.pick(c, lo.lcmp(u, v))) : Bool}:
  match c:
    case LT{}:
      {==}
    case EQ{}:
      ih
    case GT{}:
      {==}

def lo.lex(a: List<&2, Nat>, b: List<&2, Nat>) -> {Ls.lex(a, b) == Cmp.is_lt(lo.lcmp(a, b)) : Bool}:
  match a b:
    case Nil{} Nil{}:
      {==}
    case Nil{} Con{y, v}:
      {==}
    case Con{x, u} Nil{}:
      {==}
    case Con{+x, +u} Con{+y, +v}:
      lo.lex.at(Nat.cmp(x, y), u, v, lo.lex(u, v))

def lo.splex.at(c: Cmp, -u: List<&2, Nat>, -v: List<&2, Nat>, ih: {Listing.sp_lex(u, v) == Cmp.is_lt(lo.lcmp(u, v)) : Bool}) -> {Bool.or(Cmp.is_lt(c), Bool.and(Cmp.is_eq(c), Listing.sp_lex(u, v))) == Cmp.is_lt(lo.pick(c, lo.lcmp(u, v))) : Bool}:
  match c:
    case LT{}:
      {==}
    case EQ{}:
      ih
    case GT{}:
      {==}

def lo.splex(a: List<&2, Nat>, b: List<&2, Nat>) -> {Listing.sp_lex(a, b) == Cmp.is_lt(lo.lcmp(a, b)) : Bool}:
  match a b:
    case Nil{} Nil{}:
      {==}
    case Nil{} Con{y, v}:
      {==}
    case Con{x, u} Nil{}:
      {==}
    case Con{+x, +u} Con{+y, +v}:
      lo.splex.at(Nat.cmp(x, y), u, v, lo.splex(u, v))

def lo.same.at(c: Cmp, -u: List<&2, Nat>, -v: List<&2, Nat>, ih: {Listing.sp_same_nats(u, v) == Cmp.is_eq(lo.lcmp(u, v)) : Bool}) -> {Bool.and(Cmp.is_eq(c), Listing.sp_same_nats(u, v)) == Cmp.is_eq(lo.pick(c, lo.lcmp(u, v))) : Bool}:
  match c:
    case LT{}:
      {==}
    case EQ{}:
      ih
    case GT{}:
      {==}

def lo.same(a: List<&2, Nat>, b: List<&2, Nat>) -> {Listing.sp_same_nats(a, b) == Cmp.is_eq(lo.lcmp(a, b)) : Bool}:
  match a b:
    case Nil{} Nil{}:
      {==}
    case Nil{} Con{y, v}:
      {==}
    case Con{x, u} Nil{}:
      {==}
    case Con{+x, +u} Con{+y, +v}:
      lo.same.at(Nat.cmp(x, y), u, v, lo.same(u, v))

def lo.codes(s: String) -> {Listing.sp_codes(s) == Ls.codes(s) : List<&2, Nat>}:
  match s:
    case SNil{}:
      {==}
    case SCon{c, t}:
      match c:
        case Chr{x}:
          %lo.codes(t) : {U32.to_nat(x) <> Listing.sp_codes(t) == U32.to_nat(x) <> _ : List<&2, Nat>}
          {==}

def lo.id(p: Ls.Pick) -> {Listing.sp_id(p) == Ls.Pick.id(p) : String}:
  match p:
    case Ls.PSkip{}:
      {==}
    case Ls.PStore{s}:
      {==}
    case Ls.PLegacy{s}:
      {==}

# The order of rows
# -----------------

def lo.F2(c2: Cmp, c3: Cmp) -> Bool:
  match c2:
    case LT{}:
      True{}
    case EQ{}:
      Cmp.is_lt(c3)
    case GT{}:
      False{}

# before, from the compares of the times (c1), the ids (c2), the places
# (c3): a newer time first, then a smaller id, then a smaller place
def lo.F(c1: Cmp, c2: Cmp, c3: Cmp) -> Bool:
  match c1:
    case LT{}:
      False{}
    case EQ{}:
      lo.F2(c2, c3)
    case GT{}:
      True{}

def lo.kid(p: Ls.Pick) -> List<&2, Nat>:
  Ls.codes(Ls.Pick.id(p))

def lo.Fr(a: Ls.Row, b: Ls.Row) -> Bool:
  match a b:
    case Ls.Row{ia, pa, ta} Ls.Row{ib, pb, tb}:
      lo.F(lo.lcmp(Ls.tkey(ta), Ls.tkey(tb)), lo.lcmp(lo.kid(pa), lo.kid(pb)), Nat.cmp(ia, ib))

def lo.bid(c2: Cmp, ia: Nat, ib: Nat) -> {Ls.before.id(Cmp.is_lt(c2), Cmp.is_lt(lo.flip(c2)), ia, ib) == lo.F2(c2, Nat.cmp(ia, ib)) : Bool}:
  match c2:
    case LT{}:
      {==}
    case EQ{}:
      {==}
    case GT{}:
      {==}

def lo.bgo(c1: Cmp, +pa: Ls.Pick, +pb: Ls.Pick, +ia: Nat, +ib: Nat) -> {Ls.before.go(Cmp.is_lt(lo.flip(c1)), Cmp.is_lt(c1), pa, pb, ia, ib) == lo.F(c1, lo.lcmp(lo.kid(pa), lo.kid(pb)), Nat.cmp(ia, ib)) : Bool}:
  match c1:
    case LT{}:
      {==}
    case EQ{}:
      +ka = lo.kid(pa)
      +kb = lo.kid(pb)
      %Equal.sym(Bool, Ls.lex(ka, kb), Cmp.is_lt(lo.lcmp(ka, kb)), lo.lex(ka, kb)) : {Ls.before.id(_, Ls.lex(kb, ka), ia, ib) == lo.F2(lo.lcmp(ka, kb), Nat.cmp(ia, ib)) : Bool}
      %Equal.sym(Bool, Ls.lex(kb, ka), Cmp.is_lt(lo.lcmp(kb, ka)), lo.lex(kb, ka)) : {Ls.before.id(Cmp.is_lt(lo.lcmp(ka, kb)), _, ia, ib) == lo.F2(lo.lcmp(ka, kb), Nat.cmp(ia, ib)) : Bool}
      %lo.lflip(ka, kb) : {Ls.before.id(Cmp.is_lt(lo.lcmp(ka, kb)), Cmp.is_lt(_), ia, ib) == lo.F2(lo.lcmp(ka, kb), Nat.cmp(ia, ib)) : Bool}
      lo.bid(lo.lcmp(ka, kb), ia, ib)
    case GT{}:
      {==}

# the code's order is lo.Fr
def lo.before_code(a: Ls.Row, b: Ls.Row) -> {Ls.before(a, b) == lo.Fr(a, b) : Bool}:
  match a b:
    case Ls.Row{+ia, +pa, ta} Ls.Row{+ib, +pb, tb}:
      +ka = Ls.tkey(ta)
      +kb = Ls.tkey(tb)
      %Equal.sym(Bool, Ls.lex(kb, ka), Cmp.is_lt(lo.lcmp(kb, ka)), lo.lex(kb, ka)) : {Ls.before.go(_, Ls.lex(ka, kb), pa, pb, ia, ib) == lo.F(lo.lcmp(ka, kb), lo.lcmp(lo.kid(pa), lo.kid(pb)), Nat.cmp(ia, ib)) : Bool}
      %lo.lflip(ka, kb) : {Ls.before.go(Cmp.is_lt(_), Ls.lex(ka, kb), pa, pb, ia, ib) == lo.F(lo.lcmp(ka, kb), lo.lcmp(lo.kid(pa), lo.kid(pb)), Nat.cmp(ia, ib)) : Bool}
      %Equal.sym(Bool, Ls.lex(ka, kb), Cmp.is_lt(lo.lcmp(ka, kb)), lo.lex(ka, kb)) : {Ls.before.go(Cmp.is_lt(lo.flip(lo.lcmp(ka, kb))), _, pa, pb, ia, ib) == lo.F(lo.lcmp(ka, kb), lo.lcmp(lo.kid(pa), lo.kid(pb)), Nat.cmp(ia, ib)) : Bool}
      lo.bgo(lo.lcmp(ka, kb), pa, pb, ia, ib)

def lo.sF2(c2: Cmp, c3: Cmp) -> {Bool.or(Cmp.is_lt(c2), Bool.and(Cmp.is_eq(c2), Cmp.is_lt(c3))) == lo.F2(c2, c3) : Bool}:
  match c2:
    case LT{}:
      {==}
    case EQ{}:
      {==}
    case GT{}:
      {==}

def lo.sF(c1: Cmp, c2: Cmp, c3: Cmp) -> {Bool.or(Cmp.is_lt(lo.flip(c1)), Bool.and(Cmp.is_eq(c1), Bool.or(Cmp.is_lt(c2), Bool.and(Cmp.is_eq(c2), Cmp.is_lt(c3))))) == lo.F(c1, c2, c3) : Bool}:
  match c1:
    case LT{}:
      {==}
    case EQ{}:
      lo.sF2(c2, c3)
    case GT{}:
      {==}

def lo.sgen(+A: List<&2, Nat>, +B: List<&2, Nat>, +KA: List<&2, Nat>, +KB: List<&2, Nat>, +ia: Nat, +ib: Nat) ->
  {Bool.or(Listing.sp_lex(B, A), Bool.and(Listing.sp_same_nats(A, B), Bool.or(Listing.sp_lex(KA, KB), Bool.and(Listing.sp_same_nats(KA, KB), Nat.is_lt(ia, ib))))) == lo.F(lo.lcmp(A, B), lo.lcmp(KA, KB), Nat.cmp(ia, ib)) : Bool}:
  %Equal.sym(Bool, Listing.sp_lex(B, A), Cmp.is_lt(lo.lcmp(B, A)), lo.splex(B, A)) : {Bool.or(_, Bool.and(Listing.sp_same_nats(A, B), Bool.or(Listing.sp_lex(KA, KB), Bool.and(Listing.sp_same_nats(KA, KB), Nat.is_lt(ia, ib))))) == lo.F(lo.lcmp(A, B), lo.lcmp(KA, KB), Nat.cmp(ia, ib)) : Bool}
  %lo.lflip(A, B) : {Bool.or(Cmp.is_lt(_), Bool.and(Listing.sp_same_nats(A, B), Bool.or(Listing.sp_lex(KA, KB), Bool.and(Listing.sp_same_nats(KA, KB), Nat.is_lt(ia, ib))))) == lo.F(lo.lcmp(A, B), lo.lcmp(KA, KB), Nat.cmp(ia, ib)) : Bool}
  %Equal.sym(Bool, Listing.sp_same_nats(A, B), Cmp.is_eq(lo.lcmp(A, B)), lo.same(A, B)) : {Bool.or(Cmp.is_lt(lo.flip(lo.lcmp(A, B))), Bool.and(_, Bool.or(Listing.sp_lex(KA, KB), Bool.and(Listing.sp_same_nats(KA, KB), Nat.is_lt(ia, ib))))) == lo.F(lo.lcmp(A, B), lo.lcmp(KA, KB), Nat.cmp(ia, ib)) : Bool}
  %Equal.sym(Bool, Listing.sp_lex(KA, KB), Cmp.is_lt(lo.lcmp(KA, KB)), lo.splex(KA, KB)) : {Bool.or(Cmp.is_lt(lo.flip(lo.lcmp(A, B))), Bool.and(Cmp.is_eq(lo.lcmp(A, B)), Bool.or(_, Bool.and(Listing.sp_same_nats(KA, KB), Nat.is_lt(ia, ib))))) == lo.F(lo.lcmp(A, B), lo.lcmp(KA, KB), Nat.cmp(ia, ib)) : Bool}
  %Equal.sym(Bool, Listing.sp_same_nats(KA, KB), Cmp.is_eq(lo.lcmp(KA, KB)), lo.same(KA, KB)) : {Bool.or(Cmp.is_lt(lo.flip(lo.lcmp(A, B))), Bool.and(Cmp.is_eq(lo.lcmp(A, B)), Bool.or(Cmp.is_lt(lo.lcmp(KA, KB)), Bool.and(_, Nat.is_lt(ia, ib))))) == lo.F(lo.lcmp(A, B), lo.lcmp(KA, KB), Nat.cmp(ia, ib)) : Bool}
  lo.sF(lo.lcmp(A, B), lo.lcmp(KA, KB), Nat.cmp(ia, ib))

def lo.kid_spec(p: Ls.Pick) -> {Listing.sp_codes(Listing.sp_id(p)) == lo.kid(p) : List<&2, Nat>}:
  match p:
    case Ls.PSkip{}:
      {==}
    case Ls.PStore{s}:
      lo.codes(s)
    case Ls.PLegacy{s}:
      lo.codes(s)

# the spec's order is lo.Fr
def lo.before_spec(a: Ls.Row, b: Ls.Row) -> {Listing.sp_before(a, b) == lo.Fr(a, b) : Bool}:
  match a b:
    case Ls.Row{+ia, +pa, Sg.Time{+sa, +na}} Ls.Row{+ib, +pb, Sg.Time{+sb, +nb}}:
          %lo.kid_spec(pa) : {Listing.sp_before(Ls.Row{ia, pa, Sg.Time{sa, na}}, Ls.Row{ib, pb, Sg.Time{sb, nb}}) == lo.F(lo.lcmp([sa, na], [sb, nb]), lo.lcmp(_, lo.kid(pb)), Nat.cmp(ia, ib)) : Bool}
          %lo.kid_spec(pb) : {Listing.sp_before(Ls.Row{ia, pa, Sg.Time{sa, na}}, Ls.Row{ib, pb, Sg.Time{sb, nb}}) == lo.F(lo.lcmp([sa, na], [sb, nb]), lo.lcmp(Listing.sp_codes(Listing.sp_id(pa)), _), Nat.cmp(ia, ib)) : Bool}
          lo.sgen([sa, na], [sb, nb], Listing.sp_codes(Listing.sp_id(pa)), Listing.sp_codes(Listing.sp_id(pb)), ia, ib)

# The order is strict
# -------------------

def lo.F2_asym(c2: Cmp, c3: Cmp) -> {Bool.and(lo.F2(c2, c3), lo.F2(lo.flip(c2), lo.flip(c3))) == False{} : Bool}:
  match c2:
    case LT{}:
      {==}
    case EQ{}:
      match c3:
        case LT{}:
          {==}
        case EQ{}:
          {==}
        case GT{}:
          {==}
    case GT{}:
      {==}

def lo.F_asym(c1: Cmp, c2: Cmp, c3: Cmp) -> {Bool.and(lo.F(c1, c2, c3), lo.F(lo.flip(c1), lo.flip(c2), lo.flip(c3))) == False{} : Bool}:
  match c1:
    case LT{}:
      {==}
    case EQ{}:
      lo.F2_asym(c2, c3)
    case GT{}:
      {==}

def lo.F2_total(c2: Cmp, c3: Cmp, n: {c3 == EQ{} : Cmp} -> Empty) -> {Bool.or(lo.F2(c2, c3), lo.F2(lo.flip(c2), lo.flip(c3))) == True{} : Bool}:
  match c2:
    case LT{}:
      {==}
    case EQ{}:
      match c3:
        case LT{}:
          {==}
        case EQ{}:
          Empty.absurd({Bool.or(lo.F2(EQ{}, EQ{}), lo.F2(EQ{}, EQ{})) == True{} : Bool}, n({==}))
        case GT{}:
          {==}
    case GT{}:
      {==}

def lo.F_total(c1: Cmp, c2: Cmp, c3: Cmp, n: {c3 == EQ{} : Cmp} -> Empty) -> {Bool.or(lo.F(c1, c2, c3), lo.F(lo.flip(c1), lo.flip(c2), lo.flip(c3))) == True{} : Bool}:
  match c1:
    case LT{}:
      {==}
    case EQ{}:
      lo.F2_total(c2, c3, n)
    case GT{}:
      {==}

# b before a, read the other way: each compare flipped
def lo.Fr_flip(+ia: Nat, +pa: Ls.Pick, +ta: Sg.Time, +ib: Nat, +pb: Ls.Pick, +tb: Sg.Time) -> {lo.F(lo.flip(lo.lcmp(Ls.tkey(ta), Ls.tkey(tb))), lo.flip(lo.lcmp(lo.kid(pa), lo.kid(pb))), lo.flip(Nat.cmp(ia, ib))) == lo.Fr(Ls.Row{ib, pb, tb}, Ls.Row{ia, pa, ta}) : Bool}:
  %lo.lflip(Ls.tkey(ta), Ls.tkey(tb)) : {lo.F(lo.flip(lo.lcmp(Ls.tkey(ta), Ls.tkey(tb))), lo.flip(lo.lcmp(lo.kid(pa), lo.kid(pb))), lo.flip(Nat.cmp(ia, ib))) == lo.F(_, lo.lcmp(lo.kid(pb), lo.kid(pa)), Nat.cmp(ib, ia)) : Bool}
  %lo.lflip(lo.kid(pa), lo.kid(pb)) : {lo.F(lo.flip(lo.lcmp(Ls.tkey(ta), Ls.tkey(tb))), lo.flip(lo.lcmp(lo.kid(pa), lo.kid(pb))), lo.flip(Nat.cmp(ia, ib))) == lo.F(lo.flip(lo.lcmp(Ls.tkey(ta), Ls.tkey(tb))), _, Nat.cmp(ib, ia)) : Bool}
  %lo.nflip(ia, ib) : {lo.F(lo.flip(lo.lcmp(Ls.tkey(ta), Ls.tkey(tb))), lo.flip(lo.lcmp(lo.kid(pa), lo.kid(pb))), lo.flip(Nat.cmp(ia, ib))) == lo.F(lo.flip(lo.lcmp(Ls.tkey(ta), Ls.tkey(tb))), lo.flip(lo.lcmp(lo.kid(pa), lo.kid(pb))), _) : Bool}
  {==}

# never both ways
def lo.Fr_asym(a: Ls.Row, b: Ls.Row) -> {Bool.and(lo.Fr(a, b), lo.Fr(b, a)) == False{} : Bool}:
  match a b:
    case Ls.Row{+ia, +pa, +ta} Ls.Row{+ib, +pb, +tb}:
      %lo.Fr_flip(ia, pa, ta, ib, pb, tb) : {Bool.and(lo.Fr(Ls.Row{ia, pa, ta}, Ls.Row{ib, pb, tb}), _) == False{} : Bool}
      lo.F_asym(lo.lcmp(Ls.tkey(ta), Ls.tkey(tb)), lo.lcmp(lo.kid(pa), lo.kid(pb)), Nat.cmp(ia, ib))

def lo.at(r: Ls.Row) -> Nat:
  match r:
    case Ls.Row{i, p, t}:
      i

def lo.BT(b: Bool, G: Type) -> Type:
  match b:
    case True{}:
      Unit
    case False{}:
      G

def lo.tf(-G: Type, e: {True{} == False{} : Bool}) -> G:
  %e : lo.BT(_, G)
  Unit{}

def lo.ft(-G: Type, e: {False{} == True{} : Bool}) -> G:
  lo.tf(G, Equal.sym(Bool, False{}, True{}, e))

# places that are not equal do not compare EQ
def lo.ne_cmp(+x: Nat, +y: Nat, n: {Nat.is_eq(x, y) == False{} : Bool}, e: {Nat.cmp(x, y) == EQ{} : Cmp}) -> Empty:
  lo.tf(Empty, Equal.trans(Bool, True{}, Cmp.is_eq(Nat.cmp(x, y)), False{}, Equal.sym(Bool, Cmp.is_eq(Nat.cmp(x, y)), True{}, Equal.cong(Cmp, Bool, c => Cmp.is_eq(c), Nat.cmp(x, y), EQ{}, e)), n))

# one way, when the places differ
def lo.Fr_total(a: Ls.Row, b: Ls.Row, n: {Nat.is_eq(lo.at(a), lo.at(b)) == False{} : Bool}) -> {Bool.or(lo.Fr(a, b), lo.Fr(b, a)) == True{} : Bool}:
  match a b:
    case Ls.Row{+ia, +pa, +ta} Ls.Row{+ib, +pb, +tb}:
      %lo.Fr_flip(ia, pa, ta, ib, pb, tb) : {Bool.or(lo.Fr(Ls.Row{ia, pa, ta}, Ls.Row{ib, pb, tb}), _) == True{} : Bool}
      lo.F_total(lo.lcmp(Ls.tkey(ta), Ls.tkey(tb)), lo.lcmp(lo.kid(pa), lo.kid(pb)), Nat.cmp(ia, ib), e => lo.ne_cmp(ia, ib, n, e))

# The order is transitive
# -----------------------

# what the compares x (a with b) and y (b with c) say of z (a with c)
def lo.Rel(x: Cmp, y: Cmp, z: Cmp) -> Type:
  match x:
    case LT{}:
      match y:
        case LT{}:
          {z == LT{} : Cmp}
        case EQ{}:
          {z == LT{} : Cmp}
        case GT{}:
          Unit
    case EQ{}:
      {z == y : Cmp}
    case GT{}:
      match y:
        case LT{}:
          Unit
        case EQ{}:
          {z == GT{} : Cmp}
        case GT{}:
          {z == GT{} : Cmp}

def lo.flip_lt(-c: Cmp, -d: Cmp, ef: {lo.flip(c) == d : Cmp}, e: {c == GT{} : Cmp}) -> {d == LT{} : Cmp}:
  Equal.trans(Cmp, d, lo.flip(c), LT{}, Equal.sym(Cmp, lo.flip(c), d, ef), Equal.cong(Cmp, Cmp, x => lo.flip(x), c, GT{}, e))

def lo.nrel.at(c1: Cmp, c2: Cmp, +x: Nat, +y: Nat, +z: Nat, e1: {Nat.cmp(x, y) == c1 : Cmp}, e2: {Nat.cmp(y, z) == c2 : Cmp}) -> lo.Rel(c1, c2, Nat.cmp(x, z)):
  match c1:
    case LT{}:
      match c2:
        case LT{}:
          lo.nlt(x, y, z, e1, e2)
        case EQ{}:
          %lo.neq(y, z, e2) : {Nat.cmp(x, _) == LT{} : Cmp}
          e1
        case GT{}:
          Unit{}
    case EQ{}:
      %Equal.sym(Nat, x, y, lo.neq(x, y, e1)) : {Nat.cmp(_, z) == c2 : Cmp}
      e2
    case GT{}:
      match c2:
        case LT{}:
          Unit{}
        case EQ{}:
          %lo.neq(y, z, e2) : {Nat.cmp(x, _) == GT{} : Cmp}
          e1
        case GT{}:
          +zx = lo.nlt(z, y, x, lo.flip_lt(Nat.cmp(y, z), Nat.cmp(z, y), lo.nflip(y, z), e2), lo.flip_lt(Nat.cmp(x, y), Nat.cmp(y, x), lo.nflip(x, y), e1))
          %lo.nflip(z, x) : {_ == GT{} : Cmp}
          %Equal.sym(Cmp, Nat.cmp(z, x), LT{}, zx) : {lo.flip(_) == GT{} : Cmp}
          {==}

def lo.nrel(+x: Nat, +y: Nat, +z: Nat) -> lo.Rel(Nat.cmp(x, y), Nat.cmp(y, z), Nat.cmp(x, z)):
  lo.nrel.at(Nat.cmp(x, y), Nat.cmp(y, z), x, y, z, {==}, {==})

def lo.lrel.at(c1: Cmp, c2: Cmp, +a: List<&2, Nat>, +b: List<&2, Nat>, +c: List<&2, Nat>, e1: {lo.lcmp(a, b) == c1 : Cmp}, e2: {lo.lcmp(b, c) == c2 : Cmp}) -> lo.Rel(c1, c2, lo.lcmp(a, c)):
  match c1:
    case LT{}:
      match c2:
        case LT{}:
          lo.llt(a, b, c, e1, e2)
        case EQ{}:
          %lo.leq(b, c, e2) : {lo.lcmp(a, _) == LT{} : Cmp}
          e1
        case GT{}:
          Unit{}
    case EQ{}:
      %Equal.sym(List<&2, Nat>, a, b, lo.leq(a, b, e1)) : {lo.lcmp(_, c) == c2 : Cmp}
      e2
    case GT{}:
      match c2:
        case LT{}:
          Unit{}
        case EQ{}:
          %lo.leq(b, c, e2) : {lo.lcmp(a, _) == GT{} : Cmp}
          e1
        case GT{}:
          +ca = lo.llt(c, b, a, lo.flip_lt(lo.lcmp(b, c), lo.lcmp(c, b), lo.lflip(b, c), e2), lo.flip_lt(lo.lcmp(a, b), lo.lcmp(b, a), lo.lflip(a, b), e1))
          %lo.lflip(c, a) : {_ == GT{} : Cmp}
          %Equal.sym(Cmp, lo.lcmp(c, a), LT{}, ca) : {lo.flip(_) == GT{} : Cmp}
          {==}

def lo.lrel(+a: List<&2, Nat>, +b: List<&2, Nat>, +c: List<&2, Nat>) -> lo.Rel(lo.lcmp(a, b), lo.lcmp(b, c), lo.lcmp(a, c)):
  lo.lrel.at(lo.lcmp(a, b), lo.lcmp(b, c), a, b, c, {==}, {==})

def lo.F3_trans(x3: Cmp, y3: Cmp, -z3: Cmp, r3: lo.Rel(x3, y3, z3), hx: {Cmp.is_lt(x3) == True{} : Bool}, hy: {Cmp.is_lt(y3) == True{} : Bool}) -> {Cmp.is_lt(z3) == True{} : Bool}:
  match x3 y3:
    case LT{} LT{}:
      %Equal.sym(Cmp, z3, LT{}, r3) : {Cmp.is_lt(_) == True{} : Bool}
      {==}
    case LT{} EQ{}:
      lo.ft({Cmp.is_lt(z3) == True{} : Bool}, hy)
    case LT{} GT{}:
      lo.ft({Cmp.is_lt(z3) == True{} : Bool}, hy)
    case EQ{} _:
      lo.ft({Cmp.is_lt(z3) == True{} : Bool}, hx)
    case GT{} _:
      lo.ft({Cmp.is_lt(z3) == True{} : Bool}, hx)

def lo.F2_trans(x2: Cmp, y2: Cmp, +x3: Cmp, +y3: Cmp, -z2: Cmp, -z3: Cmp, r2: lo.Rel(x2, y2, z2), r3: lo.Rel(x3, y3, z3),
  hx: {lo.F2(x2, x3) == True{} : Bool}, hy: {lo.F2(y2, y3) == True{} : Bool}) -> {lo.F2(z2, z3) == True{} : Bool}:
  match x2 y2:
    case LT{} LT{}:
      %Equal.sym(Cmp, z2, LT{}, r2) : {lo.F2(_, z3) == True{} : Bool}
      {==}
    case LT{} EQ{}:
      %Equal.sym(Cmp, z2, LT{}, r2) : {lo.F2(_, z3) == True{} : Bool}
      {==}
    case LT{} GT{}:
      lo.ft({lo.F2(z2, z3) == True{} : Bool}, hy)
    case EQ{} LT{}:
      %Equal.sym(Cmp, z2, LT{}, r2) : {lo.F2(_, z3) == True{} : Bool}
      {==}
    case EQ{} EQ{}:
      %Equal.sym(Cmp, z2, EQ{}, r2) : {lo.F2(_, z3) == True{} : Bool}
      lo.F3_trans(x3, y3, z3, r3, hx, hy)
    case EQ{} GT{}:
      lo.ft({lo.F2(z2, z3) == True{} : Bool}, hy)
    case GT{} _:
      lo.ft({lo.F2(z2, z3) == True{} : Bool}, hx)

def lo.F_trans(x1: Cmp, y1: Cmp, +x2: Cmp, +y2: Cmp, +x3: Cmp, +y3: Cmp, -z1: Cmp, -z2: Cmp, -z3: Cmp,
  r1: lo.Rel(x1, y1, z1), r2: lo.Rel(x2, y2, z2), r3: lo.Rel(x3, y3, z3),
  hx: {lo.F(x1, x2, x3) == True{} : Bool}, hy: {lo.F(y1, y2, y3) == True{} : Bool}) -> {lo.F(z1, z2, z3) == True{} : Bool}:
  match x1 y1:
    case LT{} _:
      lo.ft({lo.F(z1, z2, z3) == True{} : Bool}, hx)
    case EQ{} LT{}:
      lo.ft({lo.F(z1, z2, z3) == True{} : Bool}, hy)
    case EQ{} EQ{}:
      %Equal.sym(Cmp, z1, EQ{}, r1) : {lo.F(_, z2, z3) == True{} : Bool}
      lo.F2_trans(x2, y2, x3, y3, z2, z3, r2, r3, hx, hy)
    case EQ{} GT{}:
      %Equal.sym(Cmp, z1, GT{}, r1) : {lo.F(_, z2, z3) == True{} : Bool}
      {==}
    case GT{} LT{}:
      lo.ft({lo.F(z1, z2, z3) == True{} : Bool}, hy)
    case GT{} EQ{}:
      %Equal.sym(Cmp, z1, GT{}, r1) : {lo.F(_, z2, z3) == True{} : Bool}
      {==}
    case GT{} GT{}:
      %Equal.sym(Cmp, z1, GT{}, r1) : {lo.F(_, z2, z3) == True{} : Bool}
      {==}

# before is transitive
def lo.Fr_trans(a: Ls.Row, b: Ls.Row, c: Ls.Row, hab: {lo.Fr(a, b) == True{} : Bool}, hbc: {lo.Fr(b, c) == True{} : Bool}) -> {lo.Fr(a, c) == True{} : Bool}:
  match a b c:
    case Ls.Row{+ia, +pa, +ta} Ls.Row{+ib, +pb, +tb} Ls.Row{+ic, +pc, +tc}:
      lo.F_trans(lo.lcmp(Ls.tkey(ta), Ls.tkey(tb)), lo.lcmp(Ls.tkey(tb), Ls.tkey(tc)), lo.lcmp(lo.kid(pa), lo.kid(pb)), lo.lcmp(lo.kid(pb), lo.kid(pc)), Nat.cmp(ia, ib), Nat.cmp(ib, ic),
        lo.lcmp(Ls.tkey(ta), Ls.tkey(tc)), lo.lcmp(lo.kid(pa), lo.kid(pc)), Nat.cmp(ia, ic),
        lo.lrel(Ls.tkey(ta), Ls.tkey(tb), Ls.tkey(tc)), lo.lrel(lo.kid(pa), lo.kid(pb), lo.kid(pc)), lo.nrel(ia, ib, ic), hab, hbc)
