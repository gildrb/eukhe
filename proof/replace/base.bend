# eukhe: lemmas the proofs of area replace share

import Base
import ../../bend/replace.bend as Rp
import ../../laws/replace.bend as Replace
import ../base/bool/misc.bend as LBoolMisc

# x cannot be True and False
def pr.clash(-A: Type, -x: Bool, t: {x == True{} : Bool}, f: {x == False{} : Bool}) -> A:
  LBoolMisc.supervisor.ps.absurdF(A, Equal.trans(Bool, False{}, x, True{}, Equal.sym(Bool, x, False{}, f), t))

def pr.VD(v: Rp.Verdict, A: Type) -> Type:
  match v:
    case Rp.Replace{}:
      A
    case Rp.Keep{r}:
      Unit

def pr.not_replace(-A: Type, -v: Rp.Verdict, e: {v == Rp.Replace{} : Rp.Verdict}, u: pr.VD(v, A)) -> A:
  %e : pr.VD(_, A)
  u

def pr.RD(r: Rp.Rel, A: Type) -> Type:
  match r:
    case Rp.Same{}:
      Unit
    case Rp.Older{}:
      A
    case Rp.Newer{}:
      Unit
    case Rp.Other{}:
      Unit

def pr.not_older(-A: Type, -r: Rp.Rel, e: {r == Rp.Older{} : Rp.Rel}, u: pr.RD(r, A)) -> A:
  %e : pr.RD(_, A)
  u

# The order
# ---------

def pr.lex_same(x: Nat, -t: Bool) -> {Rp.lex(x, x, t) == t : Bool}:
  match x:
    case 0n:
      {==}
    case 1n+p:
      pr.lex_same(p, t)

def pr.lt_irrefl(xs: List<&2, Nat>) -> {Rp.lt(xs, xs) == False{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +xr:
      Equal.trans(Bool, Rp.lex(x, x, Rp.lt(xr, xr)), Rp.lt(xr, xr), False{}, pr.lex_same(x, Rp.lt(xr, xr)), pr.lt_irrefl(xr))

def pr.lex_trans(x: Nat, y: Nat, z: Nat, -t1: Bool, -t2: Bool, -t3: Bool, h1: {Rp.lex(x, y, t1) == True{} : Bool}, h2: {Rp.lex(y, z, t2) == True{} : Bool}, k: {t1 == True{} : Bool} -> {t2 == True{} : Bool} -> {t3 == True{} : Bool}) -> {Rp.lex(x, z, t3) == True{} : Bool}:
  match x y z:
    case 0n 0n 0n:
      k(h1, h2)
    case 0n 0n 1n+r:
      {==}
    case 0n 1n+q 0n:
      LBoolMisc.supervisor.ps.absurdF({Rp.lex(0n, 0n, t3) == True{} : Bool}, h2)
    case 0n 1n+q 1n+r:
      {==}
    case 1n+p 0n _:
      LBoolMisc.supervisor.ps.absurdF({Rp.lex(1n+p, z, t3) == True{} : Bool}, h1)
    case 1n+p 1n+q 0n:
      LBoolMisc.supervisor.ps.absurdF({Rp.lex(1n+p, 0n, t3) == True{} : Bool}, h2)
    case 1n+p 1n+q 1n+r:
      pr.lex_trans(p, q, r, t1, t2, t3, h1, h2, k)

def pr.lt_trans(xs: List<&2, Nat>, ys: List<&2, Nat>, zs: List<&2, Nat>, h1: {Rp.lt(xs, ys) == True{} : Bool}, h2: {Rp.lt(ys, zs) == True{} : Bool}) -> {Rp.lt(xs, zs) == True{} : Bool}:
  match xs ys zs:
    case Nil{} Nil{} _:
      LBoolMisc.supervisor.ps.absurdF({Rp.lt(Nil{}, zs) == True{} : Bool}, h1)
    case Nil{} y <> yr Nil{}:
      LBoolMisc.supervisor.ps.absurdF({Rp.lt(Nil{}, Nil{}) == True{} : Bool}, h2)
    case Nil{} y <> yr z <> zr:
      {==}
    case x <> xr Nil{} _:
      LBoolMisc.supervisor.ps.absurdF({Rp.lt(x <> xr, zs) == True{} : Bool}, h1)
    case x <> xr y <> yr Nil{}:
      LBoolMisc.supervisor.ps.absurdF({Rp.lt(x <> xr, Nil{}) == True{} : Bool}, h2)
    case x <> +xr y <> +yr z <> +zr:
      pr.lex_trans(x, y, z, Rp.lt(xr, yr), Rp.lt(yr, zr), Rp.lt(xr, zr), h1, h2, a => b => pr.lt_trans(xr, yr, zr, a, b))

# The verdict
# -----------

def pr.put_replace(r: Rp.Rel, -k: Rp.Caller, e: {Rp.verdict.put(r, k) == Rp.Replace{} : Rp.Verdict}) -> {r == Rp.Older{} : Rp.Rel}:
  match r:
    case Rp.Same{}:
      pr.not_replace({Rp.Same{} == Rp.Older{} : Rp.Rel}, Rp.Keep{Rp.Same{}}, e, Unit{})
    case Rp.Older{}:
      {==}
    case Rp.Newer{}:
      pr.not_replace({Rp.Newer{} == Rp.Older{} : Rp.Rel}, Rp.Keep{Rp.Newer{}}, e, Unit{})
    case Rp.Other{}:
      pr.not_replace({Rp.Other{} == Rp.Older{} : Rp.Rel}, Rp.Keep{Rp.Other{}}, e, Unit{})

def pr.rel_older(same: Bool, older: Bool, newer: Bool, e: {Rp.rel.put(same, older, newer) == Rp.Older{} : Rp.Rel}) -> {older == True{} : Bool}:
  match same:
    case True{}:
      pr.not_older({older == True{} : Bool}, Rp.Same{}, e, Unit{})
    case False{}:
      match older:
        case True{}:
          {==}
        case False{}:
          match newer:
            case True{}:
              pr.not_older({False{} == True{} : Bool}, Rp.Newer{}, e, Unit{})
            case False{}:
              pr.not_older({False{} == True{} : Bool}, Rp.Other{}, e, Unit{})

# a replacement moves the daemon b to a client c of a higher rank
def pr.replace_older(c: Rp.Build, b: Rp.Build, -k: Rp.Caller, e: {Rp.verdict(c, b, k) == Rp.Replace{} : Rp.Verdict}) -> {Rp.lt(Rp.Build.rank(b), Rp.Build.rank(c)) == True{} : Bool}:
  match c b:
    case Rp.Build{+rc, +ic} Rp.Build{+rb, +ib}:
      pr.rel_older(String.eq(ic, ib), Rp.lt(rb, rc), Rp.lt(rc, rb), pr.put_replace(Rp.rel.put(String.eq(ic, ib), Rp.lt(rb, rc), Rp.lt(rc, rb)), k, e))

# The order and the verdict, exactly
def rk.lex_cmp(c: Cmp, -t: Bool) -> {Rp.lex.put(c, t) == Bool.or(Cmp.is_lt(c), Bool.and(Cmp.is_eq(c), t)) : Bool}:
  match c:
    case LT{}:
      {==}
    case EQ{}:
      {==}
    case GT{}:
      {==}

def rk.lt_spec(xs: List<&2, Nat>, ys: List<&2, Nat>) -> {Rp.lt(xs, ys) == Replace.rank_below(xs, ys) : Bool}:
  match xs ys:
    case Nil{} Nil{}:
      {==}
    case Nil{} y <> yr:
      {==}
    case x <> xr Nil{}:
      {==}
    case +x <> +xr +y <> +yr:
      %rk.lt_spec(xr, yr) : {Rp.lex(x, y, Rp.lt(xr, yr)) == Bool.or(Nat.is_lt(x, y), Bool.and(Nat.is_eq(x, y), _)) : Bool}
      rk.lex_cmp(Nat.cmp(x, y), Rp.lt(xr, yr))

def rk.rel_pick(same: Bool, older: Bool, newer: Bool) -> {Rp.rel.put(same, older, newer) == Replace.rel_spec.pick(same, older, newer) : Rp.Rel}:
  match same older newer:
    case True{} _ _:
      {==}
    case False{} True{} _:
      {==}
    case False{} False{} True{}:
      {==}
    case False{} False{} False{}:
      {==}

def rk.relation_exact(+c: Rp.Build, +d: Rp.Build) -> {Rp.relation(c, d) == Replace.rel_spec(c, d) : Rp.Rel}:
  match c d:
    case Rp.Build{+rc, +ic} Rp.Build{+rd, +id}:
      %rk.lt_spec(rd, rc) : {Rp.rel.put(String.eq(ic, id), Rp.lt(rd, rc), Rp.lt(rc, rd)) == Replace.rel_spec.pick(String.eq(ic, id), _, Replace.rank_below(rc, rd)) : Rp.Rel}
      %rk.lt_spec(rc, rd) : {Rp.rel.put(String.eq(ic, id), Rp.lt(rd, rc), Rp.lt(rc, rd)) == Replace.rel_spec.pick(String.eq(ic, id), Rp.lt(rd, rc), _) : Rp.Rel}
      rk.rel_pick(String.eq(ic, id), Rp.lt(rd, rc), Rp.lt(rc, rd))
