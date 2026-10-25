# eukhe: lemmas shared by the proofs of area cache_marks: the code's
# budget walk (which counts the slots left down) is the spec's (which
# counts the wanted marks seen up), for every start count; the entry's
# encoders are the spec's spellings

import Base
import ../../bend/cache_marks.bend as Cm
import ../../bend/ffi_cache_marks.bend as FCm
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/cache_marks.bend as CacheMarks
import ../log/base.bend as LLog

# Logic
# -----

def cmb.IfF(b: Bool, G: Type) -> Type:
  match b:
    case True{}:
      G
    case False{}:
      Unit

def cmb.IfT(b: Bool, G: Type) -> Type:
  match b:
    case True{}:
      Unit
    case False{}:
      G

# a premise False == True proves anything
def cmb.absurd_ft(-G: Type, e: {False{} == True{} : Bool}) -> G:
  %e : cmb.IfF(_, G)
  Unit{}

# a premise True == False proves anything
def cmb.absurd_tf(-G: Type, e: {True{} == False{} : Bool}) -> G:
  %e : cmb.IfT(_, G)
  Unit{}

# Numbers
# -------

def cmb.add_zero(n: Nat) -> {Nat.add(n, 0n) == n : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      %Equal.sym(Nat, Nat.add(p, 0n), p, cmb.add_zero(p)) : {1n+_ == 1n+p : Nat}
      {==}

def cmb.add_succ(a: Nat, +b: Nat) -> {Nat.add(a, 1n+b) == 1n+Nat.add(a, b) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      %Equal.sym(Nat, Nat.add(p, 1n+b), 1n+Nat.add(p, b), cmb.add_succ(p, b)) : {1n+_ == 1n+1n+Nat.add(p, b) : Nat}
      {==}

def cmb.lt_succ(n: Nat) -> {Nat.is_lt(n, 1n+n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      cmb.lt_succ(p)

def cmb.lt_up(a: Nat, b: Nat, h: {Nat.is_lt(a, b) == True{} : Bool}) -> {Nat.is_lt(a, 1n+b) == True{} : Bool}:
  match a b:
    case 0n _:
      {==}
    case 1n+p 0n:
      cmb.absurd_ft({Nat.is_lt(1n+p, 1n) == True{} : Bool}, h)
    case 1n+p 1n+q:
      cmb.lt_up(p, q, h)

# k is below k + 1 + g
def cmb.lt_add(g: Nat, +k: Nat) -> {Nat.is_lt(k, 1n+Nat.add(g, k)) == True{} : Bool}:
  match g:
    case 0n:
      cmb.lt_succ(k)
    case 1n++h:
      cmb.lt_up(k, 1n+Nat.add(h, k), cmb.lt_add(h, k))

def cmb.irrefl(k: Nat) -> {Nat.is_lt(k, k) == False{} : Bool}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cmb.irrefl(p)

# not below n stays not below n one count later
def cmb.ge_up(k: Nat, n: Nat, h: {Nat.is_lt(k, n) == False{} : Bool}) -> {Nat.is_lt(1n+k, n) == False{} : Bool}:
  match k n:
    case _ 0n:
      {==}
    case 0n 1n+m:
      cmb.absurd_tf({Nat.is_lt(1n, 1n+m) == False{} : Bool}, h)
    case 1n+j 1n+m:
      cmb.ge_up(j, m, h)

# Budget
# ------

# with no slot left, no mark is granted
def cmb.none(ws: List<&2, Bool>, +k: Nat, +n: Nat, +h: {Nat.is_lt(k, n) == False{} : Bool}) -> {Cm.grant.go(ws, 0n) == CacheMarks.sp_grant.go(ws, k, n) : List<&2, Bool>}:
  match ws:
    case Nil{}:
      {==}
    case w <> +t:
      match w:
        case False{}:
          %Equal.sym(List<&2, Bool>, Cm.grant.go(t, 0n), CacheMarks.sp_grant.go(t, k, n), cmb.none(t, k, n, h)) : {False{} <> _ == False{} <> CacheMarks.sp_grant.go(t, k, n) : List<&2, Bool>}
          {==}
        case True{}:
          %Equal.sym(List<&2, Bool>, Cm.grant.go(t, 0n), CacheMarks.sp_grant.go(t, 1n+k, n), cmb.none(t, 1n+k, n, cmb.ge_up(k, n, h))) : {False{} <> _ == Nat.is_lt(k, n) <> CacheMarks.sp_grant.go(t, 1n+k, n) : List<&2, Bool>}
          %Equal.sym(Bool, Nat.is_lt(k, n), False{}, h) : {False{} <> CacheMarks.sp_grant.go(t, 1n+k, n) == _ <> CacheMarks.sp_grant.go(t, 1n+k, n) : List<&2, Bool>}
          {==}

# with f slots left after k wanted marks, the code walk is the spec's
def cmb.go(ws: List<&2, Bool>, +f: Nat, +k: Nat) -> {Cm.grant.go(ws, f) == CacheMarks.sp_grant.go(ws, k, Nat.add(f, k)) : List<&2, Bool>}:
  match ws:
    case Nil{}:
      {==}
    case w <> +t:
      match w:
        case False{}:
          %Equal.sym(List<&2, Bool>, Cm.grant.go(t, f), CacheMarks.sp_grant.go(t, k, Nat.add(f, k)), cmb.go(t, f, k)) : {False{} <> _ == False{} <> CacheMarks.sp_grant.go(t, k, Nat.add(f, k)) : List<&2, Bool>}
          {==}
        case True{}:
          match f:
            case 0n:
              %Equal.sym(List<&2, Bool>, Cm.grant.go(t, 0n), CacheMarks.sp_grant.go(t, 1n+k, k), cmb.none(t, 1n+k, k, cmb.ge_up(k, k, cmb.irrefl(k)))) : {False{} <> _ == Nat.is_lt(k, k) <> CacheMarks.sp_grant.go(t, 1n+k, k) : List<&2, Bool>}
              %Equal.sym(Bool, Nat.is_lt(k, k), False{}, cmb.irrefl(k)) : {False{} <> CacheMarks.sp_grant.go(t, 1n+k, k) == _ <> CacheMarks.sp_grant.go(t, 1n+k, k) : List<&2, Bool>}
              {==}
            case 1n+g:
              %Equal.sym(List<&2, Bool>, Cm.grant.go(t, g), CacheMarks.sp_grant.go(t, 1n+k, Nat.add(g, 1n+k)), cmb.go(t, g, 1n+k)) : {True{} <> _ == Nat.is_lt(k, 1n+Nat.add(g, k)) <> CacheMarks.sp_grant.go(t, 1n+k, 1n+Nat.add(g, k)) : List<&2, Bool>}
              %Equal.sym(Nat, Nat.add(g, 1n+k), 1n+Nat.add(g, k), cmb.add_succ(g, k)) : {True{} <> CacheMarks.sp_grant.go(t, 1n+k, _) == Nat.is_lt(k, 1n+Nat.add(g, k)) <> CacheMarks.sp_grant.go(t, 1n+k, 1n+Nat.add(g, k)) : List<&2, Bool>}
              %Equal.sym(Bool, Nat.is_lt(k, 1n+Nat.add(g, k)), True{}, cmb.lt_add(g, k)) : {True{} <> CacheMarks.sp_grant.go(t, 1n+k, 1n+Nat.add(g, k)) == _ <> CacheMarks.sp_grant.go(t, 1n+k, 1n+Nat.add(g, k)) : List<&2, Bool>}
              {==}

# Wire
# ----

# the log area's spelling of Bool items is the spec's
def cmb.bools(xs: List<&2, Bool>, rest: String) -> {LLog.pe.bools(xs, rest) == CacheMarks.sp_w_bools(xs, rest) : String}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +t:
      %Equal.sym(String, LLog.pe.bools(t, rest), CacheMarks.sp_w_bools(t, rest), cmb.bools(t, rest)) : {Wr.put_bool(x, _) == Wr.put_bool(x, CacheMarks.sp_w_bools(t, rest)) : String}
      {==}

# a list of Bools is spelled by the spec
def cmb.put_list(+xs: List<&2, Bool>, rest: String) -> {Wr.put_list(~Bool, ~Wr.put_bool, xs, rest) == Wr.put_nat(List.length(&2, Bool, xs), CacheMarks.sp_w_bools(xs, rest)) : String}:
  %cmb.bools(xs, rest) : {Wr.put_list(~Bool, ~Wr.put_bool, xs, rest) == Wr.put_nat(List.length(&2, Bool, xs), _) : String}
  LLog.pe.put_list(xs, rest)
