# eukhe: lemmas of the aws_text proofs: R1 and R2 answer the first hit.
# partition.go and rid.index walk a list from an index i0 and answer the
# index of the first hit: what they answer is i0 plus the place of a hit
# (awf.go_found, awf.rid_found); a hit at place j makes them answer an
# index at most i0 plus j (awf.go_hit, awf.rid_least).

import Base
import ../../../bend/phrase.bend as P
import ../../../bend/aws_text.bend as A
import ../../../laws/aws_text.bend as AwsText
import ../../model_name/base.bend as LA

# Nat and Maybe facts
# -------------------

def awf.MS(m: Maybe<&2, Nat>, G: Type) -> Type:
  match m:
    case None{}:
      Unit
    case Some{x}:
      G

# None is not Some
def awf.none_some(-i: Nat, -G: Type, e: {None{} == Some{i} : Maybe<&2, Nat>}) -> G:
  %e : awf.MS(_, G)
  Unit{}

def awf.get(m: Maybe<&2, Nat>) -> Nat:
  match m:
    case None{}:
      0n
    case Some{x}:
      x

def awf.some_inj(-a: Nat, -b: Nat, e: {Some{a} == Some{b} : Maybe<&2, Nat>}) -> {a == b : Nat}:
  Equal.cong(Maybe<&2, Nat>, Nat, awf.get, Some{a}, Some{b}, e)

# a + 0 is a
def awf.add_zero(a: Nat) -> {Nat.add(a, 0n) == a : Nat}:
  match a:
    case 0n:
      {==}
    case 1n++x:
      Equal.cong(Nat, Nat, z => 1n+z, Nat.add(x, 0n), x, awf.add_zero(x))

# a + (1 + b) is 1 + (a + b)
def awf.add_succ(a: Nat, -b: Nat) -> {Nat.add(a, 1n+b) == 1n+Nat.add(a, b) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n++x:
      Equal.cong(Nat, Nat, z => 1n+z, Nat.add(x, 1n+b), 1n+Nat.add(x, b), awf.add_succ(x, b))

def awf.le_refl(a: Nat) -> {Nat.is_le(a, a) == True{} : Bool}:
  match a:
    case 0n:
      {==}
    case 1n+x:
      awf.le_refl(x)

# b <= c gives b <= 1 + c
def awf.le_succ(b: Nat, c: Nat, h: {Nat.is_le(b, c) == True{} : Bool}) -> {Nat.is_le(b, 1n+c) == True{} : Bool}:
  match b:
    case 0n:
      {==}
    case 1n+y:
      match c:
        case 0n:
          LA.mnb.absurd_f({Nat.is_le(1n+y, 1n) == True{} : Bool}, h)
        case 1n+z:
          awf.le_succ(y, z, h)

# b <= a + b
def awf.le_add(a: Nat, +b: Nat) -> {Nat.is_le(b, Nat.add(a, b)) == True{} : Bool}:
  match a:
    case 0n:
      awf.le_refl(b)
    case 1n++x:
      awf.le_succ(b, Nat.add(x, b), awf.le_add(x, b))

# i <= m + (1 + i0) gives i <= 1 + (m + i0)
def awf.le_shift(-i: Nat, m: Nat, -i0: Nat, le: {Nat.is_le(i, Nat.add(m, 1n+i0)) == True{} : Bool}) -> {Nat.is_le(i, 1n+Nat.add(m, i0)) == True{} : Bool}:
  %awf.add_succ(m, i0) : {Nat.is_le(i, _) == True{} : Bool}
  le

# m + (1 + i0) is i gives 1 + (m + i0) is i
def awf.eq_shift(+m: Nat, -i0: Nat, -i: Nat, e: {Nat.add(m, 1n+i0) == i : Nat}) -> {1n+Nat.add(m, i0) == i : Nat}:
  Equal.trans(Nat, 1n+Nat.add(m, i0), Nat.add(m, 1n+i0), i, Equal.sym(Nat, Nat.add(m, 1n+i0), 1n+Nat.add(m, i0), awf.add_succ(m, i0)), e)

# a pick on True answers its index
def awf.pick_t(b: Bool, -i: Nat, -f: Unit -> Maybe<&2, Nat>, e: {b == True{} : Bool}) -> {A.pick(b, i, f) == Some{i} : Maybe<&2, Nat>}:
  match b:
    case True{}:
      {==}
    case False{}:
      LA.mnb.absurd_f({A.pick(False{}, i, f) == Some{i} : Maybe<&2, Nat>}, e)

# a lazy `or` whose left side is True is True
def awf.or_t(b: Bool, -f: Unit -> Bool, e: {b == True{} : Bool}) -> {P.pm.or(b, f) == True{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      LA.mnb.absurd_f({P.pm.or(False{}, f) == True{} : Bool}, e)

# R2: the request-id header
# -------------------------

def awf.RF(names: List<&2, String>, i0: Nat, i: Nat) -> Type:
  Sigma<&1, &1, Nat, d => {AwsText.sp_rid_at(names, d) == True{} : Bool} & {Nat.add(d, i0) == i : Nat}>

def awf.rid_found_next(-n: String, -t: List<&2, String>, -i0: Nat, -i: Nat, s: awf.RF(t, 1n+i0, i)) -> awf.RF(n <> t, i0, i):
  (+d, (sr, e)) = s
  (1n+d, (sr, awf.eq_shift(d, i0, i, e)))

def awf.rid_found_at(+n: String, -t: List<&2, String>, +i0: Nat, +i: Nat, b: Bool, eb: {A.is_rid(n) == b : Bool}, h: {A.pick(b, i0, u => A.rid.index(t, 1n+i0)) == Some{i} : Maybe<&2, Nat>}, ih: {A.rid.index(t, 1n+i0) == Some{i} : Maybe<&2, Nat>} -> awf.RF(t, 1n+i0, i)) -> awf.RF(n <> t, i0, i):
  match b:
    case True{}:
      (0n, (eb, awf.some_inj(i0, i, h)))
    case False{}:
      awf.rid_found_next(n, t, i0, i, ih(h))

# what rid.index answers from i0 is i0 plus the place of a request-id
# header
def awf.rid_found(names: List<&2, String>, +i0: Nat, +i: Nat, h: {A.rid.index(names, i0) == Some{i} : Maybe<&2, Nat>}) -> awf.RF(names, i0, i):
  match names:
    case Nil{}:
      awf.none_some(i, awf.RF(Nil{}, i0, i), h)
    case +n <> +t:
      awf.rid_found_at(n, t, i0, i, A.is_rid(n), {==}, h, h2 => awf.rid_found(t, 1n+i0, i, h2))

def awf.RL(names: List<&2, String>, i0: Nat, k: Nat) -> Type:
  Sigma<&1, &1, Nat, i => {A.rid.index(names, i0) == Some{i} : Maybe<&2, Nat>} & {Nat.is_le(i, Nat.add(k, i0)) == True{} : Bool}>

def awf.rid_least_at(-t: List<&2, String>, +i0: Nat, +m: Nat, b: Bool, ih: awf.RL(t, 1n+i0, m)) -> Sigma<&1, &1, Nat, i => {A.pick(b, i0, u => A.rid.index(t, 1n+i0)) == Some{i} : Maybe<&2, Nat>} & {Nat.is_le(i, 1n+Nat.add(m, i0)) == True{} : Bool}>:
  match b:
    case True{}:
      (i0, ({==}, awf.le_add(1n+m, i0)))
    case False{}:
      (+i, (e, le)) = ih
      (i, (e, awf.le_shift(i, m, i0, le)))

# a request-id header at place k makes rid.index answer, from i0, at most
# i0 plus k
def awf.rid_least(names: List<&2, String>, k: Nat, +i0: Nat, hk: {AwsText.sp_rid_at(names, k) == True{} : Bool}) -> awf.RL(names, i0, k):
  match names:
    case Nil{}:
      LA.mnb.absurd_f(awf.RL(Nil{}, i0, k), hk)
    case +n <> +t:
      match k:
        case 0n:
          (i0, (awf.pick_t(A.is_rid(n), i0, u => A.rid.index(t, 1n+i0), hk), awf.le_refl(i0)))
        case 1n++m:
          awf.rid_least_at(t, i0, m, A.is_rid(n), awf.rid_least(t, m, 1n+i0, hk))

# R1: the partition
# -----------------

# the row j of the table (none past its end)
def awf.row(tab: List<&2, List<&2, String>>, j: Nat) -> List<&2, String>:
  match tab:
    case Nil{}:
      Nil{}
    case ps <> more:
      match j:
        case 0n:
          ps
        case 1n+m:
          awf.row(more, m)

# ps has a prefix at place n and r has its shape
def awf.at(ps: List<&2, String>, n: Nat, +r: String) -> Bool:
  match ps:
    case Nil{}:
      False{}
    case p <> t:
      match n:
        case 0n:
          A.shape(p, r)
        case 1n+m:
          awf.at(t, m, r)

# a prefix of ps whose shape r has makes shapes answer True
def awf.shapes_hit(ps: List<&2, String>, n: Nat, +r: String, h: {awf.at(ps, n, r) == True{} : Bool}) -> {A.shapes(ps, r) == True{} : Bool}:
  match ps:
    case Nil{}:
      LA.mnb.absurd_f({A.shapes(Nil{}, r) == True{} : Bool}, h)
    case +p <> +t:
      match n:
        case 0n:
          awf.or_t(A.shape(p, r), u => A.shapes(t, r), h)
        case 1n+m:
          LA.mnb.or_rl(A.shape(p, r), A.shapes(t, r), awf.shapes_hit(t, m, r, h))

def awf.SF(ps: List<&2, String>, r: String) -> Type:
  Sigma<&1, &1, Nat, n => {awf.at(ps, n, r) == True{} : Bool}>

def awf.shapes_found_next(-p: String, -t: List<&2, String>, -r: String, s: awf.SF(t, r)) -> awf.SF(p <> t, r):
  (+n, a) = s
  (1n+n, a)

def awf.shapes_found_at(+p: String, -t: List<&2, String>, +r: String, b: Bool, eb: {A.shape(p, r) == b : Bool}, h: {P.pm.or(b, u => A.shapes(t, r)) == True{} : Bool}, ih: {A.shapes(t, r) == True{} : Bool} -> awf.SF(t, r)) -> awf.SF(p <> t, r):
  match b:
    case True{}:
      (0n, eb)
    case False{}:
      awf.shapes_found_next(p, t, r, ih(h))

# shapes answers True only for a prefix of ps whose shape r has
def awf.shapes_found(ps: List<&2, String>, +r: String, h: {A.shapes(ps, r) == True{} : Bool}) -> awf.SF(ps, r):
  match ps:
    case Nil{}:
      LA.mnb.absurd_f(awf.SF(Nil{}, r), h)
    case +p <> +t:
      awf.shapes_found_at(p, t, r, A.shape(p, r), {==}, h, h2 => awf.shapes_found(t, r, h2))

def awf.GF(tab: List<&2, List<&2, String>>, r: String, i0: Nat, i: Nat) -> Type:
  Sigma<&1, &1, Nat, j => Sigma<&1, &1, Nat, n => {awf.at(awf.row(tab, j), n, r) == True{} : Bool} & {Nat.add(j, i0) == i : Nat}>>

def awf.go_found_here(-ps: List<&2, String>, -more: List<&2, List<&2, String>>, -r: String, -i0: Nat, -i: Nat, s: awf.SF(ps, r), e: {i0 == i : Nat}) -> awf.GF(ps <> more, r, i0, i):
  (+n, a) = s
  (0n, (n, (a, e)))

def awf.go_found_next(-ps: List<&2, String>, -more: List<&2, List<&2, String>>, -r: String, -i0: Nat, -i: Nat, s: awf.GF(more, r, 1n+i0, i)) -> awf.GF(ps <> more, r, i0, i):
  (+j, (+n, (a, e))) = s
  (1n+j, (n, (a, awf.eq_shift(j, i0, i, e))))

def awf.go_found_at(+ps: List<&2, String>, -more: List<&2, List<&2, String>>, +r: String, +i0: Nat, +i: Nat, b: Bool, eb: {A.shapes(ps, r) == b : Bool}, h: {A.pick(b, i0, u => A.partition.go(more, r, 1n+i0)) == Some{i} : Maybe<&2, Nat>}, ih: {A.partition.go(more, r, 1n+i0) == Some{i} : Maybe<&2, Nat>} -> awf.GF(more, r, 1n+i0, i)) -> awf.GF(ps <> more, r, i0, i):
  match b:
    case True{}:
      awf.go_found_here(ps, more, r, i0, i, awf.shapes_found(ps, r, eb), awf.some_inj(i0, i, h))
    case False{}:
      awf.go_found_next(ps, more, r, i0, i, ih(h))

# what partition.go answers from i0 is i0 plus the row of a prefix whose
# shape r has
def awf.go_found(tab: List<&2, List<&2, String>>, +r: String, +i0: Nat, +i: Nat, h: {A.partition.go(tab, r, i0) == Some{i} : Maybe<&2, Nat>}) -> awf.GF(tab, r, i0, i):
  match tab:
    case Nil{}:
      awf.none_some(i, awf.GF(Nil{}, r, i0, i), h)
    case +ps <> +more:
      awf.go_found_at(ps, more, r, i0, i, A.shapes(ps, r), {==}, h, h2 => awf.go_found(more, r, 1n+i0, i, h2))

def awf.GH(tab: List<&2, List<&2, String>>, r: String, i0: Nat, j: Nat) -> Type:
  Sigma<&1, &1, Nat, i => {A.partition.go(tab, r, i0) == Some{i} : Maybe<&2, Nat>} & {Nat.is_le(i, Nat.add(j, i0)) == True{} : Bool}>

def awf.go_hit_at(-more: List<&2, List<&2, String>>, -r: String, +i0: Nat, +m: Nat, b: Bool, ih: awf.GH(more, r, 1n+i0, m)) -> Sigma<&1, &1, Nat, i => {A.pick(b, i0, u => A.partition.go(more, r, 1n+i0)) == Some{i} : Maybe<&2, Nat>} & {Nat.is_le(i, 1n+Nat.add(m, i0)) == True{} : Bool}>:
  match b:
    case True{}:
      (i0, ({==}, awf.le_add(1n+m, i0)))
    case False{}:
      (+i, (e, le)) = ih
      (i, (e, awf.le_shift(i, m, i0, le)))

# a row j whose shapes r has makes partition.go answer, from i0, at most
# i0 plus j
def awf.go_hit(tab: List<&2, List<&2, String>>, j: Nat, +r: String, +i0: Nat, h: {A.shapes(awf.row(tab, j), r) == True{} : Bool}) -> awf.GH(tab, r, i0, j):
  match tab:
    case Nil{}:
      LA.mnb.absurd_f(awf.GH(Nil{}, r, i0, j), h)
    case +ps <> +more:
      match j:
        case 0n:
          (i0, (awf.pick_t(A.shapes(ps, r), i0, u => A.partition.go(more, r, 1n+i0), h), awf.le_refl(i0)))
        case 1n++m:
          awf.go_hit_at(more, r, i0, m, A.shapes(ps, r), awf.go_hit(more, m, r, 1n+i0, h))
