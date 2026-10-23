# eukhe: the proof of LAW union_fast

import Base
import ../../bend/catalog_union.bend as CU
import ../../LAWS.bend as Laws
import ./base.bend as LA

# The fast union
# --------------
# `fast` is `union` (law union_fast). A table answers the lookup of its
# list (`pcu.tab_find`): a put at key k answers e at k when k is empty and
# leaves every other key as it was (`pcu.put_look`). Two keys k, j > 0
# share a child exactly when k - 1 and j - 1 have the same parity, and
# are equal exactly when they also have the same half (`pcu.inj`, with
# `pcu.hf` and `pcu.pr`, the half and the parity by structure, equal to
# Nat.div and Nat.mod by 2: `pcu.dm`).

def pcu.hf(n: Nat) -> Nat:
  match n:
    case 0n:
      0n
    case 1n+p:
      match p:
        case 0n:
          0n
        case 1n+q:
          1n+pcu.hf(q)

def pcu.pr(n: Nat) -> Bool:
  match n:
    case 0n:
      False{}
    case 1n+p:
      match p:
        case 0n:
          True{}
        case 1n+q:
          pcu.pr(q)

def pcu.bit(b: Bool) -> Nat:
  match b:
    case True{}:
      1n
    case False{}:
      0n

def pcu.beq(a: Bool, b: Bool) -> Bool:
  match a b:
    case True{} True{}:
      True{}
    case True{} False{}:
      False{}
    case False{} True{}:
      False{}
    case False{} False{}:
      True{}

def pcu.sel(c: Bool, x: Maybe<&2, CU.Ent>, y: Maybe<&2, CU.Ent>) -> Maybe<&2, CU.Ent>:
  match c:
    case True{}:
      x
    case False{}:
      y

def pcu.add_succ(+a: Nat, +b: Nat) -> {Nat.add(a, 1n+b) == 1n+Nat.add(a, b) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      %pcu.add_succ(p, b) : {1n+Nat.add(p, 1n+b) == 1n+_ : Nat}
      {==}

def pcu.sub0(n: Nat) -> {Nat.sub(n, 0n) == n : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      {==}

# Nat.divmod by 2 is the half and the parity
def pcu.dm(n: Nat, +d: Nat) -> {Nat.divmod.go(n, 1n, d, 0n) == (Nat.add(pcu.hf(n), d), pcu.bit(pcu.pr(n))) : Nat & Nat}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      match p:
        case 0n:
          {==}
        case 1n++q:
          Equal.trans(Nat & Nat, Nat.divmod.go(q, 1n, 1n+d, 0n), (Nat.add(pcu.hf(q), 1n+d), pcu.bit(pcu.pr(q))), (1n+Nat.add(pcu.hf(q), d), pcu.bit(pcu.pr(q))), pcu.dm(q, 1n+d), Equal.cong(Nat, Nat & Nat, x => (x, pcu.bit(pcu.pr(q))), Nat.add(pcu.hf(q), 1n+d), 1n+Nat.add(pcu.hf(q), d), pcu.add_succ(pcu.hf(q), d)))

def pcu.bit1(b: Bool) -> {Nat.is_eq(pcu.bit(b), 1n) == b : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# key 1 + m goes right exactly when m is odd
def pcu.odd1(+m: Nat) -> {CU.key.odd(1n+m) == pcu.pr(m) : Bool}:
  %Equal.sym(Nat, Nat.sub(m, 0n), m, pcu.sub0(m)) : {Nat.is_eq(Nat.mod(_, 2n), 1n) == pcu.pr(m) : Bool}
  %Equal.sym(Nat & Nat, Nat.divmod.go(m, 1n, 0n, 0n), (Nat.add(pcu.hf(m), 0n), pcu.bit(pcu.pr(m))), pcu.dm(m, 0n)) : {Nat.is_eq(Pair.snd(Nat, Nat, _), 1n) == pcu.pr(m) : Bool}
  pcu.bit1(pcu.pr(m))

def pcu.add0(n: Nat) -> {Nat.add(n, 0n) == n : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(Nat, Nat, x => 1n+x, Nat.add(p, 0n), p, pcu.add0(p))

# the child key of 1 + m is the half of m
def pcu.half1(+m: Nat) -> {CU.key.half(1n+m) == pcu.hf(m) : Nat}:
  %Equal.sym(Nat, Nat.sub(m, 0n), m, pcu.sub0(m)) : {Nat.div(_, 2n) == pcu.hf(m) : Nat}
  %Equal.sym(Nat & Nat, Nat.divmod.go(m, 1n, 0n, 0n), (Nat.add(pcu.hf(m), 0n), pcu.bit(pcu.pr(m))), pcu.dm(m, 0n)) : {Pair.fst(Nat, Nat, _) == pcu.hf(m) : Nat}
  pcu.add0(pcu.hf(m))

def pcu.and_f(x: Bool) -> {False{} == Bool.and(x, False{}) : Bool}:
  match x:
    case True{}:
      {==}
    case False{}:
      {==}

# two numbers are equal exactly when their parities and halves are
def pcu.inj(m1: Nat, m2: Nat) -> {Nat.is_eq(m1, m2) == Bool.and(pcu.beq(pcu.pr(m1), pcu.pr(m2)), Nat.is_eq(pcu.hf(m1), pcu.hf(m2))) : Bool}:
  match m1:
    case 0n:
      match m2:
        case 0n:
          {==}
        case 1n+q:
          match q:
            case 0n:
              {==}
            case 1n+q2:
              pcu.and_f(pcu.beq(False{}, pcu.pr(q2)))
    case 1n+p:
      match p:
        case 0n:
          match m2:
            case 0n:
              {==}
            case 1n+q:
              match q:
                case 0n:
                  {==}
                case 1n+q2:
                  pcu.and_f(pcu.beq(True{}, pcu.pr(q2)))
        case 1n+p2:
          match m2:
            case 0n:
              pcu.and_f(pcu.beq(pcu.pr(p2), False{}))
            case 1n+q:
              match q:
                case 0n:
                  pcu.and_f(pcu.beq(pcu.pr(p2), True{}))
                case 1n+q2:
                  pcu.inj(p2, q2)

def pcu.beq_refl(b: Bool) -> {True{} == pcu.beq(b, b) : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# two keys > 0 on the same side are equal exactly when their child keys are
def pcu.same_side(+m1: Nat, +m2: Nat, +b: Bool, e1: {CU.key.odd(1n+m1) == b : Bool}, e2: {CU.key.odd(1n+m2) == b : Bool}) -> {Nat.is_eq(CU.key.half(1n+m1), CU.key.half(1n+m2)) == Nat.is_eq(m1, m2) : Bool}:
  %Equal.sym(Nat, CU.key.half(1n+m1), pcu.hf(m1), pcu.half1(m1)) : {Nat.is_eq(_, CU.key.half(1n+m2)) == Nat.is_eq(m1, m2) : Bool}
  %Equal.sym(Nat, CU.key.half(1n+m2), pcu.hf(m2), pcu.half1(m2)) : {Nat.is_eq(pcu.hf(m1), _) == Nat.is_eq(m1, m2) : Bool}
  %Equal.sym(Bool, Nat.is_eq(m1, m2), Bool.and(pcu.beq(pcu.pr(m1), pcu.pr(m2)), Nat.is_eq(pcu.hf(m1), pcu.hf(m2))), pcu.inj(m1, m2)) : {Nat.is_eq(pcu.hf(m1), pcu.hf(m2)) == _ : Bool}
  %Equal.trans(Bool, b, CU.key.odd(1n+m1), pcu.pr(m1), Equal.sym(Bool, CU.key.odd(1n+m1), b, e1), pcu.odd1(m1)) : {Nat.is_eq(pcu.hf(m1), pcu.hf(m2)) == Bool.and(pcu.beq(_, pcu.pr(m2)), Nat.is_eq(pcu.hf(m1), pcu.hf(m2))) : Bool}
  %Equal.trans(Bool, b, CU.key.odd(1n+m2), pcu.pr(m2), Equal.sym(Bool, CU.key.odd(1n+m2), b, e2), pcu.odd1(m2)) : {Nat.is_eq(pcu.hf(m1), pcu.hf(m2)) == Bool.and(pcu.beq(b, _), Nat.is_eq(pcu.hf(m1), pcu.hf(m2))) : Bool}
  %pcu.beq_refl(b) : {Nat.is_eq(pcu.hf(m1), pcu.hf(m2)) == Bool.and(_, Nat.is_eq(pcu.hf(m1), pcu.hf(m2))) : Bool}
  {==}

# two keys > 0 on other sides differ
def pcu.other_side(+m1: Nat, +m2: Nat, +b1: Bool, +b2: Bool, e1: {CU.key.odd(1n+m1) == b1 : Bool}, e2: {CU.key.odd(1n+m2) == b2 : Bool}, ne: {pcu.beq(b1, b2) == False{} : Bool}) -> {False{} == Nat.is_eq(m1, m2) : Bool}:
  %Equal.sym(Bool, Nat.is_eq(m1, m2), Bool.and(pcu.beq(pcu.pr(m1), pcu.pr(m2)), Nat.is_eq(pcu.hf(m1), pcu.hf(m2))), pcu.inj(m1, m2)) : {False{} == _ : Bool}
  %Equal.trans(Bool, b1, CU.key.odd(1n+m1), pcu.pr(m1), Equal.sym(Bool, CU.key.odd(1n+m1), b1, e1), pcu.odd1(m1)) : {False{} == Bool.and(pcu.beq(_, pcu.pr(m2)), Nat.is_eq(pcu.hf(m1), pcu.hf(m2))) : Bool}
  %Equal.trans(Bool, b2, CU.key.odd(1n+m2), pcu.pr(m2), Equal.sym(Bool, CU.key.odd(1n+m2), b2, e2), pcu.odd1(m2)) : {False{} == Bool.and(pcu.beq(b1, _), Nat.is_eq(pcu.hf(m1), pcu.hf(m2))) : Bool}
  %Equal.sym(Bool, pcu.beq(b1, b2), False{}, ne) : {False{} == Bool.and(_, Nat.is_eq(pcu.hf(m1), pcu.hf(m2))) : Bool}
  {==}

# a key below 1 + f leaves its child key below f
def pcu.lt_pred(q: Nat, g: Nat, h: {Nat.is_lt(1n+q, g) == True{} : Bool}) -> {Nat.is_lt(q, g) == True{} : Bool}:
  match q:
    case 0n:
      match g:
        case 0n:
          LA.pcu.absurdF({Nat.is_lt(0n, 0n) == True{} : Bool}, h)
        case 1n+g2:
          {==}
    case 1n+q2:
      match g:
        case 0n:
          LA.pcu.absurdF({Nat.is_lt(1n+q2, 0n) == True{} : Bool}, h)
        case 1n+g2:
          pcu.lt_pred(q2, g2, h)

def pcu.lt_hf(m: Nat, f: Nat, h: {Nat.is_lt(m, f) == True{} : Bool}) -> {Nat.is_lt(pcu.hf(m), f) == True{} : Bool}:
  match m:
    case 0n:
      h
    case 1n+p:
      match p:
        case 0n:
          match f:
            case 0n:
              LA.pcu.absurdF({Nat.is_lt(0n, 0n) == True{} : Bool}, h)
            case 1n+g:
              {==}
        case 1n++q:
          match f:
            case 0n:
              LA.pcu.absurdF({Nat.is_lt(1n+pcu.hf(q), 0n) == True{} : Bool}, h)
            case 1n++g:
              pcu.lt_hf(q, g, pcu.lt_pred(q, g, h))

def pcu.fuel(+m: Nat, +f: Nat, h: {Nat.is_lt(1n+m, 1n+f) == True{} : Bool}) -> {Nat.is_lt(CU.key.half(1n+m), f) == True{} : Bool}:
  %Equal.sym(Nat, CU.key.half(1n+m), pcu.hf(m), pcu.half1(m)) : {Nat.is_lt(_, f) == True{} : Bool}
  pcu.lt_hf(m, f, h)

def pcu.lt_succ(k: Nat) -> {Nat.is_lt(k, 1n+k) == True{} : Bool}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      pcu.lt_succ(p)

def pcu.ne_tf() -> {pcu.beq(True{}, False{}) == False{} : Bool}:
  {==}

def pcu.ne_ft() -> {pcu.beq(False{}, True{}) == False{} : Bool}:
  {==}

# a put at key k (fuel above k) puts e at k when k is empty and leaves
# every other key as it was
def pcu.put_look(fuel: Nat, t: CU.Tab, +k: Nat, +j: Nat, +ok: Bool, +oj: Bool, +e: CU.Ent, lt: {Nat.is_lt(k, fuel) == True{} : Bool}, +eok: {CU.key.odd(k) == ok : Bool}, +eoj: {CU.key.odd(j) == oj : Bool}) -> {CU.look(CU.put(fuel, t, k, CU.key.z(k), ok, e), j, CU.key.z(j), oj) == pcu.sel(Nat.is_eq(k, j), CU.keep(CU.look(t, j, CU.key.z(j), oj), e), CU.look(t, j, CU.key.z(j), oj)) : Maybe<&2, CU.Ent>}:
  match fuel:
    case 0n:
      match k:
        case 0n:
          LA.pcu.absurdF({CU.look(CU.put(0n, t, 0n, CU.key.z(0n), ok, e), j, CU.key.z(j), oj) == pcu.sel(Nat.is_eq(0n, j), CU.keep(CU.look(t, j, CU.key.z(j), oj), e), CU.look(t, j, CU.key.z(j), oj)) : Maybe<&2, CU.Ent>}, lt)
        case 1n+m:
          LA.pcu.absurdF({CU.look(CU.put(0n, t, 1n+m, CU.key.z(1n+m), ok, e), j, CU.key.z(j), oj) == pcu.sel(Nat.is_eq(1n+m, j), CU.keep(CU.look(t, j, CU.key.z(j), oj), e), CU.look(t, j, CU.key.z(j), oj)) : Maybe<&2, CU.Ent>}, lt)
    case 1n++f:
      match t:
        case CU.TNil{}:
          match k:
            case 0n:
              match j:
                case 0n:
                  {==}
                case 1n+m2:
                  match oj:
                    case True{}:
                      {==}
                    case False{}:
                      {==}
            case 1n++m1:
              match j:
                case 0n:
                  match ok:
                    case True{}:
                      {==}
                    case False{}:
                      {==}
                case 1n++m2:
                  match ok oj:
                    case True{} True{}:
                      +hk = CU.key.half(1n+m1)
                      +hj = CU.key.half(1n+m2)
                      %pcu.same_side(m1, m2, True{}, eok, eoj) : {CU.look(CU.put(f, CU.TNil{}, hk, CU.key.z(hk), CU.key.odd(hk), e), hj, CU.key.z(hj), CU.key.odd(hj)) == pcu.sel(_, CU.keep(None{}, e), None{}) : Maybe<&2, CU.Ent>}
                      pcu.put_look(f, CU.TNil{}, hk, hj, CU.key.odd(hk), CU.key.odd(hj), e, pcu.fuel(m1, f, lt), {==}, {==})
                    case True{} False{}:
                      +hk = CU.key.half(1n+m1)
                      +hj = CU.key.half(1n+m2)
                      %pcu.other_side(m1, m2, True{}, False{}, eok, eoj, pcu.ne_tf()) : {None{} == pcu.sel(_, CU.keep(None{}, e), None{}) : Maybe<&2, CU.Ent>}
                      {==}
                    case False{} True{}:
                      +hk = CU.key.half(1n+m1)
                      +hj = CU.key.half(1n+m2)
                      %pcu.other_side(m1, m2, False{}, True{}, eok, eoj, pcu.ne_ft()) : {None{} == pcu.sel(_, CU.keep(None{}, e), None{}) : Maybe<&2, CU.Ent>}
                      {==}
                    case False{} False{}:
                      +hk = CU.key.half(1n+m1)
                      +hj = CU.key.half(1n+m2)
                      %pcu.same_side(m1, m2, False{}, eok, eoj) : {CU.look(CU.put(f, CU.TNil{}, hk, CU.key.z(hk), CU.key.odd(hk), e), hj, CU.key.z(hj), CU.key.odd(hj)) == pcu.sel(_, CU.keep(None{}, e), None{}) : Maybe<&2, CU.Ent>}
                      pcu.put_look(f, CU.TNil{}, hk, hj, CU.key.odd(hk), CU.key.odd(hj), e, pcu.fuel(m1, f, lt), {==}, {==})
        case CU.TNode{+v, +l, +r}:
          match k:
            case 0n:
              match j:
                case 0n:
                  {==}
                case 1n+m2:
                  match oj:
                    case True{}:
                      {==}
                    case False{}:
                      {==}
            case 1n++m1:
              match j:
                case 0n:
                  match ok:
                    case True{}:
                      {==}
                    case False{}:
                      {==}
                case 1n++m2:
                  match ok oj:
                    case True{} True{}:
                      +hk = CU.key.half(1n+m1)
                      +hj = CU.key.half(1n+m2)
                      %pcu.same_side(m1, m2, True{}, eok, eoj) : {CU.look(CU.put(f, r, hk, CU.key.z(hk), CU.key.odd(hk), e), hj, CU.key.z(hj), CU.key.odd(hj)) == pcu.sel(_, CU.keep(CU.look(r, hj, CU.key.z(hj), CU.key.odd(hj)), e), CU.look(r, hj, CU.key.z(hj), CU.key.odd(hj))) : Maybe<&2, CU.Ent>}
                      pcu.put_look(f, r, hk, hj, CU.key.odd(hk), CU.key.odd(hj), e, pcu.fuel(m1, f, lt), {==}, {==})
                    case True{} False{}:
                      +hk = CU.key.half(1n+m1)
                      +hj = CU.key.half(1n+m2)
                      %pcu.other_side(m1, m2, True{}, False{}, eok, eoj, pcu.ne_tf()) : {CU.look(l, hj, CU.key.z(hj), CU.key.odd(hj)) == pcu.sel(_, CU.keep(CU.look(l, hj, CU.key.z(hj), CU.key.odd(hj)), e), CU.look(l, hj, CU.key.z(hj), CU.key.odd(hj))) : Maybe<&2, CU.Ent>}
                      {==}
                    case False{} True{}:
                      +hk = CU.key.half(1n+m1)
                      +hj = CU.key.half(1n+m2)
                      %pcu.other_side(m1, m2, False{}, True{}, eok, eoj, pcu.ne_ft()) : {CU.look(r, hj, CU.key.z(hj), CU.key.odd(hj)) == pcu.sel(_, CU.keep(CU.look(r, hj, CU.key.z(hj), CU.key.odd(hj)), e), CU.look(r, hj, CU.key.z(hj), CU.key.odd(hj))) : Maybe<&2, CU.Ent>}
                      {==}
                    case False{} False{}:
                      +hk = CU.key.half(1n+m1)
                      +hj = CU.key.half(1n+m2)
                      %pcu.same_side(m1, m2, False{}, eok, eoj) : {CU.look(CU.put(f, l, hk, CU.key.z(hk), CU.key.odd(hk), e), hj, CU.key.z(hj), CU.key.odd(hj)) == pcu.sel(_, CU.keep(CU.look(l, hj, CU.key.z(hj), CU.key.odd(hj)), e), CU.look(l, hj, CU.key.z(hj), CU.key.odd(hj))) : Maybe<&2, CU.Ent>}
                      pcu.put_look(f, l, hk, hj, CU.key.odd(hk), CU.key.odd(hj), e, pcu.fuel(m1, f, lt), {==}, {==})

def pcu.or_none(m: Maybe<&2, CU.Ent>) -> {m == Maybe.or(&2, CU.Ent, m, None{}) : Maybe<&2, CU.Ent>}:
  match m:
    case None{}:
      {==}
    case Some{x}:
      {==}

# one entry of the list: a put of the first entry of a key wins
def pcu.tab_step(hit: Bool, +m: Maybe<&2, CU.Ent>, +e: CU.Ent, +rest: List<&2, CU.Ent>, +j: Nat) -> {Maybe.or(&2, CU.Ent, pcu.sel(hit, CU.keep(m, e), m), CU.find(rest, j)) == Maybe.or(&2, CU.Ent, m, CU.find.go(e <> rest, j, hit)) : Maybe<&2, CU.Ent>}:
  match hit:
    case True{}:
      match m:
        case None{}:
          {==}
        case Some{x}:
          {==}
    case False{}:
      {==}

# the table of xs after t answers t's entry, else the first of xs
def pcu.tab_find(xs: List<&2, CU.Ent>, +t: CU.Tab, +j: Nat) -> {CU.find.t(CU.tab(xs, t), j) == Maybe.or(&2, CU.Ent, CU.find.t(t, j), CU.find(xs, j)) : Maybe<&2, CU.Ent>}:
  match xs:
    case Nil{}:
      pcu.or_none(CU.find.t(t, j))
    case +e <> +rest:
      +k = CU.Ent.key(e)
      +t2 = CU.put(1n+k, t, k, CU.key.z(k), CU.key.odd(k), e)
      +m = CU.find.t(t, j)
      %Equal.sym(Maybe<&2, CU.Ent>, CU.find.t(CU.tab(rest, t2), j), Maybe.or(&2, CU.Ent, CU.find.t(t2, j), CU.find(rest, j)), pcu.tab_find(rest, t2, j)) : {_ == Maybe.or(&2, CU.Ent, m, CU.find.go(e <> rest, j, Nat.is_eq(k, j))) : Maybe<&2, CU.Ent>}
      %Equal.sym(Maybe<&2, CU.Ent>, CU.find.t(t2, j), pcu.sel(Nat.is_eq(k, j), CU.keep(m, e), m), pcu.put_look(1n+k, t, k, j, CU.key.odd(k), CU.key.odd(j), e, pcu.lt_succ(k), {==}, {==})) : {Maybe.or(&2, CU.Ent, _, CU.find(rest, j)) == Maybe.or(&2, CU.Ent, m, CU.find.go(e <> rest, j, Nat.is_eq(k, j))) : Maybe<&2, CU.Ent>}
      pcu.tab_step(Nat.is_eq(k, j), m, e, rest, j)

# the bundled part by a table of the compiled catalog
def pcu.bundled_t(bs: List<&2, CU.Ent>, +cs: List<&2, CU.Ent>) -> {CU.bundled.t(bs, CU.tab(cs, CU.TNil{})) == CU.bundled(bs, cs) : List<&2, CU.Ent>}:
  match bs:
    case Nil{}:
      {==}
    case +b <> rest:
      +ct = CU.tab(cs, CU.TNil{})
      +kb = CU.Ent.key(b)
      %pcu.tab_find(cs, CU.TNil{}, kb) : {CU.with(b, CU.find.t(ct, kb)) <> CU.bundled.t(rest, ct) == CU.with(b, _) <> CU.bundled(rest, cs) : List<&2, CU.Ent>}
      %pcu.bundled_t(rest, cs) : {CU.with(b, CU.find.t(ct, kb)) <> CU.bundled.t(rest, ct) == CU.with(b, CU.find.t(ct, kb)) <> _ : List<&2, CU.Ent>}
      {==}

def pcu.seen_t(cs: List<&2, CU.Ent>, +bs: List<&2, CU.Ent>) -> {CU.seen.t(cs, CU.tab(bs, CU.TNil{})) == CU.seen.at(cs, bs) : Bool}:
  match cs:
    case Nil{}:
      {==}
    case c <> rest:
      +kc = CU.Ent.key(c)
      %pcu.tab_find(bs, CU.TNil{}, kc) : {Maybe.is_some(&2, CU.Ent, CU.find.t(CU.tab(bs, CU.TNil{}), kc)) == Maybe.is_some(&2, CU.Ent, _) : Bool}
      {==}

# the compiled part by a table of the bundle
def pcu.extra_t(cs: List<&2, CU.Ent>, +bs: List<&2, CU.Ent>, s: Bool) -> {CU.extra.t(cs, CU.tab(bs, CU.TNil{}), s) == CU.extra.go(cs, bs, s) : List<&2, CU.Ent>}:
  match cs:
    case Nil{}:
      {==}
    case c <> +rest:
      match s:
        case True{}:
          +bt = CU.tab(bs, CU.TNil{})
          %Equal.sym(Bool, CU.seen.t(rest, CU.tab(bs, CU.TNil{})), CU.seen.at(rest, bs), pcu.seen_t(rest, bs)) : {CU.extra.t(rest, bt, _) == CU.extra.go(rest, bs, CU.seen.at(rest, bs)) : List<&2, CU.Ent>}
          pcu.extra_t(rest, bs, CU.seen.at(rest, bs))
        case False{}:
          +bt = CU.tab(bs, CU.TNil{})
          %Equal.sym(Bool, CU.seen.t(rest, CU.tab(bs, CU.TNil{})), CU.seen.at(rest, bs), pcu.seen_t(rest, bs)) : {c <> CU.extra.t(rest, bt, _) == c <> CU.extra.go(rest, bs, CU.seen.at(rest, bs)) : List<&2, CU.Ent>}
          Equal.cong(List<&2, CU.Ent>, List<&2, CU.Ent>, x => c <> x, CU.extra.t(rest, bt, CU.seen.at(rest, bs)), CU.extra.go(rest, bs, CU.seen.at(rest, bs)), pcu.extra_t(rest, bs, CU.seen.at(rest, bs)))

def pcu.fast(+bs: List<&2, CU.Ent>, +cs: List<&2, CU.Ent>) -> {CU.fast(bs, cs) == CU.union(bs, cs) : List<&2, CU.Ent>}:
  +bt = CU.tab(bs, CU.TNil{})
  +ct = CU.tab(cs, CU.TNil{})
  %Equal.sym(Bool, CU.seen.t(cs, bt), CU.seen.at(cs, bs), pcu.seen_t(cs, bs)) : {List.append(&2, CU.Ent, CU.bundled.t(bs, ct), CU.extra.t(cs, bt, _)) == CU.union(bs, cs) : List<&2, CU.Ent>}
  %Equal.sym(List<&2, CU.Ent>, CU.extra.t(cs, bt, CU.seen.at(cs, bs)), CU.extra.go(cs, bs, CU.seen.at(cs, bs)), pcu.extra_t(cs, bs, CU.seen.at(cs, bs))) : {List.append(&2, CU.Ent, CU.bundled.t(bs, ct), _) == CU.union(bs, cs) : List<&2, CU.Ent>}
  %Equal.sym(List<&2, CU.Ent>, CU.bundled.t(bs, ct), CU.bundled(bs, cs), pcu.bundled_t(bs, cs)) : {List.append(&2, CU.Ent, _, CU.extra(cs, bs)) == CU.union(bs, cs) : List<&2, CU.Ent>}
  {==}

def Laws.union_fast(bs, cs):
  pcu.fast(bs, cs)
