# eukhe: lemmas of area quirks: the model's any_at, rule by rule
#
# any_at reads, on each rule, the model's applies, directive and rank; the
# laws read the target table (qs_applies), qs_dir and the precedence table
# (qs_rule_rank): qa.applies, QP.qp.dir and qa.rank say they agree. qa.wit
# walks the rules carrying the head's test as b (qa.unf: any_at is the
# head's test or any_at of the rest).

import Base
import ../../../bend/infer.bend as If
import ../../../laws/quirks.bend as Quirks
import ../base.bend as QP
import ./verdicts.bend as QV

# The terms
# ---------

# the model's applies is the target table's
def qa.applies(q: If.Query, r: If.Rule) -> {If.applies(q, r) == Quirks.qs_applies(q, r) : Bool}:
  match q:
    case If.Query{f, m, h}:
      match r:
        case If.Rule{l, t, d, v}:
          match l:
            case If.Fam{}:
              {==}
            case If.Mod{}:
              {==}
            case If.Host{}:
              {==}

# the model's rank is the precedence table's
def qa.rank(r: If.Rule) -> {If.Rule.rank(r) == Quirks.qs_rule_rank(r) : Nat}:
  match r:
    case If.Rule{l, t, d, v}:
      match l:
        case If.Fam{}:
          {==}
        case If.Mod{}:
          {==}
        case If.Host{}:
          {==}

# Logic
# -----

def qa.and3(-b1: Bool, -b2: Bool, -b3: Bool, e1: {b1 == True{} : Bool}, e2: {b2 == True{} : Bool}, e3: {b3 == True{} : Bool}) -> {Bool.and(Bool.and(b1, b2), b3) == True{} : Bool}:
  %Equal.sym(Bool, b1, True{}, e1) : {Bool.and(Bool.and(_, b2), b3) == True{} : Bool}
  %Equal.sym(Bool, b2, True{}, e2) : {Bool.and(Bool.and(True{}, _), b3) == True{} : Bool}
  %Equal.sym(Bool, b3, True{}, e3) : {Bool.and(Bool.and(True{}, True{}), _) == True{} : Bool}
  {==}

def qa.split(b1: Bool, b2: Bool, b3: Bool, e: {Bool.and(Bool.and(b1, b2), b3) == True{} : Bool}) -> {b1 == True{} : Bool} & ({b2 == True{} : Bool} & {b3 == True{} : Bool}):
  match b1:
    case False{}:
      QV.qv.absurd({False{} == True{} : Bool} & ({b2 == True{} : Bool} & {b3 == True{} : Bool}), e)
    case True{}:
      match b2:
        case False{}:
          QV.qv.absurd({True{} == True{} : Bool} & ({False{} == True{} : Bool} & {b3 == True{} : Bool}), e)
        case True{}:
          match b3:
            case False{}:
              QV.qv.absurd({True{} == True{} : Bool} & ({True{} == True{} : Bool} & {False{} == True{} : Bool}), e)
            case True{}:
              ({==}, ({==}, {==}))

def qa.or_l(-a: Bool, -b: Bool, e: {a == True{} : Bool}) -> {Bool.or(a, b) == True{} : Bool}:
  %Equal.sym(Bool, a, True{}, e) : {Bool.or(_, b) == True{} : Bool}
  {==}

def qa.or_r(a: Bool, -b: Bool, e: {b == True{} : Bool}) -> {Bool.or(a, b) == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      e

# A rule found
# ------------

# a rule i of rs that applies, with the directive and precedence k or
# above, makes any_at say yes
def qa.found(rs: List<&2, If.Rule>, +q: If.Query, +d: Nat, +k: Nat, i: Nat, +r: If.Rule, at: {List.get(&2, If.Rule, rs, i) == Some{r} : Maybe<&2, If.Rule>}, hit: {Quirks.qs_applies(q, r) == True{} : Bool}, hd: {Nat.is_eq(Quirks.qs_dir(r), d) == True{} : Bool}, hk: {Nat.is_le(k, Quirks.qs_rule_rank(r)) == True{} : Bool}) -> {If.any_at(rs, q, d, k) == True{} : Bool}:
  match rs:
    case Nil{}:
      QV.qv.none_some(If.Rule, {If.any_at(Nil{}, q, d, k) == True{} : Bool}, r, at)
    case +r1 <> rest:
      match i:
        case 0n:
          %Equal.sym(If.Rule, r1, r, QV.qv.some_inj(If.Rule, r1, r, at)) : {If.any_at(_ <> rest, q, d, k) == True{} : Bool}
          +e1 = Equal.trans(Bool, If.applies(q, r), Quirks.qs_applies(q, r), True{}, qa.applies(q, r), hit)
          +e2 = Equal.trans(Bool, Nat.is_eq(If.Rule.dir(r), d), Nat.is_eq(Quirks.qs_dir(r), d), True{}, Equal.cong(Nat, Bool, x => Nat.is_eq(x, d), If.Rule.dir(r), Quirks.qs_dir(r), QP.qp.dir(r)), hd)
          +e3 = Equal.trans(Bool, Nat.is_le(k, If.Rule.rank(r)), Nat.is_le(k, Quirks.qs_rule_rank(r)), True{}, Equal.cong(Nat, Bool, x => Nat.is_le(k, x), If.Rule.rank(r), Quirks.qs_rule_rank(r), qa.rank(r)), hk)
          qa.or_l(Bool.and(Bool.and(If.applies(q, r), Nat.is_eq(If.Rule.dir(r), d)), Nat.is_le(k, If.Rule.rank(r))), If.any_at(rest, q, d, k), qa.and3(If.applies(q, r), Nat.is_eq(If.Rule.dir(r), d), Nat.is_le(k, If.Rule.rank(r)), e1, e2, e3))
        case 1n+i1:
          qa.or_r(Bool.and(Bool.and(If.applies(q, r1), Nat.is_eq(If.Rule.dir(r1), d)), Nat.is_le(k, If.Rule.rank(r1))), If.any_at(rest, q, d, k), qa.found(rest, q, d, k, i1, r, at, hit, hd, hk))

# A rule witnessed
# ----------------

# rule i of rs applies, with the directive and precedence k or above
def qa.W(rs: List<&2, If.Rule>, q: If.Query, d: Nat, k: Nat) -> Type:
  Sigma<&1, &1, Nat, i => Sigma<&1, &1, If.Rule, r => {List.get(&2, If.Rule, rs, i) == Some{r} : Maybe<&2, If.Rule>} & ({Quirks.qs_applies(q, r) == True{} : Bool} & ({Nat.is_eq(Quirks.qs_dir(r), d) == True{} : Bool} & {Nat.is_le(k, Quirks.qs_rule_rank(r)) == True{} : Bool}))>>

# the head's test, as any_at makes it
def qa.hd_of(rs: List<&2, If.Rule>, +q: If.Query, +d: Nat, +k: Nat) -> Bool:
  match rs:
    case Nil{}:
      False{}
    case +r <> rest:
      Bool.and(Bool.and(If.applies(q, r), Nat.is_eq(If.Rule.dir(r), d)), Nat.is_le(k, If.Rule.rank(r)))

# the head's test b, or any_at of the rest
def qa.rest_or(b: Bool, rs: List<&2, If.Rule>, +q: If.Query, +d: Nat, +k: Nat) -> Bool:
  match rs:
    case Nil{}:
      False{}
    case r <> rest:
      Bool.or(b, If.any_at(rest, q, d, k))

def qa.unf(rs: List<&2, If.Rule>, +q: If.Query, +d: Nat, +k: Nat) -> {If.any_at(rs, q, d, k) == qa.rest_or(qa.hd_of(rs, q, d, k), rs, q, d, k) : Bool}:
  match rs:
    case Nil{}:
      {==}
    case r <> rest:
      {==}

# a witness in the rest is one in r1 <> rest, one place on
def qa.next(-r1: If.Rule, -rest: List<&2, If.Rule>, -q: If.Query, -d: Nat, -k: Nat, w: qa.W(rest, q, d, k)) -> qa.W(r1 <> rest, q, d, k):
  (i, p) = w
  (r, ps) = p
  (1n+i, (r, ps))

# the head r1 passes the test: it is the witness, read through the tables
def qa.head(+r1: If.Rule, -rest: List<&2, If.Rule>, +q: If.Query, +d: Nat, +k: Nat, sp: {If.applies(q, r1) == True{} : Bool} & ({Nat.is_eq(If.Rule.dir(r1), d) == True{} : Bool} & {Nat.is_le(k, If.Rule.rank(r1)) == True{} : Bool})) -> qa.W(r1 <> rest, q, d, k):
  (s1, s23) = sp
  (s2, s3) = s23
  +e1 = Equal.trans(Bool, Quirks.qs_applies(q, r1), If.applies(q, r1), True{}, Equal.sym(Bool, If.applies(q, r1), Quirks.qs_applies(q, r1), qa.applies(q, r1)), s1)
  +e2 = Equal.trans(Bool, Nat.is_eq(Quirks.qs_dir(r1), d), Nat.is_eq(If.Rule.dir(r1), d), True{}, Equal.cong(Nat, Bool, x => Nat.is_eq(x, d), Quirks.qs_dir(r1), If.Rule.dir(r1), Equal.sym(Nat, If.Rule.dir(r1), Quirks.qs_dir(r1), QP.qp.dir(r1))), s2)
  +e3 = Equal.trans(Bool, Nat.is_le(k, Quirks.qs_rule_rank(r1)), Nat.is_le(k, If.Rule.rank(r1)), True{}, Equal.cong(Nat, Bool, x => Nat.is_le(k, x), Quirks.qs_rule_rank(r1), If.Rule.rank(r1), Equal.sym(Nat, If.Rule.rank(r1), Quirks.qs_rule_rank(r1), qa.rank(r1))), s3)
  (0n, (r1, ({==}, (e1, (e2, e3)))))

def qa.wit(rs: List<&2, If.Rule>, +q: If.Query, +d: Nat, +k: Nat, b: Bool, eb: {qa.hd_of(rs, q, d, k) == b : Bool}, h: {qa.rest_or(b, rs, q, d, k) == True{} : Bool}) -> qa.W(rs, q, d, k):
  match rs:
    case Nil{}:
      QV.qv.absurd(qa.W(Nil{}, q, d, k), h)
    case +r1 <> +rest:
      match b:
        case True{}:
          qa.head(r1, rest, q, d, k, qa.split(If.applies(q, r1), Nat.is_eq(If.Rule.dir(r1), d), Nat.is_le(k, If.Rule.rank(r1)), eb))
        case False{}:
          +h2 = Equal.trans(Bool, qa.rest_or(qa.hd_of(rest, q, d, k), rest, q, d, k), If.any_at(rest, q, d, k), True{}, Equal.sym(Bool, If.any_at(rest, q, d, k), qa.rest_or(qa.hd_of(rest, q, d, k), rest, q, d, k), qa.unf(rest, q, d, k)), h)
          qa.next(r1, rest, q, d, k, qa.wit(rest, q, d, k, qa.hd_of(rest, q, d, k), {==}, h2))
