# eukhe: lemmas of area quirks: the model's verdicts, rule by rule
#
# The verdict at index i of verdicts.go(rs, known, i0) is the verdict of
# rule i on the rules after it, whose clash scan (clash.go) starts at the
# index i0 + i + 1. qv.cg_none and qv.cg_some read that scan: no hit means
# no later rule clashes; a hit at J is a rule that clashes, J - n places
# on from where the scan started at n; qv.cg_first: no rule before it
# clashes.

import Base
import ../../../bend/infer.bend as If
import ../../../laws/quirks.bend as Quirks
import ../base.bend as QP

# Logic
# -----

def qv.BD(b: Bool, G: Type) -> Type:
  match b:
    case True{}:
      G
    case False{}:
      Unit

# a False that is True proves anything
def qv.absurd(-G: Type, e: {False{} == True{} : Bool}) -> G:
  %e : qv.BD(_, G)
  Unit{}

# a True that is False proves anything
def qv.absurd_tf(-G: Type, e: {True{} == False{} : Bool}) -> G:
  qv.absurd(G, Equal.sym(Bool, True{}, False{}, e))

def qv.is_some(-A: Data, m: Maybe<&2, A>) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{x}:
      True{}

# None is never Some
def qv.none_some(-A: Data, -G: Type, -x: A, e: {None{} == Some{x} : Maybe<&2, A>}) -> G:
  qv.absurd(G, Equal.cong(Maybe<&2, A>, Bool, m => qv.is_some(A, m), None{}, Some{x}, e))

# Some is never None
def qv.some_none(-A: Data, -G: Type, -x: A, e: {Some{x} == None{} : Maybe<&2, A>}) -> G:
  qv.absurd_tf(G, Equal.cong(Maybe<&2, A>, Bool, m => qv.is_some(A, m), Some{x}, None{}, e))

def qv.or(-A: Data, d: A, m: Maybe<&2, A>) -> A:
  match m:
    case None{}:
      d
    case Some{x}:
      x

# Some is one to one
def qv.some_inj(-A: Data, +x: A, -y: A, e: {Some{x} == Some{y} : Maybe<&2, A>}) -> {x == y : A}:
  Equal.cong(Maybe<&2, A>, A, m => qv.or(A, x, m), Some{x}, Some{y}, e)

# Numbers
# -------

def qv.add_zero(n: Nat) -> {Nat.add(n, 0n) == n : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(Nat, Nat, x => 1n+x, Nat.add(p, 0n), p, qv.add_zero(p))

def qv.add_succ(n: Nat, -k: Nat) -> {Nat.add(n, 1n+k) == 1n+Nat.add(n, k) : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(Nat, Nat, x => 1n+x, Nat.add(p, 1n+k), 1n+Nat.add(p, k), qv.add_succ(p, k))

# n + k is never below n
def qv.lt_add(n: Nat, k: Nat) -> {Nat.is_lt(Nat.add(n, k), n) == False{} : Bool}:
  match n:
    case 0n:
      match k:
        case 0n:
          {==}
        case 1n+q:
          {==}
    case 1n+p:
      qv.lt_add(p, k)

# The model's clash scan
# ----------------------

# no hit: no rule of xs clashes with r
def qv.cg_none(xs: List<&2, If.Rule>, +r: If.Rule, +n: Nat, b: Bool, eb: {If.clash.head(r, xs) == b : Bool}, e: {If.clash.go(xs, r, n, b) == None{} : Maybe<&2, Nat>}, k: Nat, -s: If.Rule, g: {List.get(&2, If.Rule, xs, k) == Some{s} : Maybe<&2, If.Rule>}) -> {Quirks.qs_clash(r, s) == False{} : Bool}:
  match xs:
    case Nil{}:
      qv.none_some(If.Rule, {Quirks.qs_clash(r, s) == False{} : Bool}, s, g)
    case +x <> +t:
      match b:
        case True{}:
          qv.some_none(Nat, {Quirks.qs_clash(r, s) == False{} : Bool}, n, e)
        case False{}:
          match k:
            case 0n:
              %qv.some_inj(If.Rule, x, s, g) : {Quirks.qs_clash(r, _) == False{} : Bool}
              Equal.trans(Bool, Quirks.qs_clash(r, x), If.clash(r, x), False{}, Equal.sym(Bool, If.clash(r, x), Quirks.qs_clash(r, x), QP.qp.clash_eq(r, x)), eb)
            case 1n+k1:
              qv.cg_none(t, r, 1n+n, If.clash.head(r, t), {==}, e, k1, s, g)

# a hit at J: the rule J - n places on clashes with r
def qv.HIT(xs: List<&2, If.Rule>, r: If.Rule, n: Nat, J: Nat) -> Type:
  Sigma<&1, &1, Nat, k => {J == Nat.add(n, k) : Nat} & {Quirks.qs_clash_at(r, List.get(&2, If.Rule, xs, k)) == True{} : Bool}>

# a hit in t, scanned from 1 + n, is a hit in x <> t from n
def qv.hit_next(-x: If.Rule, -t: List<&2, If.Rule>, -r: If.Rule, +n: Nat, -J: Nat, h: qv.HIT(t, r, 1n+n, J)) -> qv.HIT(x <> t, r, n, J):
  (k, p) = h
  (ej, ec) = p
  (1n+k, (Equal.trans(Nat, J, Nat.add(1n+n, k), Nat.add(n, 1n+k), ej, Equal.sym(Nat, Nat.add(n, 1n+k), 1n+Nat.add(n, k), qv.add_succ(n, k))), ec))

def qv.cg_some(xs: List<&2, If.Rule>, +r: If.Rule, +n: Nat, -J: Nat, b: Bool, eb: {If.clash.head(r, xs) == b : Bool}, e: {If.clash.go(xs, r, n, b) == Some{J} : Maybe<&2, Nat>}) -> qv.HIT(xs, r, n, J):
  match xs:
    case Nil{}:
      qv.none_some(Nat, qv.HIT(Nil{}, r, n, J), J, e)
    case +x <> +t:
      match b:
        case True{}:
          +ej = Equal.trans(Nat, J, n, Nat.add(n, 0n), Equal.sym(Nat, n, J, qv.some_inj(Nat, n, J, e)), Equal.sym(Nat, Nat.add(n, 0n), n, qv.add_zero(n)))
          (0n, (ej, Equal.trans(Bool, Quirks.qs_clash(r, x), If.clash(r, x), True{}, Equal.sym(Bool, If.clash(r, x), Quirks.qs_clash(r, x), QP.qp.clash_eq(r, x)), eb)))
        case False{}:
          qv.hit_next(x, t, r, n, J, qv.cg_some(t, r, 1n+n, J, If.clash.head(r, t), {==}, e))

# a hit at J is the first: no rule before it clashes with r
def qv.cg_first(xs: List<&2, If.Rule>, +r: If.Rule, +n: Nat, +J: Nat, b: Bool, eb: {If.clash.head(r, xs) == b : Bool}, e: {If.clash.go(xs, r, n, b) == Some{J} : Maybe<&2, Nat>}, k: Nat, -s: If.Rule, g: {List.get(&2, If.Rule, xs, k) == Some{s} : Maybe<&2, If.Rule>}, lt: {Nat.is_lt(Nat.add(n, k), J) == True{} : Bool}) -> {Quirks.qs_clash(r, s) == False{} : Bool}:
  match xs:
    case Nil{}:
      qv.none_some(If.Rule, {Quirks.qs_clash(r, s) == False{} : Bool}, s, g)
    case +x <> +t:
      match b:
        case True{}:
          +lt0 = Equal.trans(Bool, Nat.is_lt(Nat.add(n, k), n), Nat.is_lt(Nat.add(n, k), J), True{}, Equal.cong(Nat, Bool, z => Nat.is_lt(Nat.add(n, k), z), n, J, qv.some_inj(Nat, n, J, e)), lt)
          qv.absurd_tf({Quirks.qs_clash(r, s) == False{} : Bool}, Equal.trans(Bool, True{}, Nat.is_lt(Nat.add(n, k), n), False{}, Equal.sym(Bool, Nat.is_lt(Nat.add(n, k), n), True{}, lt0), qv.lt_add(n, k)))
        case False{}:
          match k:
            case 0n:
              %qv.some_inj(If.Rule, x, s, g) : {Quirks.qs_clash(r, _) == False{} : Bool}
              Equal.trans(Bool, Quirks.qs_clash(r, x), If.clash(r, x), False{}, Equal.sym(Bool, If.clash(r, x), Quirks.qs_clash(r, x), QP.qp.clash_eq(r, x)), eb)
            case 1n+k1:
              +lt1 = Equal.trans(Bool, Nat.is_lt(1n+Nat.add(n, k1), J), Nat.is_lt(Nat.add(n, 1n+k1), J), True{}, Equal.cong(Nat, Bool, z => Nat.is_lt(z, J), 1n+Nat.add(n, k1), Nat.add(n, 1n+k1), Equal.sym(Nat, Nat.add(n, 1n+k1), 1n+Nat.add(n, k1), qv.add_succ(n, k1))), lt)
              qv.cg_first(t, r, 1n+n, J, If.clash.head(r, t), {==}, e, k1, s, g, lt1)

# The verdict on one rule
# -----------------------

def qv.isF(m: Maybe<&2, If.Verdict>) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{v}:
      match v:
        case If.Fine{}:
          True{}
        case If.Unheard{}:
          False{}
        case If.ClashAt{j}:
          False{}

def qv.isC(m: Maybe<&2, If.Verdict>) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{v}:
      match v:
        case If.Fine{}:
          False{}
        case If.Unheard{}:
          False{}
        case If.ClashAt{j}:
          True{}

def qv.at(m: Maybe<&2, If.Verdict>) -> Nat:
  match m:
    case None{}:
      0n
    case Some{v}:
      match v:
        case If.Fine{}:
          0n
        case If.Unheard{}:
          0n
        case If.ClashAt{j}:
          j

# a fine verdict: the scan found no clash
def qv.v_fine(k: Bool, c: Maybe<&2, Nat>, e: {Some{If.verdict(k, c)} == Some{If.Fine{}} : Maybe<&2, If.Verdict>}) -> {c == None{} : Maybe<&2, Nat>}:
  match k:
    case False{}:
      qv.absurd({c == None{} : Maybe<&2, Nat>}, Equal.cong(Maybe<&2, If.Verdict>, Bool, qv.isF, Some{If.Unheard{}}, Some{If.Fine{}}, e))
    case True{}:
      match c:
        case None{}:
          {==}
        case Some{j}:
          qv.absurd({Some{j} == None{} : Maybe<&2, Nat>}, Equal.cong(Maybe<&2, If.Verdict>, Bool, qv.isF, Some{If.ClashAt{j}}, Some{If.Fine{}}, e))

# a clash verdict: the scan hit
def qv.v_clash(k: Bool, c: Maybe<&2, Nat>, -J: Nat, e: {Some{If.verdict(k, c)} == Some{If.ClashAt{J}} : Maybe<&2, If.Verdict>}) -> {c == Some{J} : Maybe<&2, Nat>}:
  match k:
    case False{}:
      qv.absurd({c == Some{J} : Maybe<&2, Nat>}, Equal.cong(Maybe<&2, If.Verdict>, Bool, qv.isC, Some{If.Unheard{}}, Some{If.ClashAt{J}}, e))
    case True{}:
      match c:
        case None{}:
          qv.absurd({None{} == Some{J} : Maybe<&2, Nat>}, Equal.cong(Maybe<&2, If.Verdict>, Bool, qv.isC, Some{If.Fine{}}, Some{If.ClashAt{J}}, e))
        case Some{j}:
          Equal.cong(Nat, Maybe<&2, Nat>, x => Some{x}, j, J, Equal.cong(Maybe<&2, If.Verdict>, Nat, qv.at, Some{If.ClashAt{j}}, Some{If.ClashAt{J}}, e))

# a verdict says a known directive exactly when it is known
def qv.v_heard(k: Bool, c: Maybe<&2, Nat>) -> {Quirks.qs_heard(Some{If.verdict(k, c)}) == k : Bool}:
  match k:
    case False{}:
      {==}
    case True{}:
      match c:
        case None{}:
          {==}
        case Some{j}:
          {==}

# The verdicts, rule by rule
# --------------------------

# rule i's verdict says its directive is known exactly when it is
def qv.heard(rs: List<&2, If.Rule>, +known: List<&2, Nat>, +i0: Nat, i: Nat, -r: If.Rule, at: {List.get(&2, If.Rule, rs, i) == Some{r} : Maybe<&2, If.Rule>}) -> {Quirks.qs_heard(List.get(&2, If.Verdict, If.verdicts.go(rs, known, i0), i)) == Quirks.qs_mem(known, Quirks.qs_dir(r)) : Bool}:
  match rs:
    case Nil{}:
      qv.none_some(If.Rule, {Quirks.qs_heard(None{}) == Quirks.qs_mem(known, Quirks.qs_dir(r)) : Bool}, r, at)
    case +r1 <> +rest:
      match i:
        case 0n:
          %qv.some_inj(If.Rule, r1, r, at) : {Quirks.qs_heard(Some{If.verdict(If.elem(known, If.Rule.dir(r1)), If.clash.go(rest, r1, 1n+i0, If.clash.head(r1, rest)))}) == Quirks.qs_mem(known, Quirks.qs_dir(_)) : Bool}
          %QP.qp.dir(r1) : {Quirks.qs_heard(Some{If.verdict(If.elem(known, If.Rule.dir(r1)), If.clash.go(rest, r1, 1n+i0, If.clash.head(r1, rest)))}) == Quirks.qs_mem(known, _) : Bool}
          %QP.qp.mem(known, If.Rule.dir(r1)) : {Quirks.qs_heard(Some{If.verdict(If.elem(known, If.Rule.dir(r1)), If.clash.go(rest, r1, 1n+i0, If.clash.head(r1, rest)))}) == _ : Bool}
          qv.v_heard(If.elem(known, If.Rule.dir(r1)), If.clash.go(rest, r1, 1n+i0, If.clash.head(r1, rest)))
        case 1n+i1:
          qv.heard(rest, known, 1n+i0, i1, r, at)

# a fine rule i clashes with no later rule j
def qv.fine(rs: List<&2, If.Rule>, +known: List<&2, Nat>, +i0: Nat, i: Nat, j: Nat, -r: If.Rule, -s: If.Rule, at: {List.get(&2, If.Rule, rs, i) == Some{r} : Maybe<&2, If.Rule>}, fine: {List.get(&2, If.Verdict, If.verdicts.go(rs, known, i0), i) == Some{If.Fine{}} : Maybe<&2, If.Verdict>}, later: {List.get(&2, If.Rule, rs, j) == Some{s} : Maybe<&2, If.Rule>}, after: {Nat.is_lt(i, j) == True{} : Bool}) -> {Quirks.qs_clash(r, s) == False{} : Bool}:
  match rs:
    case Nil{}:
      qv.none_some(If.Rule, {Quirks.qs_clash(r, s) == False{} : Bool}, r, at)
    case +r1 <> +rest:
      match i:
        case 0n:
          match j:
            case 0n:
              qv.absurd({Quirks.qs_clash(r, s) == False{} : Bool}, after)
            case 1n+j1:
              %qv.some_inj(If.Rule, r1, r, at) : {Quirks.qs_clash(_, s) == False{} : Bool}
              qv.cg_none(rest, r1, 1n+i0, If.clash.head(r1, rest), {==}, qv.v_fine(If.elem(known, If.Rule.dir(r1)), If.clash.go(rest, r1, 1n+i0, If.clash.head(r1, rest)), fine), j1, s, later)
        case 1n+i1:
          match j:
            case 0n:
              qv.absurd({Quirks.qs_clash(r, s) == False{} : Bool}, after)
            case 1n+j1:
              qv.fine(rest, known, 1n+i0, i1, j1, r, s, at, fine, later, after)

# a clash verdict of rule i: the index of a later rule it clashes with
def qv.CL(rs: List<&2, If.Rule>, r: If.Rule, i0: Nat, i: Nat, J: Nat) -> Type:
  Sigma<&1, &1, Nat, p => {J == Nat.add(i0, p) : Nat} & ({Nat.is_lt(i, p) == True{} : Bool} & {Quirks.qs_clash_at(r, List.get(&2, If.Rule, rs, p)) == True{} : Bool})>

def qv.cl_head(-r1: If.Rule, -rest: List<&2, If.Rule>, +i0: Nat, -J: Nat, h: qv.HIT(rest, r1, 1n+i0, J)) -> qv.CL(r1 <> rest, r1, i0, 0n, J):
  (k, p) = h
  (ej, ec) = p
  (1n+k, (Equal.trans(Nat, J, 1n+Nat.add(i0, k), Nat.add(i0, 1n+k), ej, Equal.sym(Nat, Nat.add(i0, 1n+k), 1n+Nat.add(i0, k), qv.add_succ(i0, k))), ({==}, ec)))

def qv.cl_next(-r1: If.Rule, -rest: List<&2, If.Rule>, -r: If.Rule, +i0: Nat, -i1: Nat, -J: Nat, h: qv.CL(rest, r, 1n+i0, i1, J)) -> qv.CL(r1 <> rest, r, i0, 1n+i1, J):
  (p, q) = h
  (ej, lc) = q
  (1n+p, (Equal.trans(Nat, J, 1n+Nat.add(i0, p), Nat.add(i0, 1n+p), ej, Equal.sym(Nat, Nat.add(i0, 1n+p), 1n+Nat.add(i0, p), qv.add_succ(i0, p))), lc))

def qv.clash(rs: List<&2, If.Rule>, +known: List<&2, Nat>, +i0: Nat, i: Nat, -r: If.Rule, -J: Nat, at: {List.get(&2, If.Rule, rs, i) == Some{r} : Maybe<&2, If.Rule>}, v: {List.get(&2, If.Verdict, If.verdicts.go(rs, known, i0), i) == Some{If.ClashAt{J}} : Maybe<&2, If.Verdict>}) -> qv.CL(rs, r, i0, i, J):
  match rs:
    case Nil{}:
      qv.none_some(If.Rule, qv.CL(Nil{}, r, i0, i, J), r, at)
    case +r1 <> +rest:
      match i:
        case 0n:
          %qv.some_inj(If.Rule, r1, r, at) : qv.CL(r1 <> rest, _, i0, 0n, J)
          qv.cl_head(r1, rest, i0, J, qv.cg_some(rest, r1, 1n+i0, J, If.clash.head(r1, rest), {==}, qv.v_clash(If.elem(known, If.Rule.dir(r1)), If.clash.go(rest, r1, 1n+i0, If.clash.head(r1, rest)), J, v)))
        case 1n+i1:
          qv.cl_next(r1, rest, r, i0, i1, J, qv.clash(rest, known, 1n+i0, i1, r, J, at, v))

# a clash verdict of rule i at J: no rule k between them clashes
def qv.first(rs: List<&2, If.Rule>, +known: List<&2, Nat>, +i0: Nat, i: Nat, k: Nat, -r: If.Rule, -s: If.Rule, +J: Nat, at: {List.get(&2, If.Rule, rs, i) == Some{r} : Maybe<&2, If.Rule>}, v: {List.get(&2, If.Verdict, If.verdicts.go(rs, known, i0), i) == Some{If.ClashAt{J}} : Maybe<&2, If.Verdict>}, mid: {List.get(&2, If.Rule, rs, k) == Some{s} : Maybe<&2, If.Rule>}, after: {Nat.is_lt(i, k) == True{} : Bool}, before: {Nat.is_lt(Nat.add(i0, k), J) == True{} : Bool}) -> {Quirks.qs_clash(r, s) == False{} : Bool}:
  match rs:
    case Nil{}:
      qv.none_some(If.Rule, {Quirks.qs_clash(r, s) == False{} : Bool}, r, at)
    case +r1 <> +rest:
      match i:
        case 0n:
          match k:
            case 0n:
              qv.absurd({Quirks.qs_clash(r, s) == False{} : Bool}, after)
            case 1n+k1:
              +b1 = Equal.trans(Bool, Nat.is_lt(1n+Nat.add(i0, k1), J), Nat.is_lt(Nat.add(i0, 1n+k1), J), True{}, Equal.cong(Nat, Bool, z => Nat.is_lt(z, J), 1n+Nat.add(i0, k1), Nat.add(i0, 1n+k1), Equal.sym(Nat, Nat.add(i0, 1n+k1), 1n+Nat.add(i0, k1), qv.add_succ(i0, k1))), before)
              %qv.some_inj(If.Rule, r1, r, at) : {Quirks.qs_clash(_, s) == False{} : Bool}
              qv.cg_first(rest, r1, 1n+i0, J, If.clash.head(r1, rest), {==}, qv.v_clash(If.elem(known, If.Rule.dir(r1)), If.clash.go(rest, r1, 1n+i0, If.clash.head(r1, rest)), J, v), k1, s, mid, b1)
        case 1n+i1:
          match k:
            case 0n:
              qv.absurd({Quirks.qs_clash(r, s) == False{} : Bool}, after)
            case 1n+k1:
              +b1 = Equal.trans(Bool, Nat.is_lt(1n+Nat.add(i0, k1), J), Nat.is_lt(Nat.add(i0, 1n+k1), J), True{}, Equal.cong(Nat, Bool, z => Nat.is_lt(z, J), 1n+Nat.add(i0, k1), Nat.add(i0, 1n+k1), Equal.sym(Nat, Nat.add(i0, 1n+k1), 1n+Nat.add(i0, k1), qv.add_succ(i0, k1))), before)
              qv.first(rest, known, 1n+i0, i1, k1, r, s, J, at, v, mid, after, b1)

# The count of faults
# -------------------

# no verdict is a fault exactly when every verdict is fine
def qv.faults(vs: List<&2, If.Verdict>) -> {Nat.is_eq(Quirks.qs_faults(vs), 0n) == If.fine_all(vs) : Bool}:
  match vs:
    case Nil{}:
      {==}
    case v <> t:
      match v:
        case If.Fine{}:
          qv.faults(t)
        case If.Unheard{}:
          {==}
        case If.ClashAt{j}:
          {==}
