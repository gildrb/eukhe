# eukhe: lemmas of the history laws of area autoresearch (prefix ah.):
# absurd cases, Bool and Nat facts, the last kept metric over appended
# rows, and the order of kept metrics a keep extends.

import Base
import ../../../bend/autoresearch/dec.bend as ArD
import ../../../bend/autoresearch/line.bend as ArL
import ../../../bend/autoresearch/state.bend as ArS
import ../../../spec/autoresearch/segment.bend as SG

# Absurd cases
# ------------

def ah.If(b: Bool, G: Type) -> Type:
  match b:
    case True{}:
      G
    case False{}:
      Unit

# False is not True
def ah.absurd(-G: Type, e: {False{} == True{} : Bool}) -> G:
  %e : ah.If(_, G)
  Unit{}

def ah.IfF(b: Bool, G: Type) -> Type:
  match b:
    case True{}:
      Unit
    case False{}:
      G

# True is not False
def ah.absurdT(-G: Type, e: {True{} == False{} : Bool}) -> G:
  %e : ah.IfF(_, G)
  Unit{}

def ah.Z(n: Nat, G: Type) -> Type:
  match n:
    case 0n:
      G
    case 1n+p:
      Unit

def ah.pred(n: Nat) -> Nat:
  match n:
    case 0n:
      0n
    case 1n+p:
      p

# no number is its own successor
def ah.nsucc(-G: Type, n: Nat, e: {1n+n == n : Nat}) -> G:
  match n:
    case 0n:
      %e : ah.Z(_, G)
      Unit{}
    case 1n+k:
      ah.nsucc(G, k, Equal.cong(Nat, Nat, ah.pred, 2n+k, 1n+k, e))

# Bool and Nat facts
# ------------------

def ah.and_l(+a: Bool, -b: Bool, e: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case False{}:
      ah.absurd({False{} == True{} : Bool}, e)
    case True{}:
      {==}

def ah.and_r(+a: Bool, -b: Bool, e: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case False{}:
      ah.absurd({b == True{} : Bool}, e)
    case True{}:
      e

def ah.and_i(+a: Bool, -b: Bool, ea: {a == True{} : Bool}, eb: {b == True{} : Bool}) -> {Bool.and(a, b) == True{} : Bool}:
  %Equal.sym(Bool, a, True{}, ea) : {Bool.and(_, b) == True{} : Bool}
  eb

def ah.eq_refl(n: Nat) -> {Nat.is_eq(n, n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+k:
      ah.eq_refl(k)

def ah.add_zero(n: Nat) -> {Nat.add(n, 0n) == n : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+k:
      Equal.cong(Nat, Nat, x => 1n+x, Nat.add(k, 0n), k, ah.add_zero(k))

def ah.add_succ(a: Nat, -b: Nat) -> {Nat.add(a, 1n+b) == 1n+Nat.add(a, b) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+k:
      Equal.cong(Nat, Nat, x => 1n+x, Nat.add(k, 1n+b), 1n+Nat.add(k, b), ah.add_succ(k, b))

def ah.add_assoc(a: Nat, -b: Nat, -c: Nat) -> {Nat.add(Nat.add(a, b), c) == Nat.add(a, Nat.add(b, c)) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+k:
      Equal.cong(Nat, Nat, x => 1n+x, Nat.add(Nat.add(k, b), c), Nat.add(k, Nat.add(b, c)), ah.add_assoc(k, b, c))

# The last kept metric
# --------------------

def ah.last_at_none(x: Maybe<&2, ArD.Dec>) -> {ArS.last.at(None{}, x) == x : Maybe<&2, ArD.Dec>}:
  match x:
    case None{}:
      {==}
    case Some{y}:
      {==}

def ah.last_at_assoc(-a: Maybe<&2, ArD.Dec>, -b: Maybe<&2, ArD.Dec>, c: Maybe<&2, ArD.Dec>) -> {ArS.last.at(a, ArS.last.at(b, c)) == ArS.last.at(ArS.last.at(a, b), c) : Maybe<&2, ArD.Dec>}:
  match c:
    case None{}:
      {==}
    case Some{y}:
      {==}

# the last kept metric of rs then ys: that of ys, else that of rs
def ah.last_app(rs: List<&2, ArS.Row>, +ys: List<&2, ArS.Row>, +seg: Nat) -> {ArS.last(ArS.snoc(rs, ys), seg) == ArS.last.at(ArS.last(rs, seg), ArS.last(ys, seg)) : Maybe<&2, ArD.Dec>}:
  match rs:
    case Nil{}:
      Equal.sym(Maybe<&2, ArD.Dec>, ArS.last.at(None{}, ArS.last(ys, seg)), ArS.last(ys, seg), ah.last_at_none(ArS.last(ys, seg)))
    case +r <> +t:
      Equal.trans(Maybe<&2, ArD.Dec>, ArS.last.at(ArS.kept(r, seg), ArS.last(ArS.snoc(t, ys), seg)), ArS.last.at(ArS.kept(r, seg), ArS.last.at(ArS.last(t, seg), ArS.last(ys, seg))), ArS.last.at(ArS.last.at(ArS.kept(r, seg), ArS.last(t, seg)), ArS.last(ys, seg)), Equal.cong(Maybe<&2, ArD.Dec>, Maybe<&2, ArD.Dec>, x => ArS.last.at(ArS.kept(r, seg), x), ArS.last(ArS.snoc(t, ys), seg), ArS.last.at(ArS.last(t, seg), ArS.last(ys, seg)), ah.last_app(t, ys, seg)), ah.last_at_assoc(ArS.kept(r, seg), ArS.last(t, seg), ArS.last(ys, seg)))

# rows that keep nothing leave the last kept metric
def ah.last_none(+rs: List<&2, ArS.Row>, +ys: List<&2, ArS.Row>, +seg: Nat, h: {ArS.last(ys, seg) == None{} : Maybe<&2, ArD.Dec>}) -> {ArS.last(ArS.snoc(rs, ys), seg) == ArS.last(rs, seg) : Maybe<&2, ArD.Dec>}:
  Equal.trans(Maybe<&2, ArD.Dec>, ArS.last(ArS.snoc(rs, ys), seg), ArS.last.at(ArS.last(rs, seg), ArS.last(ys, seg)), ArS.last(rs, seg), ah.last_app(rs, ys, seg), Equal.cong(Maybe<&2, ArD.Dec>, Maybe<&2, ArD.Dec>, k => ArS.last.at(ArS.last(rs, seg), k), ArS.last(ys, seg), None{}, h))

def ah.kof(b: Bool, -m: Maybe<&2, ArD.Dec>) -> {ArS.kept.of(Bool.and(b, False{}), m) == None{} : Maybe<&2, ArD.Dec>}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# an abandoned run keeps nothing
def ah.last_ab0(+m: String, +sg: Nat, p: Maybe<&2, ArS.Pend>, +seg: Nat) -> {ArS.last(ArS.abandon(m, sg, p), seg) == None{} : Maybe<&2, ArD.Dec>}:
  match p:
    case None{}:
      {==}
    case Some{q}:
      match q:
        case ArS.Pend{id, kvs, fin}:
          ah.kof(Nat.is_eq(sg, seg), ArS.lookup(kvs, m))

def ah.last_ab(+rs: List<&2, ArS.Row>, +m: String, +sg: Nat, +p: Maybe<&2, ArS.Pend>, +seg: Nat) -> {ArS.last(ArS.snoc(rs, ArS.abandon(m, sg, p)), seg) == ArS.last(rs, seg) : Maybe<&2, ArD.Dec>}:
  ah.last_none(rs, ArS.abandon(m, sg, p), seg, ah.last_ab0(m, sg, p, seg))

# a run logged with a status other than keep keeps nothing
def ah.last_nk0(+m: String, +sg: Nat, p: ArS.Pend, st: ArS.Status, -desc: String, +seg: Nat, h: {ArS.kept.st(Some{st}) == False{} : Bool}) -> {ArS.last([ArS.row(m, sg, p, Some{st}, desc)], seg) == None{} : Maybe<&2, ArD.Dec>}:
  match p:
    case ArS.Pend{id, kvs, fin}:
      match st:
        case ArS.Keep{}:
          ah.absurdT({ArS.last([ArS.row(m, sg, ArS.Pend{id, kvs, fin}, Some{ArS.Keep{}}, desc)], seg) == None{} : Maybe<&2, ArD.Dec>}, h)
        case ArS.Discard{}:
          ah.kof(Nat.is_eq(sg, seg), ArS.lookup(kvs, m))
        case ArS.Crash{}:
          ah.kof(Nat.is_eq(sg, seg), ArS.lookup(kvs, m))
        case ArS.Checks{}:
          ah.kof(Nat.is_eq(sg, seg), ArS.lookup(kvs, m))

def ah.last_nk(+rs: List<&2, ArS.Row>, +m: String, +sg: Nat, +p: ArS.Pend, +st: ArS.Status, +desc: String, +seg: Nat, h: {ArS.kept.st(Some{st}) == False{} : Bool}) -> {ArS.last(ArS.snoc(rs, [ArS.row(m, sg, p, Some{st}, desc)]), seg) == ArS.last(rs, seg) : Maybe<&2, ArD.Dec>}:
  ah.last_none(rs, [ArS.row(m, sg, p, Some{st}, desc)], seg, ah.last_nk0(m, sg, p, st, desc, seg, h))

def ah.prim(c: ArS.Cfg) -> {ArS.primary(Some{c}) == ArS.Cfg.metric(c) : String}:
  match c:
    case ArS.Cfg{name, goal, metric, unit, dir, sec, scope, off, max}:
      {==}

# a kept run of the segment keeps its parsed metric
def ah.kept_keep(+id: Nat, +seg: Nat, +kvs: List<&2, ArL.Kv>, -fin: Maybe<&2, Bool>, -desc: String, +mc: String, -x: ArD.Dec, eq: {ArS.lookup(kvs, mc) == Some{x} : Maybe<&2, ArD.Dec>}) -> {ArS.kept(ArS.row(mc, seg, ArS.Pend{id, kvs, fin}, Some{ArS.Keep{}}, desc), seg) == Some{x} : Maybe<&2, ArD.Dec>}:
  %Equal.sym(Bool, Nat.is_eq(seg, seg), True{}, ah.eq_refl(seg)) : {ArS.kept.of(Bool.and(_, True{}), ArS.lookup(kvs, mc)) == Some{x} : Maybe<&2, ArD.Dec>}
  eq

def ah.last_keep(+rs: List<&2, ArS.Row>, +id: Nat, +seg: Nat, +kvs: List<&2, ArL.Kv>, +fin: Maybe<&2, Bool>, +desc: String, +mc: String, +x: ArD.Dec, eq: {ArS.lookup(kvs, mc) == Some{x} : Maybe<&2, ArD.Dec>}) -> {ArS.last(ArS.snoc(rs, [ArS.row(mc, seg, ArS.Pend{id, kvs, fin}, Some{ArS.Keep{}}, desc)]), seg) == Some{x} : Maybe<&2, ArD.Dec>}:
  +r = ArS.row(mc, seg, ArS.Pend{id, kvs, fin}, Some{ArS.Keep{}}, desc)
  Equal.trans(Maybe<&2, ArD.Dec>, ArS.last(ArS.snoc(rs, [r]), seg), ArS.last.at(ArS.last(rs, seg), ArS.last.at(ArS.kept(r, seg), None{})), Some{x}, ah.last_app(rs, [r], seg), Equal.cong(Maybe<&2, ArD.Dec>, Maybe<&2, ArD.Dec>, k => ArS.last.at(ArS.last(rs, seg), ArS.last.at(k, None{})), ArS.kept(r, seg), Some{x}, ah.kept_keep(id, seg, kvs, fin, desc, mc, x, eq)))

# Beating the kept metrics
# ------------------------

def ah.ba_at(+dir: ArS.Dir, +x: ArD.Dec, -k1: Maybe<&2, ArD.Dec>, k2: Maybe<&2, ArD.Dec>, h1: {ArS.beats.at(dir, x, k1) == True{} : Bool}, h2: {ArS.beats.at(dir, x, k2) == True{} : Bool}) -> {ArS.beats.at(dir, x, ArS.last.at(k1, k2)) == True{} : Bool}:
  match k2:
    case None{}:
      h1
    case Some{y}:
      h2

# a metric that beats every kept one beats the last
def ah.beats_last(+dir: ArS.Dir, +x: ArD.Dec, rs: List<&2, ArS.Row>, +seg: Nat, +h: {ArS.beats(dir, x, rs, seg) == True{} : Bool}) -> {ArS.beats.at(dir, x, ArS.last(rs, seg)) == True{} : Bool}:
  match rs:
    case Nil{}:
      {==}
    case +r <> +t:
      ah.ba_at(dir, x, ArS.kept(r, seg), ArS.last(t, seg), ah.and_l(ArS.beats.at(dir, x, ArS.kept(r, seg)), ArS.beats(dir, x, t, seg), h), ah.beats_last(dir, x, t, seg, ah.and_r(ArS.beats.at(dir, x, ArS.kept(r, seg)), ArS.beats(dir, x, t, seg), h)))

# the code's order is the spec's
def ah.better_sg(d: ArS.Dir, -x: ArD.Dec, -y: ArD.Dec) -> {ArS.better(d, x, y) == SG.is_better(~ArD.Dec.cmp, d, x, y) : Bool}:
  match d:
    case ArS.Lower{}:
      {==}
    case ArS.Higher{}:
      {==}
