# eukhe: lemmas the proofs of the cvar resolution laws share: the
# model's id test and lookup against the laws' plain id checks.

import Base
import ../../../bend/cvar.bend as Cv
import ../../../laws/cvar/resolution.bend as Cvar
import ../base.bend as LA
import ./save.bend as LS

# Booleans
# --------

def rs.not_t(b: Bool, h: {Bool.not(b) == True{} : Bool}) -> {b == False{} : Bool}:
  match b:
    case True{}:
      LA.pv.absurdF({True{} == False{} : Bool}, h)
    case False{}:
      {==}

# Ids
# ---

def rs.decl_id(d: Cv.Decl) -> {Cv.Decl.id(d) == Cvar.spec_id(d) : Nat}:
  match d:
    case Cv.Decl{i, t, c, p, r, v}:
      {==}

# the model's id test on d is the laws' own: d has id x
def rs.id_hit(d: Cv.Decl, +x: Nat, ed: {Cvar.spec_id(d) == x : Nat}) -> {True{} == Nat.is_eq(Cv.Decl.id(d), x) : Bool}:
  match d:
    case Cv.Decl{+i, t, c, p, r, v}:
      %ed : {True{} == Nat.is_eq(i, _) : Bool}
      LA.cvar.pv.eq_refl(i)

# a declaration with another id
def rs.id_miss(d: Cv.Decl, +x: Nat, h: {Bool.not(Nat.is_eq(Cvar.spec_id(d), x)) == True{} : Bool}) -> {False{} == Nat.is_eq(Cv.Decl.id(d), x) : Bool}:
  match d:
    case Cv.Decl{+i, t, c, p, r, v}:
      Equal.sym(Bool, Nat.is_eq(i, x), False{}, rs.not_t(Nat.is_eq(i, x), h))

# the lookup of x past declarations of other ids, to d of id x
def rs.find_first(pre: List<&2, Cv.Decl>, +x: Nat, +d: Cv.Decl, +post: List<&2, Cv.Decl>, ed: {Cvar.spec_id(d) == x : Nat}, +fresh: {Cvar.spec_no_id(pre, x) == True{} : Bool}) -> {Cv.find(List.append(&2, Cv.Decl, pre, d <> post), x) == Some{d} : Maybe<&2, Cv.Decl>}:
  match pre:
    case Nil{}:
      %rs.id_hit(d, x, ed) : {Cv.find.go(d <> post, x, _) == Some{d} : Maybe<&2, Cv.Decl>}
      {==}
    case +h <> +t:
      %rs.id_miss(h, x, LA.cvar.pv.and_l(Bool.not(Nat.is_eq(Cvar.spec_id(h), x)), Cvar.spec_no_id(t, x), fresh)) : {Cv.find.go(h <> List.append(&2, Cv.Decl, t, d <> post), x, _) == Some{d} : Maybe<&2, Cv.Decl>}
      rs.find_first(t, x, d, post, ed, LA.cvar.pv.and_r(Bool.not(Nat.is_eq(Cvar.spec_id(h), x)), Cvar.spec_no_id(t, x), fresh))

# the lookup of an id no declaration has
def rs.find_absent(ds: List<&2, Cv.Decl>, +x: Nat, +none: {Cvar.spec_no_id(ds, x) == True{} : Bool}) -> {Cv.find(ds, x) == None{} : Maybe<&2, Cv.Decl>}:
  match ds:
    case Nil{}:
      {==}
    case +h <> +t:
      %rs.id_miss(h, x, LA.cvar.pv.and_l(Bool.not(Nat.is_eq(Cvar.spec_id(h), x)), Cvar.spec_no_id(t, x), none)) : {Cv.find.go(h <> t, x, _) == None{} : Maybe<&2, Cv.Decl>}
      rs.find_absent(t, x, LA.cvar.pv.and_r(Bool.not(Nat.is_eq(Cvar.spec_id(h), x)), Cvar.spec_no_id(t, x), none))

def rs.some_go(hb: Bool, +h: Cv.Decl, +t: List<&2, Cv.Decl>, +x: Nat, eh: {Nat.is_eq(Cv.Decl.id(h), x) == hb : Bool}, ih: {Maybe.is_some(&2, Cv.Decl, Cv.find(t, x)) == Bool.not(Cvar.spec_no_id(t, x)) : Bool}) -> {Maybe.is_some(&2, Cv.Decl, Cv.find.go(h <> t, x, hb)) == Bool.not(Bool.and(Bool.not(Nat.is_eq(Cv.Decl.id(h), x)), Cvar.spec_no_id(t, x))) : Bool}:
  match hb:
    case True{}:
      %Equal.sym(Bool, Nat.is_eq(Cv.Decl.id(h), x), True{}, eh) : {True{} == Bool.not(Bool.and(Bool.not(_), Cvar.spec_no_id(t, x))) : Bool}
      {==}
    case False{}:
      %Equal.sym(Bool, Nat.is_eq(Cv.Decl.id(h), x), False{}, eh) : {Maybe.is_some(&2, Cv.Decl, Cv.find(t, x)) == Bool.not(Bool.and(Bool.not(_), Cvar.spec_no_id(t, x))) : Bool}
      ih

# x is declared in ds exactly when some declaration has id x
def rs.some_no_id(ds: List<&2, Cv.Decl>, +x: Nat) -> {Maybe.is_some(&2, Cv.Decl, Cv.find(ds, x)) == Bool.not(Cvar.spec_no_id(ds, x)) : Bool}:
  match ds:
    case Nil{}:
      {==}
    case +h <> +t:
      %rs.decl_id(h) : {Maybe.is_some(&2, Cv.Decl, Cv.find.go(h <> t, x, Nat.is_eq(Cv.Decl.id(h), x))) == Bool.not(Bool.and(Bool.not(Nat.is_eq(_, x)), Cvar.spec_no_id(t, x))) : Bool}
      rs.some_go(Nat.is_eq(Cv.Decl.id(h), x), h, t, x, {==}, rs.some_no_id(t, x))

# Defaults down a chain
# ---------------------

def rs.orm_default(m: Maybe<&2, Cv.Val>, +c: Maybe<&2, Cv.Val>, +b: Cv.Val) -> {Maybe.default(&2, Cv.Val, LS.sv.orm(m, c), b) == Maybe.default(&2, Cv.Val, m, Maybe.default(&2, Cv.Val, c, b)) : Cv.Val}:
  match m:
    case None{}:
      {==}
    case Some{y}:
      {==}

# a layer over c, defaulted to b, is the layer over nothing, defaulted to
# c's default
def rs.layer_default(+ss: List<&2, Cv.Bind>, +ds: List<&2, Cv.Decl>, +l: Cv.Layer, +x: Nat, +c: Maybe<&2, Cv.Val>, +b: Cv.Val) -> {Maybe.default(&2, Cv.Val, Cv.layer(ss, ds, l, x, c), b) == Maybe.default(&2, Cv.Val, Cv.layer(ss, ds, l, x, None{}), Maybe.default(&2, Cv.Val, c, b)) : Cv.Val}:
  %Equal.sym(Maybe<&2, Cv.Val>, Cv.layer(ss, ds, l, x, c), LS.sv.orm(Cv.layer(ss, ds, l, x, None{}), c), LS.sv.or(ss, ds, l, x, c)) : {Maybe.default(&2, Cv.Val, _, b) == Maybe.default(&2, Cv.Val, Cv.layer(ss, ds, l, x, None{}), Maybe.default(&2, Cv.Val, c, b)) : Cv.Val}
  rs.orm_default(Cv.layer(ss, ds, l, x, None{}), c, b)

# one agent on a defaulted value: its layers on the value, defaulted
def rs.over(+p: List<&2, Cv.Bind>, +s: List<&2, Cv.Bind>, +ds: List<&2, Cv.Decl>, +x: Nat, +c: Maybe<&2, Cv.Val>, +b: Cv.Val) -> {Cv.over(ds, Cv.Ag{p, s}, x, Maybe.default(&2, Cv.Val, c, b)) == Maybe.default(&2, Cv.Val, Cv.layer(s, ds, Cv.Agent{}, x, Cv.layer(p, ds, Cv.Agent{}, x, c)), b) : Cv.Val}:
  +d = Maybe.default(&2, Cv.Val, c, b)
  +pn = Cv.layer(p, ds, Cv.Agent{}, x, None{})
  +pc = Cv.layer(p, ds, Cv.Agent{}, x, c)
  +sn = Cv.layer(s, ds, Cv.Agent{}, x, None{})
  +m = Maybe.default(&2, Cv.Val, sn, Maybe.default(&2, Cv.Val, pn, d))
  +m2 = Maybe.default(&2, Cv.Val, sn, Maybe.default(&2, Cv.Val, pc, b))
  +lhs = Maybe.default(&2, Cv.Val, Cv.layer(s, ds, Cv.Agent{}, x, pn), d)
  +rhs = Maybe.default(&2, Cv.Val, Cv.layer(s, ds, Cv.Agent{}, x, pc), b)
  Equal.trans(Cv.Val, lhs, m, rhs, rs.layer_default(s, ds, Cv.Agent{}, x, pn, d),
    Equal.sym(Cv.Val, rhs, m,
      Equal.trans(Cv.Val, rhs, m2, m, rs.layer_default(s, ds, Cv.Agent{}, x, pc, b),
        Equal.cong(Cv.Val, Cv.Val, y => Maybe.default(&2, Cv.Val, sn, y), Maybe.default(&2, Cv.Val, pc, b), Maybe.default(&2, Cv.Val, pn, d), rs.layer_default(p, ds, Cv.Agent{}, x, c, b)))))

# a chain on a defaulted value is the chain's layered value, defaulted
def rs.chain(fam: List<&2, Cv.Ag>, +ds: List<&2, Cv.Decl>, +x: Nat, +c: Maybe<&2, Cv.Val>, +b: Cv.Val) -> {Cv.chain(fam, ds, x, Maybe.default(&2, Cv.Val, c, b)) == Maybe.default(&2, Cv.Val, Cv.chainm(fam, ds, x, c), b) : Cv.Val}:
  match fam:
    case Nil{}:
      {==}
    case Cv.Ag{+p, +s} <> +rest:
      +n = Cv.layer(s, ds, Cv.Agent{}, x, Cv.layer(p, ds, Cv.Agent{}, x, c))
      %Equal.sym(Cv.Val, Cv.over(ds, Cv.Ag{p, s}, x, Maybe.default(&2, Cv.Val, c, b)), Maybe.default(&2, Cv.Val, n, b), rs.over(p, s, ds, x, c, b)) : {Cv.chain(rest, ds, x, _) == Maybe.default(&2, Cv.Val, Cv.chainm(rest, ds, x, n), b) : Cv.Val}
      rs.chain(rest, ds, x, n, b)

# the value of a cvar of declaration m: its layered value, else its default
def rs.value_at(m: Maybe<&2, Cv.Decl>, +ds: List<&2, Cv.Decl>, +cfg: List<&2, Cv.Bind>, +fam: List<&2, Cv.Ag>, +x: Nat) -> {Cv.value.at(m, ds, cfg, fam, x) == Cvar.spec_value.at(m, Cv.layered(ds, cfg, fam, x)) : Maybe<&2, Cv.Val>}:
  match m:
    case None{}:
      {==}
    case Some{d}:
      match d:
        case Cv.Decl{i, t, c, p, r, +v}:
          +lc = Cv.layer(cfg, ds, Cv.Config{}, x, None{})
          Equal.cong(Cv.Val, Maybe<&2, Cv.Val>, y => Some{y}, Cv.chain(fam, ds, x, Maybe.default(&2, Cv.Val, lc, v)), Maybe.default(&2, Cv.Val, Cv.chainm(fam, ds, x, lc), v), rs.chain(fam, ds, x, lc, v))

# Layers
# ------

def rs.ty_eq(v: Cv.Val, t: Cv.Ty) -> {Cv.Ty.eq(Cv.Val.ty(v), t) == Cvar.spec_typed(v, t) : Bool}:
  match v:
    case Cv.VNat{n}:
      match t:
        case Cv.TNat{}:
          {==}
        case Cv.TBool{}:
          {==}
    case Cv.VBool{b}:
      match t:
        case Cv.TNat{}:
          {==}
        case Cv.TBool{}:
          {==}

def rs.and_true(b: Bool) -> {b == Bool.and(b, True{}) : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def rs.and_false(b: Bool) -> {False{} == Bool.and(b, False{}) : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# the model's validity of a value under declaration m is the laws' rule
def rs.valid_at(m: Maybe<&2, Cv.Decl>, l: Cv.Layer, +i: Nat, +v: Cv.Val) -> {Cv.valid.at(m, l, Cv.Bind{i, v}) == Cvar.spec_counts.at(m, l, v) : Bool}:
  match m:
    case None{}:
      {==}
    case Some{d}:
      match d:
        case Cv.Decl{j, +t, c, p, r, w}:
          match c:
            case Cv.Global{}:
              match l:
                case Cv.Config{}:
                  rs.ty_eq(v, t)
                case Cv.Agent{}:
                  rs.and_false(Cvar.spec_typed(v, t))
            case Cv.Local{}:
              match l:
                case Cv.Config{}:
                  rs.ty_eq(v, t)
                case Cv.Agent{}:
                  Equal.trans(Bool, Cv.Ty.eq(Cv.Val.ty(v), t), Cvar.spec_typed(v, t), Bool.and(Cvar.spec_typed(v, t), True{}), rs.ty_eq(v, t), rs.and_true(Cvar.spec_typed(v, t)))

# the model's validity of a set is the laws' rule (Cvar.spec_counts)
def rs.valid(+ds: List<&2, Cv.Decl>, l: Cv.Layer, s: Cv.Bind) -> {Cv.valid(ds, l, s) == Cvar.spec_counts(ds, l, s) : Bool}:
  match s:
    case Cv.Bind{+i, +v}:
      rs.valid_at(Cv.find(ds, i), l, i, v)

def rs.one_go(h: Bool, +s: Cv.Bind, +ds: List<&2, Cv.Decl>, +l: Cv.Layer, +x: Nat) -> {Cv.layer.go([s], ds, l, x, None{}, h) == Cvar.spec_latest.or(None{}, h, Cv.Bind.val(s)) : Maybe<&2, Cv.Val>}:
  match h:
    case True{}:
      {==}
    case False{}:
      {==}

# one set alone: its value when it is a set of x that counts, else none
def rs.one(s: Cv.Bind, +ds: List<&2, Cv.Decl>, +l: Cv.Layer, +x: Nat) -> {Cv.layer([s], ds, l, x, None{}) == Cvar.spec_latest(Cvar.spec_tag(l, [s]), ds, x) : Maybe<&2, Cv.Val>}:
  match s:
    case Cv.Bind{+i, +v}:
      +b = {Cv.Bind{i, v} : Cv.Bind}
      %Equal.sym(Bool, Cv.hit.when(Nat.is_eq(i, x), ds, l, b), Bool.and(Nat.is_eq(i, x), Cv.valid(ds, l, b)), LA.pv.hit_and(Nat.is_eq(i, x), ds, l, b)) : {Cv.layer.go([b], ds, l, x, None{}, _) == Cvar.spec_latest.or(None{}, Bool.and(Nat.is_eq(i, x), Cvar.spec_counts(ds, l, b)), v) : Maybe<&2, Cv.Val>}
      %Equal.sym(Bool, Cv.valid(ds, l, b), Cvar.spec_counts(ds, l, b), rs.valid(ds, l, b)) : {Cv.layer.go([b], ds, l, x, None{}, Bool.and(Nat.is_eq(i, x), _)) == Cvar.spec_latest.or(None{}, Bool.and(Nat.is_eq(i, x), Cvar.spec_counts(ds, l, b)), v) : Maybe<&2, Cv.Val>}
      rs.one_go(Bool.and(Nat.is_eq(i, x), Cvar.spec_counts(ds, l, b)), b, ds, l, x)

# the latest of t, over m before it: m when t holds no counting set of x
def rs.at_orm(t: Cvar.LSet, m: Maybe<&2, Cv.Val>, +r: Maybe<&2, Cv.Val>, +ds: List<&2, Cv.Decl>, +x: Nat) -> {Cvar.spec_latest.at(t, LS.sv.orm(m, r), ds, x) == LS.sv.orm(m, Cvar.spec_latest.at(t, r, ds, x)) : Maybe<&2, Cv.Val>}:
  match t:
    case Cvar.LSet{l, s}:
      match m:
        case None{}:
          {==}
        case Some{w}:
          {==}

def rs.orm_none(m: Maybe<&2, Cv.Val>) -> {m == LS.sv.orm(m, None{}) : Maybe<&2, Cv.Val>}:
  match m:
    case None{}:
      {==}
    case Some{w}:
      {==}

# the latest set of a ++ b: b's, else a's
def rs.latest_app(a: List<&2, Cvar.LSet>, +b: List<&2, Cvar.LSet>, +ds: List<&2, Cv.Decl>, +x: Nat) -> {Cvar.spec_latest(List.append(&2, Cvar.LSet, a, b), ds, x) == LS.sv.orm(Cvar.spec_latest(b, ds, x), Cvar.spec_latest(a, ds, x)) : Maybe<&2, Cv.Val>}:
  match a:
    case Nil{}:
      rs.orm_none(Cvar.spec_latest(b, ds, x))
    case +t <> +rest:
      %Equal.sym(Maybe<&2, Cv.Val>, Cvar.spec_latest(List.append(&2, Cvar.LSet, rest, b), ds, x), LS.sv.orm(Cvar.spec_latest(b, ds, x), Cvar.spec_latest(rest, ds, x)), rs.latest_app(rest, b, ds, x)) : {Cvar.spec_latest.at(t, _, ds, x) == LS.sv.orm(Cvar.spec_latest(b, ds, x), Cvar.spec_latest.at(t, Cvar.spec_latest(rest, ds, x), ds, x)) : Maybe<&2, Cv.Val>}
      rs.at_orm(t, Cvar.spec_latest(b, ds, x), Cvar.spec_latest(rest, ds, x), ds, x)

# a layer over nothing is the latest set of it that counts
def rs.layer_tag(ss: List<&2, Cv.Bind>, +ds: List<&2, Cv.Decl>, +l: Cv.Layer, +x: Nat) -> {Cv.layer(ss, ds, l, x, None{}) == Cvar.spec_latest(Cvar.spec_tag(l, ss), ds, x) : Maybe<&2, Cv.Val>}:
  match ss:
    case Nil{}:
      {==}
    case +s <> +rest:
      +one = Cv.layer([s], ds, l, x, None{})
      +ts = Cvar.spec_tag(l, [s])
      +tr = Cvar.spec_tag(l, rest)
      +m1 = Cv.layer(rest, ds, l, x, one)
      +m2 = LS.sv.orm(Cv.layer(rest, ds, l, x, None{}), one)
      +m3 = LS.sv.orm(Cvar.spec_latest(tr, ds, x), Cvar.spec_latest(ts, ds, x))
      +fin = Cvar.spec_latest(List.append(&2, Cvar.LSet, ts, tr), ds, x)
      Equal.trans(Maybe<&2, Cv.Val>, Cv.layer(s <> rest, ds, l, x, None{}), m1, fin, LA.pv.layer_cons(s, rest, ds, l, x, None{}),
        Equal.trans(Maybe<&2, Cv.Val>, m1, m2, fin, LS.sv.or(rest, ds, l, x, one),
          Equal.trans(Maybe<&2, Cv.Val>, m2, m3, fin,
            Equal.trans(Maybe<&2, Cv.Val>, m2, LS.sv.orm(Cvar.spec_latest(tr, ds, x), one), m3,
              Equal.cong(Maybe<&2, Cv.Val>, Maybe<&2, Cv.Val>, y => LS.sv.orm(y, one), Cv.layer(rest, ds, l, x, None{}), Cvar.spec_latest(tr, ds, x), rs.layer_tag(rest, ds, l, x)),
              Equal.cong(Maybe<&2, Cv.Val>, Maybe<&2, Cv.Val>, y => LS.sv.orm(Cvar.spec_latest(tr, ds, x), y), one, Cvar.spec_latest(ts, ds, x), rs.one(s, ds, l, x))),
            Equal.sym(Maybe<&2, Cv.Val>, fin, m3, rs.latest_app(ts, tr, ds, x)))))

# a family chain on cur: its latest counting set, else cur
def rs.chainm(fam: List<&2, Cv.Ag>, +ds: List<&2, Cv.Decl>, +x: Nat, +cur: Maybe<&2, Cv.Val>) -> {Cv.chainm(fam, ds, x, cur) == LS.sv.orm(Cvar.spec_latest(Cvar.spec_flat_fam(fam), ds, x), cur) : Maybe<&2, Cv.Val>}:
  match fam:
    case Nil{}:
      {==}
    case Cv.Ag{+p, +s} <> +rest:
      +tp = Cvar.spec_tag(Cv.Agent{}, p)
      +tq = Cvar.spec_tag(Cv.Agent{}, s)
      +fr = Cvar.spec_flat_fam(rest)
      +lp = Cvar.spec_latest(tp, ds, x)
      +lq = Cvar.spec_latest(tq, ds, x)
      +lr = Cvar.spec_latest(fr, ds, x)
      +pc = Cv.layer(p, ds, Cv.Agent{}, x, cur)
      +sc = Cv.layer(s, ds, Cv.Agent{}, x, pc)
      +n1 = LS.sv.orm(lr, sc)
      +n2 = LS.sv.orm(lr, LS.sv.orm(lq, LS.sv.orm(lp, cur)))
      +n3 = LS.sv.orm(LS.sv.orm(lr, lq), LS.sv.orm(lp, cur))
      +n4 = LS.sv.orm(LS.sv.orm(LS.sv.orm(lr, lq), lp), cur)
      +qr = Cvar.spec_latest(List.append(&2, Cvar.LSet, tq, fr), ds, x)
      +all = Cvar.spec_latest(List.append(&2, Cvar.LSet, tp, List.append(&2, Cvar.LSet, tq, fr)), ds, x)
      +fin = LS.sv.orm(all, cur)
      +e_pc = Equal.trans(Maybe<&2, Cv.Val>, pc, LS.sv.orm(Cv.layer(p, ds, Cv.Agent{}, x, None{}), cur), LS.sv.orm(lp, cur), LS.sv.or(p, ds, Cv.Agent{}, x, cur), Equal.cong(Maybe<&2, Cv.Val>, Maybe<&2, Cv.Val>, y => LS.sv.orm(y, cur), Cv.layer(p, ds, Cv.Agent{}, x, None{}), lp, rs.layer_tag(p, ds, Cv.Agent{}, x)))
      +e_sc = Equal.trans(Maybe<&2, Cv.Val>, sc, LS.sv.orm(Cv.layer(s, ds, Cv.Agent{}, x, None{}), pc), LS.sv.orm(lq, LS.sv.orm(lp, cur)), LS.sv.or(s, ds, Cv.Agent{}, x, pc),
        Equal.trans(Maybe<&2, Cv.Val>, LS.sv.orm(Cv.layer(s, ds, Cv.Agent{}, x, None{}), pc), LS.sv.orm(lq, pc), LS.sv.orm(lq, LS.sv.orm(lp, cur)),
          Equal.cong(Maybe<&2, Cv.Val>, Maybe<&2, Cv.Val>, y => LS.sv.orm(y, pc), Cv.layer(s, ds, Cv.Agent{}, x, None{}), lq, rs.layer_tag(s, ds, Cv.Agent{}, x)),
          Equal.cong(Maybe<&2, Cv.Val>, Maybe<&2, Cv.Val>, y => LS.sv.orm(lq, y), pc, LS.sv.orm(lp, cur), e_pc)))
      +e_all = Equal.trans(Maybe<&2, Cv.Val>, all, LS.sv.orm(qr, lp), LS.sv.orm(LS.sv.orm(lr, lq), lp), rs.latest_app(tp, List.append(&2, Cvar.LSet, tq, fr), ds, x),
        Equal.cong(Maybe<&2, Cv.Val>, Maybe<&2, Cv.Val>, y => LS.sv.orm(y, lp), qr, LS.sv.orm(lr, lq), rs.latest_app(tq, fr, ds, x)))
      Equal.trans(Maybe<&2, Cv.Val>, Cv.chainm(rest, ds, x, sc), n1, fin, rs.chainm(rest, ds, x, sc),
        Equal.trans(Maybe<&2, Cv.Val>, n1, n2, fin, Equal.cong(Maybe<&2, Cv.Val>, Maybe<&2, Cv.Val>, y => LS.sv.orm(lr, y), sc, LS.sv.orm(lq, LS.sv.orm(lp, cur)), e_sc),
          Equal.trans(Maybe<&2, Cv.Val>, n2, n3, fin, LS.sv.orm_assoc(lr, lq, LS.sv.orm(lp, cur)),
            Equal.trans(Maybe<&2, Cv.Val>, n3, n4, fin, LS.sv.orm_assoc(LS.sv.orm(lr, lq), lp, cur),
              Equal.sym(Maybe<&2, Cv.Val>, fin, n4, Equal.cong(Maybe<&2, Cv.Val>, Maybe<&2, Cv.Val>, y => LS.sv.orm(y, cur), all, LS.sv.orm(LS.sv.orm(lr, lq), lp), e_all))))))
