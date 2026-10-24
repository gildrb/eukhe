# eukhe: lemmas the proofs of the cvar resolution laws share: the model's
# lookup, validity and layers equal the laws' specs (each a case split on
# the stage's own test, passed in as a parameter), and a default carried
# down a family chain is the default of the chain's layered value.

import Base
import ../../../bend/cvar.bend as Cv
import ../../../laws/cvar.bend as Cvar
import ../base.bend as LA

# Lookup and validity
# -------------------

def re.find_go(b: Bool, +d: Cv.Decl, +rest: List<&2, Cv.Decl>, +x: Nat, ih: {Cv.find(rest, x) == Cvar.spec_find(rest, x) : Maybe<&2, Cv.Decl>}) -> {Cv.find.go(d <> rest, x, b) == Cvar.spec_find.pick(b, d, Cvar.spec_find(rest, x)) : Maybe<&2, Cv.Decl>}:
  match b:
    case True{}:
      {==}
    case False{}:
      ih

# the model's declaration of x is the spec's
def re.find(ds: List<&2, Cv.Decl>, +x: Nat) -> {Cv.find(ds, x) == Cvar.spec_find(ds, x) : Maybe<&2, Cv.Decl>}:
  match ds:
    case Nil{}:
      {==}
    case Cv.Decl{+i, +t, +c, +p, +r, +v} <> +rest:
      re.find_go(Nat.is_eq(i, x), Cv.Decl{i, t, c, p, r, v}, rest, x, re.find(rest, x))

# the model's type test is the spec's
def re.ty(v: Cv.Val, t: Cv.Ty) -> {Cv.Ty.eq(Cv.Val.ty(v), t) == Cvar.spec_typed(v, t) : Bool}:
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

def re.valid_at(m: Maybe<&2, Cv.Decl>, l: Cv.Layer, +i: Nat, +v: Cv.Val) -> {Cv.valid.at(m, l, Cv.Bind{i, v}) == Cvar.spec_valid.at(m, l, v) : Bool}:
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
                  re.ty(v, t)
                case Cv.Agent{}:
                  {==}
            case Cv.Local{}:
              match l:
                case Cv.Config{}:
                  re.ty(v, t)
                case Cv.Agent{}:
                  re.ty(v, t)

# the model's validity of a set is the spec's
def re.valid(+ds: List<&2, Cv.Decl>, +l: Cv.Layer, s: Cv.Bind) -> {Cv.valid(ds, l, s) == Cvar.spec_valid(ds, l, s) : Bool}:
  match s:
    case Cv.Bind{+i, +v}:
      %re.find(ds, i) : {Cv.valid.at(Cv.find(ds, i), l, Cv.Bind{i, v}) == Cvar.spec_valid.at(_, l, v) : Bool}
      re.valid_at(Cv.find(ds, i), l, i, v)

# Layers
# ------

def re.layer_go(b: Bool, +i: Nat, +v: Cv.Val, +rest: List<&2, Cv.Bind>, +ds: List<&2, Cv.Decl>, +l: Cv.Layer, +x: Nat, +cur: Maybe<&2, Cv.Val>,
  hs: {Cv.layer(rest, ds, l, x, Some{v}) == Cvar.spec_last(rest, ds, l, x, Some{v}) : Maybe<&2, Cv.Val>},
  hc: {Cv.layer(rest, ds, l, x, cur) == Cvar.spec_last(rest, ds, l, x, cur) : Maybe<&2, Cv.Val>})
  -> {Cv.layer.go(Cv.Bind{i, v} <> rest, ds, l, x, cur, b) == Cvar.spec_last(rest, ds, l, x, Cvar.spec_last.pick(b, v, cur)) : Maybe<&2, Cv.Val>}:
  match b:
    case True{}:
      hs
    case False{}:
      hc

# a layer of the model is the spec's last set that counts
def re.layer(ss: List<&2, Cv.Bind>, +ds: List<&2, Cv.Decl>, +l: Cv.Layer, +x: Nat, +cur: Maybe<&2, Cv.Val>) -> {Cv.layer(ss, ds, l, x, cur) == Cvar.spec_last(ss, ds, l, x, cur) : Maybe<&2, Cv.Val>}:
  match ss:
    case Nil{}:
      {==}
    case Cv.Bind{+i, +v} <> +rest:
      %re.valid(ds, l, Cv.Bind{i, v}) : {Cv.layer(Cv.Bind{i, v} <> rest, ds, l, x, cur) == Cvar.spec_last(rest, ds, l, x, Cvar.spec_last.pick(Bool.and(Nat.is_eq(i, x), _), v, cur)) : Maybe<&2, Cv.Val>}
      %LA.pv.hit_and(Nat.is_eq(i, x), ds, l, Cv.Bind{i, v}) : {Cv.layer(Cv.Bind{i, v} <> rest, ds, l, x, cur) == Cvar.spec_last(rest, ds, l, x, Cvar.spec_last.pick(_, v, cur)) : Maybe<&2, Cv.Val>}
      re.layer_go(Cv.hit.when(Nat.is_eq(i, x), ds, l, Cv.Bind{i, v}), i, v, rest, ds, l, x, cur, re.layer(rest, ds, l, x, Some{v}), re.layer(rest, ds, l, x, cur))

# the model's family chain is the spec's
def re.chainm(fam: List<&2, Cv.Ag>, +ds: List<&2, Cv.Decl>, +x: Nat, +cur: Maybe<&2, Cv.Val>) -> {Cv.chainm(fam, ds, x, cur) == Cvar.spec_agents(fam, ds, x, cur) : Maybe<&2, Cv.Val>}:
  match fam:
    case Nil{}:
      {==}
    case Cv.Ag{+p, +s} <> +rest:
      +lp = Cv.layer(p, ds, Cv.Agent{}, x, cur)
      %re.layer(p, ds, Cv.Agent{}, x, cur) : {Cv.chainm(rest, ds, x, Cv.layer(s, ds, Cv.Agent{}, x, lp)) == Cvar.spec_agents(rest, ds, x, Cvar.spec_last(s, ds, Cv.Agent{}, x, _)) : Maybe<&2, Cv.Val>}
      %re.layer(s, ds, Cv.Agent{}, x, lp) : {Cv.chainm(rest, ds, x, Cv.layer(s, ds, Cv.Agent{}, x, lp)) == Cvar.spec_agents(rest, ds, x, _) : Maybe<&2, Cv.Val>}
      re.chainm(rest, ds, x, Cv.layer(s, ds, Cv.Agent{}, x, lp))

# the model's layered value is the spec's
def re.layered(+ds: List<&2, Cv.Decl>, +cfg: List<&2, Cv.Bind>, +fam: List<&2, Cv.Ag>, +x: Nat) -> {Cv.layered(ds, cfg, fam, x) == Cvar.spec_layered(ds, cfg, fam, x) : Maybe<&2, Cv.Val>}:
  %re.layer(cfg, ds, Cv.Config{}, x, None{}) : {Cv.chainm(fam, ds, x, Cv.layer(cfg, ds, Cv.Config{}, x, None{})) == Cvar.spec_agents(fam, ds, x, _) : Maybe<&2, Cv.Val>}
  re.chainm(fam, ds, x, Cv.layer(cfg, ds, Cv.Config{}, x, None{}))

# Defaults down a chain
# ---------------------

def re.pick_default(ok: Bool, +v: Cv.Val, +c: Maybe<&2, Cv.Val>, +b: Cv.Val) -> {Maybe.default(&2, Cv.Val, Cvar.spec_last.pick(ok, v, c), b) == Maybe.default(&2, Cv.Val, Cvar.spec_last.pick(ok, v, None{}), Maybe.default(&2, Cv.Val, c, b)) : Cv.Val}:
  match ok:
    case True{}:
      {==}
    case False{}:
      {==}

# the last set over c, defaulted to b, is the last set over nothing,
# defaulted to c's default
def re.last_default(ss: List<&2, Cv.Bind>, +ds: List<&2, Cv.Decl>, +l: Cv.Layer, +x: Nat, +c: Maybe<&2, Cv.Val>, +b: Cv.Val) -> {Maybe.default(&2, Cv.Val, Cvar.spec_last(ss, ds, l, x, c), b) == Maybe.default(&2, Cv.Val, Cvar.spec_last(ss, ds, l, x, None{}), Maybe.default(&2, Cv.Val, c, b)) : Cv.Val}:
  match ss:
    case Nil{}:
      {==}
    case Cv.Bind{+i, +v} <> +rest:
      +ok = Bool.and(Nat.is_eq(i, x), Cvar.spec_valid(ds, l, Cv.Bind{i, v}))
      +pc = Cvar.spec_last.pick(ok, v, c)
      +pn = Cvar.spec_last.pick(ok, v, None{})
      +d = Maybe.default(&2, Cv.Val, c, b)
      +sn = Cvar.spec_last(rest, ds, l, x, None{})
      +lhs = Maybe.default(&2, Cv.Val, Cvar.spec_last(rest, ds, l, x, pc), b)
      +mid = Maybe.default(&2, Cv.Val, sn, Maybe.default(&2, Cv.Val, pc, b))
      +far = Maybe.default(&2, Cv.Val, sn, Maybe.default(&2, Cv.Val, pn, d))
      +rhs = Maybe.default(&2, Cv.Val, Cvar.spec_last(rest, ds, l, x, pn), d)
      Equal.trans(Cv.Val, lhs, mid, rhs, re.last_default(rest, ds, l, x, pc, b),
        Equal.trans(Cv.Val, mid, far, rhs,
          Equal.cong(Cv.Val, Cv.Val, y => Maybe.default(&2, Cv.Val, sn, y), Maybe.default(&2, Cv.Val, pc, b), Maybe.default(&2, Cv.Val, pn, d), re.pick_default(ok, v, c, b)),
          Equal.sym(Cv.Val, rhs, far, re.last_default(rest, ds, l, x, pn, d))))

# the same for the model's layers
def re.layer_default(+ss: List<&2, Cv.Bind>, +ds: List<&2, Cv.Decl>, +l: Cv.Layer, +x: Nat, +c: Maybe<&2, Cv.Val>, +b: Cv.Val) -> {Maybe.default(&2, Cv.Val, Cv.layer(ss, ds, l, x, c), b) == Maybe.default(&2, Cv.Val, Cv.layer(ss, ds, l, x, None{}), Maybe.default(&2, Cv.Val, c, b)) : Cv.Val}:
  %Equal.sym(Maybe<&2, Cv.Val>, Cv.layer(ss, ds, l, x, c), Cvar.spec_last(ss, ds, l, x, c), re.layer(ss, ds, l, x, c)) : {Maybe.default(&2, Cv.Val, _, b) == Maybe.default(&2, Cv.Val, Cv.layer(ss, ds, l, x, None{}), Maybe.default(&2, Cv.Val, c, b)) : Cv.Val}
  %Equal.sym(Maybe<&2, Cv.Val>, Cv.layer(ss, ds, l, x, None{}), Cvar.spec_last(ss, ds, l, x, None{}), re.layer(ss, ds, l, x, None{})) : {Maybe.default(&2, Cv.Val, Cvar.spec_last(ss, ds, l, x, c), b) == Maybe.default(&2, Cv.Val, _, Maybe.default(&2, Cv.Val, c, b)) : Cv.Val}
  re.last_default(ss, ds, l, x, c, b)

# one agent on a defaulted value: its layers on the value, defaulted
def re.over(+p: List<&2, Cv.Bind>, +s: List<&2, Cv.Bind>, +ds: List<&2, Cv.Decl>, +x: Nat, +c: Maybe<&2, Cv.Val>, +b: Cv.Val) -> {Cv.over(ds, Cv.Ag{p, s}, x, Maybe.default(&2, Cv.Val, c, b)) == Maybe.default(&2, Cv.Val, Cv.layer(s, ds, Cv.Agent{}, x, Cv.layer(p, ds, Cv.Agent{}, x, c)), b) : Cv.Val}:
  +d = Maybe.default(&2, Cv.Val, c, b)
  +pn = Cv.layer(p, ds, Cv.Agent{}, x, None{})
  +pc = Cv.layer(p, ds, Cv.Agent{}, x, c)
  +sn = Cv.layer(s, ds, Cv.Agent{}, x, None{})
  +m = Maybe.default(&2, Cv.Val, sn, Maybe.default(&2, Cv.Val, pn, d))
  +m2 = Maybe.default(&2, Cv.Val, sn, Maybe.default(&2, Cv.Val, pc, b))
  +lhs = Maybe.default(&2, Cv.Val, Cv.layer(s, ds, Cv.Agent{}, x, pn), d)
  +rhs = Maybe.default(&2, Cv.Val, Cv.layer(s, ds, Cv.Agent{}, x, pc), b)
  Equal.trans(Cv.Val, lhs, m, rhs, re.layer_default(s, ds, Cv.Agent{}, x, pn, d),
    Equal.sym(Cv.Val, rhs, m,
      Equal.trans(Cv.Val, rhs, m2, m, re.layer_default(s, ds, Cv.Agent{}, x, pc, b),
        Equal.cong(Cv.Val, Cv.Val, y => Maybe.default(&2, Cv.Val, sn, y), Maybe.default(&2, Cv.Val, pc, b), Maybe.default(&2, Cv.Val, pn, d), re.layer_default(p, ds, Cv.Agent{}, x, c, b)))))

# a chain on a defaulted value is the chain's layered value, defaulted
def re.chain(fam: List<&2, Cv.Ag>, +ds: List<&2, Cv.Decl>, +x: Nat, +c: Maybe<&2, Cv.Val>, +b: Cv.Val) -> {Cv.chain(fam, ds, x, Maybe.default(&2, Cv.Val, c, b)) == Maybe.default(&2, Cv.Val, Cv.chainm(fam, ds, x, c), b) : Cv.Val}:
  match fam:
    case Nil{}:
      {==}
    case Cv.Ag{+p, +s} <> +rest:
      +n = Cv.layer(s, ds, Cv.Agent{}, x, Cv.layer(p, ds, Cv.Agent{}, x, c))
      %Equal.sym(Cv.Val, Cv.over(ds, Cv.Ag{p, s}, x, Maybe.default(&2, Cv.Val, c, b)), Maybe.default(&2, Cv.Val, n, b), re.over(p, s, ds, x, c, b)) : {Cv.chain(rest, ds, x, _) == Maybe.default(&2, Cv.Val, Cv.chainm(rest, ds, x, n), b) : Cv.Val}
      re.chain(rest, ds, x, n, b)

def re.value_at(m: Maybe<&2, Cv.Decl>, +ds: List<&2, Cv.Decl>, +cfg: List<&2, Cv.Bind>, +fam: List<&2, Cv.Ag>, +x: Nat) -> {Cv.value.at(m, ds, cfg, fam, x) == Cvar.spec_value.at(m, Cv.layered(ds, cfg, fam, x)) : Maybe<&2, Cv.Val>}:
  match m:
    case None{}:
      {==}
    case Some{d}:
      match d:
        case Cv.Decl{i, t, c, p, r, +v}:
          +lc = Cv.layer(cfg, ds, Cv.Config{}, x, None{})
          Equal.cong(Cv.Val, Maybe<&2, Cv.Val>, y => Some{y}, Cv.chain(fam, ds, x, Maybe.default(&2, Cv.Val, lc, v)), Maybe.default(&2, Cv.Val, Cv.chainm(fam, ds, x, lc), v), re.chain(fam, ds, x, lc, v))

# the model's value is the spec's
def re.value(+ds: List<&2, Cv.Decl>, +cfg: List<&2, Cv.Bind>, +fam: List<&2, Cv.Ag>, +x: Nat) -> {Cv.value(ds, cfg, fam, x) == Cvar.spec_value(ds, cfg, fam, x) : Maybe<&2, Cv.Val>}:
  %re.find(ds, x) : {Cv.value.at(Cv.find(ds, x), ds, cfg, fam, x) == Cvar.spec_value.at(_, Cvar.spec_layered(ds, cfg, fam, x)) : Maybe<&2, Cv.Val>}
  %re.layered(ds, cfg, fam, x) : {Cv.value.at(Cv.find(ds, x), ds, cfg, fam, x) == Cvar.spec_value.at(Cv.find(ds, x), _) : Maybe<&2, Cv.Val>}
  re.value_at(Cv.find(ds, x), ds, cfg, fam, x)
