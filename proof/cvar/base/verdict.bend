# eukhe: lemmas of the proofs of the cvar verdict laws: the verdict on a
# set against the laws' counting rule, case by case on the declaration,
# the layer and the type test.

import Base
import ../../../bend/cvar.bend as Cv
import ../../../laws/cvar/resolution.bend as Cvar
import ../base.bend as LA
import ./resolve.bend as LR

def ck.ty_fine(b: Bool) -> {Cvar.spec_ck_fine(Cv.check.ty(b)) == b : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def ck.ty_undeclared(b: Bool) -> {Cvar.spec_ck_undeclared(Cv.check.ty(b)) == False{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def ck.ty_global(b: Bool) -> {Cvar.spec_ck_global(Cv.check.ty(b)) == False{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# the verdict is valid exactly when the set counts in the layer
def ck.fine_at(m: Maybe<&2, Cv.Decl>, l: Cv.Layer, +i: Nat, +v: Cv.Val) -> {Cvar.spec_ck_fine(Cv.check.at(m, l, Cv.Bind{i, v})) == Cvar.spec_counts.at(m, l, v) : Bool}:
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
                  %Equal.sym(Bool, Cv.Ty.eq(Cv.Val.ty(v), t), Cvar.spec_typed(v, t), LR.rs.ty_eq(v, t)) : {Cvar.spec_ck_fine(Cv.check.ty(_)) == Cvar.spec_typed(v, t) : Bool}
                  ck.ty_fine(Cvar.spec_typed(v, t))
                case Cv.Agent{}:
                  LR.rs.and_false(Cvar.spec_typed(v, t))
            case Cv.Local{}:
              match l:
                case Cv.Config{}:
                  %Equal.sym(Bool, Cv.Ty.eq(Cv.Val.ty(v), t), Cvar.spec_typed(v, t), LR.rs.ty_eq(v, t)) : {Cvar.spec_ck_fine(Cv.check.ty(_)) == Cvar.spec_typed(v, t) : Bool}
                  ck.ty_fine(Cvar.spec_typed(v, t))
                case Cv.Agent{}:
                  %Equal.sym(Bool, Cv.Ty.eq(Cv.Val.ty(v), t), Cvar.spec_typed(v, t), LR.rs.ty_eq(v, t)) : {Cvar.spec_ck_fine(Cv.check.ty(_)) == Bool.and(Cvar.spec_typed(v, t), True{}) : Bool}
                  Equal.trans(Bool, Cvar.spec_ck_fine(Cv.check.ty(Cvar.spec_typed(v, t))), Cvar.spec_typed(v, t), Bool.and(Cvar.spec_typed(v, t), True{}), ck.ty_fine(Cvar.spec_typed(v, t)), LR.rs.and_true(Cvar.spec_typed(v, t)))

def ck.undeclared_at(m: Maybe<&2, Cv.Decl>, l: Cv.Layer, +i: Nat, +v: Cv.Val) -> {Cvar.spec_ck_undeclared(Cv.check.at(m, l, Cv.Bind{i, v})) == Bool.not(Maybe.is_some(&2, Cv.Decl, m)) : Bool}:
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
                  ck.ty_undeclared(Cv.Ty.eq(Cv.Val.ty(v), t))
                case Cv.Agent{}:
                  {==}
            case Cv.Local{}:
              match l:
                case Cv.Config{}:
                  ck.ty_undeclared(Cv.Ty.eq(Cv.Val.ty(v), t))
                case Cv.Agent{}:
                  ck.ty_undeclared(Cv.Ty.eq(Cv.Val.ty(v), t))

def ck.global_at(m: Maybe<&2, Cv.Decl>, l: Cv.Layer, +i: Nat, +v: Cv.Val) -> {Cvar.spec_ck_global(Cv.check.at(m, l, Cv.Bind{i, v})) == Cvar.spec_global_in(l, m) : Bool}:
  match m:
    case None{}:
      match l:
        case Cv.Config{}:
          {==}
        case Cv.Agent{}:
          {==}
    case Some{d}:
      match d:
        case Cv.Decl{j, +t, c, p, r, w}:
          match c:
            case Cv.Global{}:
              match l:
                case Cv.Config{}:
                  ck.ty_global(Cv.Ty.eq(Cv.Val.ty(v), t))
                case Cv.Agent{}:
                  {==}
            case Cv.Local{}:
              match l:
                case Cv.Config{}:
                  ck.ty_global(Cv.Ty.eq(Cv.Val.ty(v), t))
                case Cv.Agent{}:
                  ck.ty_global(Cv.Ty.eq(Cv.Val.ty(v), t))

def ck.some_or(h: Bool, -v: Cv.Val) -> {Maybe.is_some(&2, Cv.Val, Cvar.spec_latest.or(None{}, h, v)) == h : Bool}:
  match h:
    case True{}:
      {==}
    case False{}:
      {==}

# Toggles
# -------

def tg.If(m: Maybe<&2, Cv.Val>, G: Type) -> Type:
  match m:
    case None{}:
      Unit
    case Some{y}:
      G

def tg.none_some(-y: Cv.Val, -G: Type, e: {None{} == Some{y} : Maybe<&2, Cv.Val>}) -> G:
  %e : tg.If(_, G)
  Unit{}

# a declared value cannot be the value of an undeclared cvar
def tg.undeclared(+ds: List<&2, Cv.Decl>, +cfg: List<&2, Cv.Bind>, +fam: List<&2, Cv.Ag>, +x: Nat, -y: Cv.Val, -G: Type, em: {Cv.find(ds, x) == None{} : Maybe<&2, Cv.Decl>}, val: {Cv.value(ds, cfg, fam, x) == Some{y} : Maybe<&2, Cv.Val>}) -> G:
  +e = Equal.cong(Maybe<&2, Cv.Decl>, Maybe<&2, Cv.Val>, m => Cv.value.at(m, ds, cfg, fam, x), Cv.find(ds, x), None{}, em)
  tg.none_some(y, G, Equal.trans(Maybe<&2, Cv.Val>, None{}, Cv.value(ds, cfg, fam, x), Some{y}, Equal.sym(Maybe<&2, Cv.Val>, Cv.value(ds, cfg, fam, x), None{}, e), val))

# the verdict of a toggle the layer allows is the flip of the value
def tg.allowed(m: Maybe<&2, Cv.Decl>, l: Cv.Layer, +ds: List<&2, Cv.Decl>, +cfg: List<&2, Cv.Bind>, +fam: List<&2, Cv.Ag>, +x: Nat, +y: Cv.Val, em: {Cv.find(ds, x) == m : Maybe<&2, Cv.Decl>}, allowed: {Cvar.spec_global_in(l, m) == False{} : Bool}, val: {Cv.value(ds, cfg, fam, x) == Some{y} : Maybe<&2, Cv.Val>}) -> {Cv.tog.at(m, l, ds, cfg, fam, x) == Cv.tog.flip(Cv.flip(x, Some{y})) : Cv.Tog}:
  match m:
    case None{}:
      tg.undeclared(ds, cfg, fam, x, y, {Cv.tog.at(None{}, l, ds, cfg, fam, x) == Cv.tog.flip(Cv.flip(x, Some{y})) : Cv.Tog}, em, val)
    case Some{d}:
      match d:
        case Cv.Decl{j, t, c, p, r, w}:
          match c:
            case Cv.Global{}:
              match l:
                case Cv.Config{}:
                  %Equal.sym(Maybe<&2, Cv.Val>, Cv.value(ds, cfg, fam, x), Some{y}, val) : {Cv.tog.flip(Cv.flip(x, _)) == Cv.tog.flip(Cv.flip(x, Some{y})) : Cv.Tog}
                  {==}
                case Cv.Agent{}:
                  LA.pv.absurdF({Cv.TgGlobal{} == Cv.tog.flip(Cv.flip(x, Some{y})) : Cv.Tog}, Equal.sym(Bool, True{}, False{}, allowed))
            case Cv.Local{}:
              match l:
                case Cv.Config{}:
                  %Equal.sym(Maybe<&2, Cv.Val>, Cv.value(ds, cfg, fam, x), Some{y}, val) : {Cv.tog.flip(Cv.flip(x, _)) == Cv.tog.flip(Cv.flip(x, Some{y})) : Cv.Tog}
                  {==}
                case Cv.Agent{}:
                  %Equal.sym(Maybe<&2, Cv.Val>, Cv.value(ds, cfg, fam, x), Some{y}, val) : {Cv.tog.flip(Cv.flip(x, _)) == Cv.tog.flip(Cv.flip(x, Some{y})) : Cv.Tog}
                  {==}
