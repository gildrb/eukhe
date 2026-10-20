# proof_child_env: the G3 laws (laws/child_env.bend, no credential
# reaches a child) of the model in bend/child_env.bend.
#
# The filter keeps a variable exactly when its name passes. So every
# variable of the child passes (`pce.all` holds of the filtered list, and
# a member of a list of which `pce.all` holds passes), and every member of
# the merged list that passes is a member of the child. What remains is
# logic on the test: with an empty keep list a name passes only when it is
# not a credential; a credential name passes only when the keep list holds
# it and it is no provider name; a name that is not a credential passes,
# and so does a kept name that is no provider name.
#
# A recursive proof takes the value it inspects as a parameter (Bend
# matches only parameters), with an equation that names it.

import Base
import ./child_env.bend as Env

# Logic
# -----

def pce.BD(b: Bool, t: Type, f: Type) -> Type:
  match b:
    case True{}:
      t
    case False{}:
      f

def pce.absurd(-A: Type, e: {True{} == False{} : Bool}) -> A:
  %e : pce.BD(_, Unit, A)
  Unit{}

def pce.absurdF(-A: Type, e: {False{} == True{} : Bool}) -> A:
  %e : pce.BD(_, A, Unit)
  Unit{}

def pce.and_l(a: Bool, +b: Bool, h: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      pce.absurdF({False{} == True{} : Bool}, h)

def pce.and_r(a: Bool, +b: Bool, h: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      h
    case False{}:
      pce.absurdF({b == True{} : Bool}, h)

def pce.not_t(b: Bool, h: {Bool.not(b) == True{} : Bool}) -> {b == False{} : Bool}:
  match b:
    case True{}:
      pce.absurdF({True{} == False{} : Bool}, h)
    case False{}:
      {==}

def pce.or_false(a: Bool, h: {Bool.or(a, False{}) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      pce.absurdF({False{} == True{} : Bool}, h)

# The filter
# ----------

# every variable of xs passes
def pce.all(+reg: List<&2, String>, +ks: List<&2, String>, xs: List<&2, Env.Var>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case +v <> rest:
      Bool.and(Env.passes(reg, ks, Env.Var.name(v)), pce.all(reg, ks, rest))

def pce.put_all(+reg: List<&2, String>, +ks: List<&2, String>, b: Bool, +h: Env.Var, +r: List<&2, Env.Var>, e: {Env.passes(reg, ks, Env.Var.name(h)) == b : Bool}, ih: {pce.all(reg, ks, r) == True{} : Bool}) -> {pce.all(reg, ks, Env.keep.put(b, h, r)) == True{} : Bool}:
  match b:
    case True{}:
      %Equal.sym(Bool, Env.passes(reg, ks, Env.Var.name(h)), True{}, e) : {Bool.and(_, pce.all(reg, ks, r)) == True{} : Bool}
      ih
    case False{}:
      ih

# every variable the filter keeps passes
def pce.keep_all(+reg: List<&2, String>, +ks: List<&2, String>, xs: List<&2, Env.Var>) -> {pce.all(reg, ks, Env.keep(reg, ks, xs)) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +h <> +t:
      pce.put_all(reg, ks, Env.passes(reg, ks, Env.Var.name(h)), h, Env.keep(reg, ks, t), {==}, pce.keep_all(reg, ks, t))

# a member of a list of which pce.all holds passes
def pce.in_all(+reg: List<&2, String>, +ks: List<&2, String>, xs: List<&2, Env.Var>, +v: Env.Var, i: Env.In(v, xs), a: {pce.all(reg, ks, xs) == True{} : Bool}) -> {Env.passes(reg, ks, Env.Var.name(v)) == True{} : Bool}:
  match xs:
    case Nil{}:
      match i:
    case +h <> +t:
      match i:
        case Inl{eq}:
          %Equal.sym(Env.Var, v, h, eq) : {Env.passes(reg, ks, Env.Var.name(_)) == True{} : Bool}
          pce.and_l(Env.passes(reg, ks, Env.Var.name(h)), pce.all(reg, ks, t), a)
        case Inr{it}:
          pce.in_all(reg, ks, t, v, it, pce.and_r(Env.passes(reg, ks, Env.Var.name(h)), pce.all(reg, ks, t), a))

# every variable of the child passes
def pce.child_passes(+reg: List<&2, String>, +ks: List<&2, String>, +xs: List<&2, Env.Var>, +v: Env.Var, i: Env.In(v, Env.keep(reg, ks, xs))) -> {Env.passes(reg, ks, Env.Var.name(v)) == True{} : Bool}:
  pce.in_all(reg, ks, Env.keep(reg, ks, xs), v, i, pce.keep_all(reg, ks, xs))

def pce.in_put(b: Bool, +h: Env.Var, +r: List<&2, Env.Var>, +v: Env.Var, i: Env.In(v, r)) -> Env.In(v, Env.keep.put(b, h, r)):
  match b:
    case True{}:
      Inr{i}
    case False{}:
      i

# a member of xs that passes is a member of the filtered list
def pce.in_keep(+reg: List<&2, String>, +ks: List<&2, String>, xs: List<&2, Env.Var>, +v: Env.Var, i: Env.In(v, xs), p: {Env.passes(reg, ks, Env.Var.name(v)) == True{} : Bool}) -> Env.In(v, Env.keep(reg, ks, xs)):
  match xs:
    case Nil{}:
      match i:
    case +h <> +t:
      match i:
        case Inl{eq}:
          %eq : Env.In(v, Env.keep.put(Env.passes(reg, ks, Env.Var.name(_)), _, Env.keep(reg, ks, t)))
          %Equal.sym(Bool, Env.passes(reg, ks, Env.Var.name(v)), True{}, p) : Env.In(v, Env.keep.put(_, v, Env.keep(reg, ks, t)))
          Inl{{==}}
        case Inr{it}:
          pce.in_put(Env.passes(reg, ks, Env.Var.name(h)), h, Env.keep(reg, ks, t), v, pce.in_keep(reg, ks, t, v, it, p))

# The test
# --------

# a credential name passes only when kept and no provider name
def pce.only(c: Bool, +l: Bool, +r: Bool, e: {c == True{} : Bool}, +p: {Bool.or(Bool.not(c), Bool.and(l, Bool.not(r))) == True{} : Bool}) -> ({l == True{} : Bool} & {r == False{} : Bool}):
  match c:
    case True{}:
      (pce.and_l(l, Bool.not(r), p), pce.not_t(r, pce.and_r(l, Bool.not(r), p)))
    case False{}:
      pce.absurdF(({l == True{} : Bool} & {r == False{} : Bool}), e)

# a name that is not a credential passes
def pce.rest(c: Bool, +x: Bool, e: {c == False{} : Bool}) -> {Bool.or(Bool.not(c), x) == True{} : Bool}:
  match c:
    case True{}:
      pce.absurd({Bool.or(False{}, x) == True{} : Bool}, e)
    case False{}:
      {==}

# a kept name that is no provider name passes
def pce.kept(x: Bool, l: Bool, r: Bool, kl: {l == True{} : Bool}, kr: {r == False{} : Bool}) -> {Bool.or(x, Bool.and(l, Bool.not(r))) == True{} : Bool}:
  match x:
    case True{}:
      {==}
    case False{}:
      match l:
        case True{}:
          match r:
            case True{}:
              pce.absurd({Bool.not(True{}) == True{} : Bool}, kr)
            case False{}:
              {==}
        case False{}:
          pce.absurdF({Bool.and(False{}, Bool.not(r)) == True{} : Bool}, kl)

# The laws
# --------

def pce.env_drops_credentials(+reg: List<&2, String>, base: List<&2, Env.Var>, over: List<&2, Env.Var>, +v: Env.Var, i: Env.In(v, Env.child(reg, Nil{}, base, over))) -> {Env.cred(reg, Env.Var.name(v)) == False{} : Bool}:
  +n = Env.Var.name(v)
  pce.not_t(Env.cred(reg, n), pce.or_false(Bool.not(Env.cred(reg, n)), pce.child_passes(reg, Nil{}, Env.merge(base, over), v, i)))

def pce.env_kernel_keeps_only_listed(+reg: List<&2, String>, +keep: List<&2, String>, base: List<&2, Env.Var>, over: List<&2, Env.Var>, +v: Env.Var, i: Env.In(v, Env.child(reg, keep, base, over)), c: {Env.cred(reg, Env.Var.name(v)) == True{} : Bool}) -> ({Env.listed(keep, Env.Var.name(v)) == True{} : Bool} & {Env.registered(reg, Env.Var.name(v)) == False{} : Bool}):
  +n = Env.Var.name(v)
  pce.only(Env.cred(reg, n), Env.listed(keep, n), Env.registered(reg, n), c, pce.child_passes(reg, keep, Env.merge(base, over), v, i))

def pce.env_keeps_the_rest(+reg: List<&2, String>, +keep: List<&2, String>, base: List<&2, Env.Var>, over: List<&2, Env.Var>, +v: Env.Var, i: Env.In(v, Env.merge(base, over)), c: {Env.cred(reg, Env.Var.name(v)) == False{} : Bool}) -> Env.In(v, Env.child(reg, keep, base, over)):
  +n = Env.Var.name(v)
  pce.in_keep(reg, keep, Env.merge(base, over), v, i, pce.rest(Env.cred(reg, n), Bool.and(Env.listed(keep, n), Bool.not(Env.registered(reg, n))), c))

def pce.env_keeps_listed(+reg: List<&2, String>, +keep: List<&2, String>, base: List<&2, Env.Var>, over: List<&2, Env.Var>, +v: Env.Var, i: Env.In(v, Env.merge(base, over)), k: {Env.listed(keep, Env.Var.name(v)) == True{} : Bool}, r: {Env.registered(reg, Env.Var.name(v)) == False{} : Bool}) -> Env.In(v, Env.child(reg, keep, base, over)):
  +n = Env.Var.name(v)
  pce.in_keep(reg, keep, Env.merge(base, over), v, i, pce.kept(Bool.not(Env.cred(reg, n)), Env.listed(keep, n), Env.registered(reg, n), k, r))
