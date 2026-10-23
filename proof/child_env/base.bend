# eukhe: lemmas the proofs of area child_env share

import Base
import ../../bend/child_env.bend as Env
import ../../bend/ffi_child_env.bend as FEnv
import ../../bend/wire.bend as Wr
import ../../laws/child_env.bend as ChildEnv
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../base/logic/bool.bend as LLogicBool
import ../base/wire.bend as LWire

# ---- child_env ----

# proof_child_env: the G3 laws (LAWS.bend section child_env, no credential
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
# The model's test runs its checks one by one (`Env.passes`); it equals
# the test of the laws (`pce.passes_eq`). The overlay over the base: a
# member of the overlay or of the filtered base is a member of the
# concatenation and back (`pce.app_in_l`, `pce.app_in_r`, `pce.app_in`);
# a member of the base reaches the filtered base exactly when the overlay
# does not name it (`pce.under_in`, `pce.under_out`).
#
# A recursive proof takes the value it inspects as a parameter (Bend
# matches only parameters), with an equation that names it.

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

# The test of the model is the test of the laws
# ---------------------------------------------

def pce.and_f(k: Bool) -> {False{} == Bool.and(k, False{}) : Bool}:
  match k:
    case True{}:
      {==}
    case False{}:
      {==}

def pce.and_t2(k: Bool) -> {k == Bool.and(k, True{}) : Bool}:
  match k:
    case True{}:
      {==}
    case False{}:
      {==}

def pce.pat_eq(m: Bool, +keep: List<&2, String>, +n: String) -> {Env.passes.pat(m, keep, n) == Bool.or(Bool.not(m), Bool.and(Env.listed(keep, n), True{})) : Bool}:
  match m:
    case True{}:
      pce.and_t2(Env.listed(keep, n))
    case False{}:
      {==}

def pce.reg_eq(l: Bool, +u: String, +keep: List<&2, String>, +n: String) -> {Env.passes.reg(l, u, keep, n) == Bool.or(Bool.not(Bool.or(l, Env.matched(Env.patterns(), u))), Bool.and(Env.listed(keep, n), Bool.not(l))) : Bool}:
  match l:
    case True{}:
      pce.and_f(Env.listed(keep, n))
    case False{}:
      pce.pat_eq(Env.matched(Env.patterns(), u), keep, n)

# a name passes exactly when it is no credential, or kept and no provider
# name
def pce.passes_eq(+reg: List<&2, String>, +keep: List<&2, String>, +n: String) -> {Env.passes(reg, keep, n) == Bool.or(Bool.not(Env.cred(reg, n)), Bool.and(Env.listed(keep, n), Bool.not(Env.registered(reg, n)))) : Bool}:
  pce.reg_eq(Env.listed(reg, Env.up(n)), Env.up(n), keep, n)

def pce.spec_of(+reg: List<&2, String>, +keep: List<&2, String>, +n: String, h: {Env.passes(reg, keep, n) == True{} : Bool}) -> {Bool.or(Bool.not(Env.cred(reg, n)), Bool.and(Env.listed(keep, n), Bool.not(Env.registered(reg, n)))) == True{} : Bool}:
  Equal.trans(Bool, Bool.or(Bool.not(Env.cred(reg, n)), Bool.and(Env.listed(keep, n), Bool.not(Env.registered(reg, n)))), Env.passes(reg, keep, n), True{}, Equal.sym(Bool, Env.passes(reg, keep, n), Bool.or(Bool.not(Env.cred(reg, n)), Bool.and(Env.listed(keep, n), Bool.not(Env.registered(reg, n)))), pce.passes_eq(reg, keep, n)), h)

def pce.of_spec(+reg: List<&2, String>, +keep: List<&2, String>, +n: String, h: {Bool.or(Bool.not(Env.cred(reg, n)), Bool.and(Env.listed(keep, n), Bool.not(Env.registered(reg, n)))) == True{} : Bool}) -> {Env.passes(reg, keep, n) == True{} : Bool}:
  Equal.trans(Bool, Env.passes(reg, keep, n), Bool.or(Bool.not(Env.cred(reg, n)), Bool.and(Env.listed(keep, n), Bool.not(Env.registered(reg, n)))), True{}, pce.passes_eq(reg, keep, n), h)

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

def pce.or_cons(-h: Env.Var, -t: List<&2, Env.Var>, -ys: List<&2, Env.Var>, -v: Env.Var, o: Or(Env.In(v, t), Env.In(v, ys))) -> Or(Env.In(v, h <> t), Env.In(v, ys)):
  match o:
    case Inl{a}:
      Inl{Inr{a}}
    case Inr{b}:
      Inr{b}

def pce.app_in(xs: List<&2, Env.Var>, +ys: List<&2, Env.Var>, +v: Env.Var, i: Env.In(v, List.append(&2, Env.Var, xs, ys))) -> Or(Env.In(v, xs), Env.In(v, ys)):
  match xs:
    case Nil{}:
      Inr{i}
    case +h <> +t:
      match i:
        case Inl{eq}:
          Inl{Inl{eq}}
        case Inr{it}:
          pce.or_cons(h, t, ys, v, pce.app_in(t, ys, v, it))

# the spec's name test is the model's
def pce.named_eq(+n: String, xs: List<&2, Env.Var>) -> {ChildEnv.env_named(n, xs) == Env.named(n, xs) : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +w <> rest:
      Equal.cong(Bool, Bool, x => Bool.or(String.eq(Env.Var.name(w), n), x), ChildEnv.env_named(n, rest), Env.named(n, rest), pce.named_eq(n, rest))

# a member equal to h has h's name test
def pce.named_by(+over: List<&2, Env.Var>, -v: Env.Var, -h: Env.Var, eq: {v == h : Env.Var}, eb: {Env.named(Env.Var.name(h), over) == False{} : Bool}) -> {Env.named(Env.Var.name(v), over) == False{} : Bool}:
  %Equal.sym(Env.Var, v, h, eq) : {Env.named(Env.Var.name(_), over) == False{} : Bool}
  eb

def pce.pair_inr(-h: Env.Var, -t: List<&2, Env.Var>, -over: List<&2, Env.Var>, -v: Env.Var, p: (Env.In(v, t) & {Env.named(Env.Var.name(v), over) == False{} : Bool})) -> (Env.In(v, h <> t) & {Env.named(Env.Var.name(v), over) == False{} : Bool}):
  (a, f) = p
  (Inr{a}, f)

def pce.under_put_out(b: Bool, +h: Env.Var, -t: List<&2, Env.Var>, +over: List<&2, Env.Var>, +v: Env.Var, eb: {Env.named(Env.Var.name(h), over) == b : Bool}, i: Env.In(v, Env.under.put(b, h, Env.under(t, over))), ih: Env.In(v, Env.under(t, over)) -> (Env.In(v, t) & {Env.named(Env.Var.name(v), over) == False{} : Bool})) -> (Env.In(v, h <> t) & {Env.named(Env.Var.name(v), over) == False{} : Bool}):
  match b:
    case True{}:
      pce.pair_inr(h, t, over, v, ih(i))
    case False{}:
      match i:
        case Inl{+eq}:
          (Inl{eq}, pce.named_by(over, v, h, eq, eb))
        case Inr{it}:
          pce.pair_inr(h, t, over, v, ih(it))

# a member of the filtered base is a member of the base the overlay does
# not name
def pce.under_out(base: List<&2, Env.Var>, +over: List<&2, Env.Var>, +v: Env.Var, i: Env.In(v, Env.under(base, over))) -> (Env.In(v, base) & {Env.named(Env.Var.name(v), over) == False{} : Bool}):
  match base:
    case Nil{}:
      match i:
    case +h <> +t:
      pce.under_put_out(Env.named(Env.Var.name(h), over), h, t, over, v, {==}, i, x => pce.under_out(t, over, v, x))

# ---- child_env_entry ----

# The entry of the compiled core (bend/ffi_child_env.bend), field by field
# as proof_director's entry.

def pce.var_rt(+v: Env.Var, +rest: String, +h: {ChildEnv.env_var_fits(v) == True{} : Bool}) -> {FEnv.get_var(FEnv.put_var(v, rest)) == Wr.Got{v, rest} : Wr.Dec<Env.Var>}:
  match v:
    case Env.Var{+n, +x}:
      Equal.trans(Wr.Dec<Env.Var>, FEnv.get_var.name(Wr.get_str(Wr.put_str(n, Wr.put_str(x, rest)))), FEnv.get_var.name(Wr.Got{n, Wr.put_str(x, rest)}), Wr.Got{Env.Var{n, x}, rest}, Equal.cong(Wr.Dec<String>, Wr.Dec<Env.Var>, d => FEnv.get_var.name(d), Wr.get_str(Wr.put_str(n, Wr.put_str(x, rest))), Wr.Got{n, Wr.put_str(x, rest)}, Wire.wire_str_round_trip(n, Wr.put_str(x, rest), LLogicBool.wr_and_l(ChildEnv.env_str_fits(n), ChildEnv.env_str_fits(x), h))), Equal.cong(Wr.Dec<String>, Wr.Dec<Env.Var>, d => FEnv.get_var.value(n, d), Wr.get_str(Wr.put_str(x, rest)), Wr.Got{x, rest}, Wire.wire_str_round_trip(x, rest, LLogicBool.wr_and_r(ChildEnv.env_str_fits(n), ChildEnv.env_str_fits(x), h))))

# the items of a list of String, then rest
def pce.ss.items(xs: List<&2, String>, rest: String) -> String:
  match xs:
    case Nil{}:
      rest
    case Con{x, t}:
      Wr.put_str(x, pce.ss.items(t, rest))

def pce.ss.put_go(xs: List<&2, String>, -rest: String) -> {Wr.put_list.go(~String, ~Wr.put_str, xs, rest) == (List.length(&2, String, xs), pce.ss.items(xs, rest)) : Nat & String}:
  match xs:
    case Nil{}:
      {==}
    case Con{x, +t}:
      %Equal.sym(Nat & String, Wr.put_list.go(~String, ~Wr.put_str, t, rest), (List.length(&2, String, t), pce.ss.items(t, rest)), pce.ss.put_go(t, rest)) : {Wr.put_list.step(~String, ~Wr.put_str, x, _) == (1n+List.length(&2, String, t), Wr.put_str(x, pce.ss.items(t, rest))) : Nat & String}
      {==}

# a list of String is its count, then its items
def pce.ss.put(+xs: List<&2, String>, -rest: String) -> {Wr.put_list(~String, ~Wr.put_str, xs, rest) == Wr.put_nat(List.length(&2, String, xs), pce.ss.items(xs, rest)) : String}:
  %Equal.sym(Nat & String, Wr.put_list.go(~String, ~Wr.put_str, xs, rest), (List.length(&2, String, xs), pce.ss.items(xs, rest)), pce.ss.put_go(xs, rest)) : {Wr.put_list.fin(_) == Wr.put_nat(List.length(&2, String, xs), pce.ss.items(xs, rest)) : String}
  {==}

# the item loop reads back x then t
def pce.ss.go_rt(+t: List<&2, String>, +x: String, +rest: String, +hf: {ChildEnv.env_strs_fit(x <> t) == True{} : Bool}) -> {Wr.get_list.go(~String, ~Wr.get_str, List.length(&2, String, t), Wr.get_str(Wr.put_str(x, pce.ss.items(t, rest)))) == Wr.Got{x <> t, rest} : Wr.Dec<List<&2, String>>}:
  match t:
    case Nil{}:
      %Equal.sym(Wr.Dec<String>, Wr.get_str(Wr.put_str(x, rest)), Wr.Got{x, rest}, Wire.wire_str_round_trip(x, rest, LLogicBool.wr_and_l(ChildEnv.env_str_fits(x), True{}, hf))) : {Wr.get_list.go(~String, ~Wr.get_str, 0n, _) == Wr.Got{[x], rest} : Wr.Dec<List<&2, String>>}
      {==}
    case Con{+y, +u}:
      %Equal.sym(Wr.Dec<String>, Wr.get_str(Wr.put_str(x, Wr.put_str(y, pce.ss.items(u, rest)))), Wr.Got{x, Wr.put_str(y, pce.ss.items(u, rest))}, Wire.wire_str_round_trip(x, Wr.put_str(y, pce.ss.items(u, rest)), LLogicBool.wr_and_l(ChildEnv.env_str_fits(x), ChildEnv.env_strs_fit(y <> u), hf))) : {Wr.get_list.go(~String, ~Wr.get_str, 1n+List.length(&2, String, u), _) == Wr.Got{x <> y <> u, rest} : Wr.Dec<List<&2, String>>}
      %Equal.sym(Wr.Dec<List<&2, String>>, Wr.get_list.go(~String, ~Wr.get_str, List.length(&2, String, u), Wr.get_str(Wr.put_str(y, pce.ss.items(u, rest)))), Wr.Got{y <> u, rest}, pce.ss.go_rt(u, y, rest, LLogicBool.wr_and_r(ChildEnv.env_str_fits(x), ChildEnv.env_strs_fit(y <> u), hf))) : {Wr.get_list.cons(String, x, _) == Wr.Got{x <> y <> u, rest} : Wr.Dec<List<&2, String>>}
      {==}

# a list of String that fits reads back
def pce.ss.rt(+xs: List<&2, String>, +rest: String, h: {Bool.and(LawsBase.wire_fits(List.length(&2, String, xs)), ChildEnv.env_strs_fit(xs)) == True{} : Bool}) -> {Wr.get_list(~String, ~Wr.get_str, Wr.put_list(~String, ~Wr.put_str, xs, rest)) == Wr.Got{xs, rest} : Wr.Dec<List<&2, String>>}:
  match xs:
    case Nil{}:
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(0n, rest)), Wr.Got{0n, rest}, Wire.wire_nat_round_trip(0n, rest, LLogicBool.wr_and_l(LawsBase.wire_fits(0n), True{}, h))) : {Wr.get_list.start(~String, ~Wr.get_str, _) == Wr.Got{Nil{}, rest} : Wr.Dec<List<&2, String>>}
      {==}
    case Con{+x, +t}:
      +r = rest
      +hh = h
      %Equal.sym(String, Wr.put_list(~String, ~Wr.put_str, x <> t, r), Wr.put_nat(List.length(&2, String, x <> t), pce.ss.items(x <> t, r)), pce.ss.put(x <> t, r)) : {Wr.get_list(~String, ~Wr.get_str, _) == Wr.Got{x <> t, r} : Wr.Dec<List<&2, String>>}
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(List.length(&2, String, x <> t), pce.ss.items(x <> t, r))), Wr.Got{List.length(&2, String, x <> t), pce.ss.items(x <> t, r)}, Wire.wire_nat_round_trip(List.length(&2, String, x <> t), pce.ss.items(x <> t, r), LLogicBool.wr_and_l(LawsBase.wire_fits(List.length(&2, String, x <> t)), ChildEnv.env_strs_fit(x <> t), hh))) : {Wr.get_list.start(~String, ~Wr.get_str, _) == Wr.Got{x <> t, r} : Wr.Dec<List<&2, String>>}
      pce.ss.go_rt(t, x, r, LLogicBool.wr_and_r(LawsBase.wire_fits(List.length(&2, String, x <> t)), ChildEnv.env_strs_fit(x <> t), hh))

# the items of a list of Env.Var, then rest
def pce.vs.items(xs: List<&2, Env.Var>, rest: String) -> String:
  match xs:
    case Nil{}:
      rest
    case Con{x, t}:
      FEnv.put_var(x, pce.vs.items(t, rest))

def pce.vs.put_go(xs: List<&2, Env.Var>, -rest: String) -> {Wr.put_list.go(~Env.Var, ~FEnv.put_var, xs, rest) == (List.length(&2, Env.Var, xs), pce.vs.items(xs, rest)) : Nat & String}:
  match xs:
    case Nil{}:
      {==}
    case Con{x, +t}:
      %Equal.sym(Nat & String, Wr.put_list.go(~Env.Var, ~FEnv.put_var, t, rest), (List.length(&2, Env.Var, t), pce.vs.items(t, rest)), pce.vs.put_go(t, rest)) : {Wr.put_list.step(~Env.Var, ~FEnv.put_var, x, _) == (1n+List.length(&2, Env.Var, t), FEnv.put_var(x, pce.vs.items(t, rest))) : Nat & String}
      {==}

# a list of Env.Var is its count, then its items
def pce.vs.put(+xs: List<&2, Env.Var>, -rest: String) -> {Wr.put_list(~Env.Var, ~FEnv.put_var, xs, rest) == Wr.put_nat(List.length(&2, Env.Var, xs), pce.vs.items(xs, rest)) : String}:
  %Equal.sym(Nat & String, Wr.put_list.go(~Env.Var, ~FEnv.put_var, xs, rest), (List.length(&2, Env.Var, xs), pce.vs.items(xs, rest)), pce.vs.put_go(xs, rest)) : {Wr.put_list.fin(_) == Wr.put_nat(List.length(&2, Env.Var, xs), pce.vs.items(xs, rest)) : String}
  {==}

# the item loop reads back x then t
def pce.vs.go_rt(+t: List<&2, Env.Var>, +x: Env.Var, +rest: String, +hf: {ChildEnv.env_vars_fit(x <> t) == True{} : Bool}) -> {Wr.get_list.go(~Env.Var, ~FEnv.get_var, List.length(&2, Env.Var, t), FEnv.get_var(FEnv.put_var(x, pce.vs.items(t, rest)))) == Wr.Got{x <> t, rest} : Wr.Dec<List<&2, Env.Var>>}:
  match t:
    case Nil{}:
      %Equal.sym(Wr.Dec<Env.Var>, FEnv.get_var(FEnv.put_var(x, rest)), Wr.Got{x, rest}, pce.var_rt(x, rest, LLogicBool.wr_and_l(ChildEnv.env_var_fits(x), True{}, hf))) : {Wr.get_list.go(~Env.Var, ~FEnv.get_var, 0n, _) == Wr.Got{[x], rest} : Wr.Dec<List<&2, Env.Var>>}
      {==}
    case Con{+y, +u}:
      %Equal.sym(Wr.Dec<Env.Var>, FEnv.get_var(FEnv.put_var(x, FEnv.put_var(y, pce.vs.items(u, rest)))), Wr.Got{x, FEnv.put_var(y, pce.vs.items(u, rest))}, pce.var_rt(x, FEnv.put_var(y, pce.vs.items(u, rest)), LLogicBool.wr_and_l(ChildEnv.env_var_fits(x), ChildEnv.env_vars_fit(y <> u), hf))) : {Wr.get_list.go(~Env.Var, ~FEnv.get_var, 1n+List.length(&2, Env.Var, u), _) == Wr.Got{x <> y <> u, rest} : Wr.Dec<List<&2, Env.Var>>}
      %Equal.sym(Wr.Dec<List<&2, Env.Var>>, Wr.get_list.go(~Env.Var, ~FEnv.get_var, List.length(&2, Env.Var, u), FEnv.get_var(FEnv.put_var(y, pce.vs.items(u, rest)))), Wr.Got{y <> u, rest}, pce.vs.go_rt(u, y, rest, LLogicBool.wr_and_r(ChildEnv.env_var_fits(x), ChildEnv.env_vars_fit(y <> u), hf))) : {Wr.get_list.cons(Env.Var, x, _) == Wr.Got{x <> y <> u, rest} : Wr.Dec<List<&2, Env.Var>>}
      {==}

# a list of Env.Var that fits reads back
def pce.vs.rt(+xs: List<&2, Env.Var>, +rest: String, h: {Bool.and(LawsBase.wire_fits(List.length(&2, Env.Var, xs)), ChildEnv.env_vars_fit(xs)) == True{} : Bool}) -> {Wr.get_list(~Env.Var, ~FEnv.get_var, Wr.put_list(~Env.Var, ~FEnv.put_var, xs, rest)) == Wr.Got{xs, rest} : Wr.Dec<List<&2, Env.Var>>}:
  match xs:
    case Nil{}:
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(0n, rest)), Wr.Got{0n, rest}, Wire.wire_nat_round_trip(0n, rest, LLogicBool.wr_and_l(LawsBase.wire_fits(0n), True{}, h))) : {Wr.get_list.start(~Env.Var, ~FEnv.get_var, _) == Wr.Got{Nil{}, rest} : Wr.Dec<List<&2, Env.Var>>}
      {==}
    case Con{+x, +t}:
      +r = rest
      +hh = h
      %Equal.sym(String, Wr.put_list(~Env.Var, ~FEnv.put_var, x <> t, r), Wr.put_nat(List.length(&2, Env.Var, x <> t), pce.vs.items(x <> t, r)), pce.vs.put(x <> t, r)) : {Wr.get_list(~Env.Var, ~FEnv.get_var, _) == Wr.Got{x <> t, r} : Wr.Dec<List<&2, Env.Var>>}
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(List.length(&2, Env.Var, x <> t), pce.vs.items(x <> t, r))), Wr.Got{List.length(&2, Env.Var, x <> t), pce.vs.items(x <> t, r)}, Wire.wire_nat_round_trip(List.length(&2, Env.Var, x <> t), pce.vs.items(x <> t, r), LLogicBool.wr_and_l(LawsBase.wire_fits(List.length(&2, Env.Var, x <> t)), ChildEnv.env_vars_fit(x <> t), hh))) : {Wr.get_list.start(~Env.Var, ~FEnv.get_var, _) == Wr.Got{x <> t, r} : Wr.Dec<List<&2, Env.Var>>}
      pce.vs.go_rt(t, x, r, LLogicBool.wr_and_r(LawsBase.wire_fits(List.length(&2, Env.Var, x <> t)), ChildEnv.env_vars_fit(x <> t), hh))

def pce.req_rt(+q: FEnv.Req, +rest: String, +h: {ChildEnv.env_req_fits(q) == True{} : Bool}) -> {FEnv.get_req(FEnv.put_req(q, rest)) == Wr.Got{q, rest} : Wr.Dec<FEnv.Req>}:
  match q:
    case FEnv.Req{+r, +k, +b, +o}:
      +h1 = LLogicBool.wr_and_r(Bool.and(LawsBase.wire_fits(List.length(&2, String, r)), ChildEnv.env_strs_fit(r)), Bool.and(Bool.and(LawsBase.wire_fits(List.length(&2, String, k)), ChildEnv.env_strs_fit(k)), Bool.and(Bool.and(LawsBase.wire_fits(List.length(&2, Env.Var, b)), ChildEnv.env_vars_fit(b)), Bool.and(LawsBase.wire_fits(List.length(&2, Env.Var, o)), ChildEnv.env_vars_fit(o)))), h)
      +h2 = LLogicBool.wr_and_r(Bool.and(LawsBase.wire_fits(List.length(&2, String, k)), ChildEnv.env_strs_fit(k)), Bool.and(Bool.and(LawsBase.wire_fits(List.length(&2, Env.Var, b)), ChildEnv.env_vars_fit(b)), Bool.and(LawsBase.wire_fits(List.length(&2, Env.Var, o)), ChildEnv.env_vars_fit(o))), h1)
      Equal.trans(Wr.Dec<FEnv.Req>, FEnv.get_req.reg(Wr.get_list(~String, ~Wr.get_str, Wr.put_list(~String, ~Wr.put_str, r, Wr.put_list(~String, ~Wr.put_str, k, Wr.put_list(~Env.Var, ~FEnv.put_var, b, Wr.put_list(~Env.Var, ~FEnv.put_var, o, rest)))))), FEnv.get_req.reg(Wr.Got{r, Wr.put_list(~String, ~Wr.put_str, k, Wr.put_list(~Env.Var, ~FEnv.put_var, b, Wr.put_list(~Env.Var, ~FEnv.put_var, o, rest)))}), Wr.Got{FEnv.Req{r, k, b, o}, rest}, Equal.cong(Wr.Dec<List<&2, String>>, Wr.Dec<FEnv.Req>, d => FEnv.get_req.reg(d), Wr.get_list(~String, ~Wr.get_str, Wr.put_list(~String, ~Wr.put_str, r, Wr.put_list(~String, ~Wr.put_str, k, Wr.put_list(~Env.Var, ~FEnv.put_var, b, Wr.put_list(~Env.Var, ~FEnv.put_var, o, rest))))), Wr.Got{r, Wr.put_list(~String, ~Wr.put_str, k, Wr.put_list(~Env.Var, ~FEnv.put_var, b, Wr.put_list(~Env.Var, ~FEnv.put_var, o, rest)))}, pce.ss.rt(r, Wr.put_list(~String, ~Wr.put_str, k, Wr.put_list(~Env.Var, ~FEnv.put_var, b, Wr.put_list(~Env.Var, ~FEnv.put_var, o, rest))), LLogicBool.wr_and_l(Bool.and(LawsBase.wire_fits(List.length(&2, String, r)), ChildEnv.env_strs_fit(r)), Bool.and(Bool.and(LawsBase.wire_fits(List.length(&2, String, k)), ChildEnv.env_strs_fit(k)), Bool.and(Bool.and(LawsBase.wire_fits(List.length(&2, Env.Var, b)), ChildEnv.env_vars_fit(b)), Bool.and(LawsBase.wire_fits(List.length(&2, Env.Var, o)), ChildEnv.env_vars_fit(o)))), h))), Equal.trans(Wr.Dec<FEnv.Req>, FEnv.get_req.keep(r, Wr.get_list(~String, ~Wr.get_str, Wr.put_list(~String, ~Wr.put_str, k, Wr.put_list(~Env.Var, ~FEnv.put_var, b, Wr.put_list(~Env.Var, ~FEnv.put_var, o, rest))))), FEnv.get_req.keep(r, Wr.Got{k, Wr.put_list(~Env.Var, ~FEnv.put_var, b, Wr.put_list(~Env.Var, ~FEnv.put_var, o, rest))}), Wr.Got{FEnv.Req{r, k, b, o}, rest}, Equal.cong(Wr.Dec<List<&2, String>>, Wr.Dec<FEnv.Req>, d => FEnv.get_req.keep(r, d), Wr.get_list(~String, ~Wr.get_str, Wr.put_list(~String, ~Wr.put_str, k, Wr.put_list(~Env.Var, ~FEnv.put_var, b, Wr.put_list(~Env.Var, ~FEnv.put_var, o, rest)))), Wr.Got{k, Wr.put_list(~Env.Var, ~FEnv.put_var, b, Wr.put_list(~Env.Var, ~FEnv.put_var, o, rest))}, pce.ss.rt(k, Wr.put_list(~Env.Var, ~FEnv.put_var, b, Wr.put_list(~Env.Var, ~FEnv.put_var, o, rest)), LLogicBool.wr_and_l(Bool.and(LawsBase.wire_fits(List.length(&2, String, k)), ChildEnv.env_strs_fit(k)), Bool.and(Bool.and(LawsBase.wire_fits(List.length(&2, Env.Var, b)), ChildEnv.env_vars_fit(b)), Bool.and(LawsBase.wire_fits(List.length(&2, Env.Var, o)), ChildEnv.env_vars_fit(o))), h1))), Equal.trans(Wr.Dec<FEnv.Req>, FEnv.get_req.base(r, k, Wr.get_list(~Env.Var, ~FEnv.get_var, Wr.put_list(~Env.Var, ~FEnv.put_var, b, Wr.put_list(~Env.Var, ~FEnv.put_var, o, rest)))), FEnv.get_req.base(r, k, Wr.Got{b, Wr.put_list(~Env.Var, ~FEnv.put_var, o, rest)}), Wr.Got{FEnv.Req{r, k, b, o}, rest}, Equal.cong(Wr.Dec<List<&2, Env.Var>>, Wr.Dec<FEnv.Req>, d => FEnv.get_req.base(r, k, d), Wr.get_list(~Env.Var, ~FEnv.get_var, Wr.put_list(~Env.Var, ~FEnv.put_var, b, Wr.put_list(~Env.Var, ~FEnv.put_var, o, rest))), Wr.Got{b, Wr.put_list(~Env.Var, ~FEnv.put_var, o, rest)}, pce.vs.rt(b, Wr.put_list(~Env.Var, ~FEnv.put_var, o, rest), LLogicBool.wr_and_l(Bool.and(LawsBase.wire_fits(List.length(&2, Env.Var, b)), ChildEnv.env_vars_fit(b)), Bool.and(LawsBase.wire_fits(List.length(&2, Env.Var, o)), ChildEnv.env_vars_fit(o)), h2))), Equal.cong(Wr.Dec<List<&2, Env.Var>>, Wr.Dec<FEnv.Req>, d => FEnv.get_req.over(r, k, b, d), Wr.get_list(~Env.Var, ~FEnv.get_var, Wr.put_list(~Env.Var, ~FEnv.put_var, o, rest)), Wr.Got{o, rest}, pce.vs.rt(o, rest, LLogicBool.wr_and_r(Bool.and(LawsBase.wire_fits(List.length(&2, Env.Var, b)), ChildEnv.env_vars_fit(b)), Bool.and(LawsBase.wire_fits(List.length(&2, Env.Var, o)), ChildEnv.env_vars_fit(o)), h2))))))
