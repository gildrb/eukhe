# eukhe: the proof of LAW quirk_valid_rulebook_compiles

import Base
import ../../bend/infer.bend as If
import ../../laws/infer.bend as Infer
import ./base.bend as LA

# Known directives
# ----------------

# the laws' membership is the code's
def pv.has_elem(ks: List<&2, Nat>, +d: Nat) -> {Infer.rb.has(ks, d) == If.elem(ks, d) : Bool}:
  match ks:
    case Nil{}:
      {==}
    case +k <> +rest:
      %pv.has_elem(rest, d) : {Bool.or(Nat.is_eq(k, d), Infer.rb.has(rest, d)) == Bool.or(Nat.is_eq(k, d), _) : Bool}
      {==}

# every directive known by the laws: the code finds every directive known
def pv.known(+ks: List<&2, Nat>, rs: List<&2, If.Rule>, +kn: {Infer.rb.all_known(ks, rs) == True{} : Bool}) -> {If.known_all(rs, ks) == True{} : Bool}:
  match rs:
    case Nil{}:
      {==}
    case +r <> +rest:
      +D = If.Rule.dir(r)
      +hk = LA.pi.and_l(Infer.rb.has(ks, D), Infer.rb.all_known(ks, rest), kn)
      +he = Equal.trans(Bool, If.elem(ks, D), Infer.rb.has(ks, D), True{}, Equal.sym(Bool, Infer.rb.has(ks, D), If.elem(ks, D), pv.has_elem(ks, D)), hk)
      LA.pq.and_t(If.elem(ks, D), If.known_all(rest, ks), he, pv.known(ks, rest, LA.pi.and_r(Infer.rb.has(ks, D), Infer.rb.all_known(ks, rest), kn)))

# Clashes
# -------

# the laws' clash is the code's
def pv.clash_eq(+a: If.Rule, +b: If.Rule) -> {Infer.rb.clash(a, b) == If.clash(a, b) : Bool}:
  match a b:
    case If.Rule{If.Fam{}, ta, da, va} If.Rule{If.Fam{}, tb, db, vb}:
      {==}
    case If.Rule{If.Fam{}, ta, da, va} If.Rule{If.Mod{}, tb, db, vb}:
      {==}
    case If.Rule{If.Fam{}, ta, da, va} If.Rule{If.Host{}, tb, db, vb}:
      {==}
    case If.Rule{If.Mod{}, ta, da, va} If.Rule{If.Fam{}, tb, db, vb}:
      {==}
    case If.Rule{If.Mod{}, ta, da, va} If.Rule{If.Mod{}, tb, db, vb}:
      {==}
    case If.Rule{If.Mod{}, ta, da, va} If.Rule{If.Host{}, tb, db, vb}:
      {==}
    case If.Rule{If.Host{}, ta, da, va} If.Rule{If.Fam{}, tb, db, vb}:
      {==}
    case If.Rule{If.Host{}, ta, da, va} If.Rule{If.Mod{}, tb, db, vb}:
      {==}
    case If.Rule{If.Host{}, ta, da, va} If.Rule{If.Host{}, tb, db, vb}:
      {==}

# r clashes with no rule of rs: the code finds no clash of r in rs
def pv.calm_clashes(+r: If.Rule, rs: List<&2, If.Rule>, +h: {Infer.rb.calm(r, rs) == True{} : Bool}) -> {If.clashes(r, rs) == False{} : Bool}:
  match rs:
    case Nil{}:
      {==}
    case +s <> +rest:
      +N = Bool.not(Infer.rb.clash(r, s))
      +c = LA.pq.not_f(Infer.rb.clash(r, s), LA.pi.and_l(N, Infer.rb.calm(r, rest), h))
      +ce = Equal.trans(Bool, If.clash(r, s), Infer.rb.clash(r, s), False{}, Equal.sym(Bool, Infer.rb.clash(r, s), If.clash(r, s), pv.clash_eq(r, s)), c)
      %Equal.sym(Bool, If.clash(r, s), False{}, ce) : {Bool.or(_, If.clashes(r, rest)) == False{} : Bool}
      pv.calm_clashes(r, rest, LA.pi.and_r(N, Infer.rb.calm(r, rest), h))

# calm against s <> ys: calm against ys
def pv.calm_drop(+x: If.Rule, +s: If.Rule, +ys: List<&2, If.Rule>, h: {Infer.rb.calm(x, s <> ys) == True{} : Bool}) -> {Infer.rb.calm(x, ys) == True{} : Bool}:
  LA.pi.and_r(Bool.not(Infer.rb.clash(x, s)), Infer.rb.calm(x, ys), h)

# every rule of xs calm against s <> ys: calm against ys
def pv.calm_all_drop(xs: List<&2, If.Rule>, +s: If.Rule, +ys: List<&2, If.Rule>, +h: {Infer.rb.calm_all(xs, s <> ys) == True{} : Bool}) -> {Infer.rb.calm_all(xs, ys) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +rest:
      +A = Infer.rb.calm(x, s <> ys)
      +B = Infer.rb.calm_all(rest, s <> ys)
      LA.pq.and_t(Infer.rb.calm(x, ys), Infer.rb.calm_all(rest, ys), pv.calm_drop(x, s, ys, LA.pi.and_l(A, B, h)), pv.calm_all_drop(rest, s, ys, LA.pi.and_r(A, B, h)))

# no rule of rs clashes with a rule of rs: the code finds no ambiguity
def pv.calm_amb(rs: List<&2, If.Rule>, +h: {Infer.rb.calm_all(rs, rs) == True{} : Bool}) -> {If.ambiguous(rs) == False{} : Bool}:
  match rs:
    case Nil{}:
      {==}
    case +r <> +rest:
      +A = Infer.rb.calm(r, r <> rest)
      +B = Infer.rb.calm_all(rest, r <> rest)
      +c = pv.calm_clashes(r, rest, pv.calm_drop(r, r, rest, LA.pi.and_l(A, B, h)))
      %Equal.sym(Bool, If.clashes(r, rest), False{}, c) : {Bool.or(_, If.ambiguous(rest)) == False{} : Bool}
      pv.calm_amb(rest, pv.calm_all_drop(rest, r, rest, LA.pi.and_r(A, B, h)))

def pv.quirk_valid_rulebook_compiles(+known: List<&2, Nat>, +rs: List<&2, If.Rule>, kn: {Infer.rb.all_known(known, rs) == True{} : Bool}, calm: {Infer.rb.calm_all(rs, rs) == True{} : Bool}) -> {If.compiles(known, rs) == True{} : Bool}:
  %Equal.sym(Bool, If.known_all(rs, known), True{}, pv.known(known, rs, kn)) : {Bool.and(_, Bool.not(If.ambiguous(rs))) == True{} : Bool}
  %Equal.sym(Bool, If.ambiguous(rs), False{}, pv.calm_amb(rs, calm)) : {Bool.and(True{}, Bool.not(_)) == True{} : Bool}
  {==}

# (S6) The inference layer

def Infer.quirk_valid_rulebook_compiles(known, rs, kn, calm):
  pv.quirk_valid_rulebook_compiles(known, rs, kn, calm)
