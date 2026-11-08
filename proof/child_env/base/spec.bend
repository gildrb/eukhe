# eukhe: lemmas of area child_env: the model's terms and environment of a
# child are the spec's (laws/child_env.bend, ce_*), the entry's encoders
# write what the spec's spellers write and its decoders read what the
# spec's readers read, on every input.

import Base
import ../../../bend/child_env.bend as Env
import ../../../bend/ffi_child_env.bend as FEnv
import ../../../bend/wire.bend as Wr
import ../../../laws/child_env.bend as ChildEnv

# The model
# ---------

def pcs.up(s: String) -> {Env.up(s) == ChildEnv.ce_up(s) : String}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      %pcs.up(t) : {SCon{Char.to_upper(c), Env.up(t)} == SCon{Char.to_upper(c), _} : String}
      {==}

def pcs.lstep(b: Bool, +r: String, +rest: List<&2, String>, +u: String, ih: {Env.listed.go(rest, u, Env.listed.at(rest, u)) == ChildEnv.ce_has(rest, u) : Bool}) -> {Env.listed.go(r <> rest, u, b) == Bool.or(b, ChildEnv.ce_has(rest, u)) : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      ih

def pcs.listed(ns: List<&2, String>, +u: String) -> {Env.listed(ns, u) == ChildEnv.ce_has(ns, u) : Bool}:
  match ns:
    case Nil{}:
      {==}
    case +r <> +rest:
      pcs.lstep(String.eq(r, u), r, rest, u, pcs.listed(rest, u))

def pcs.mstep(b: Bool, +p: String, +rest: List<&2, String>, +u: String, ih: {Env.matched.go(rest, u, Env.matched.at(rest, u)) == ChildEnv.ce_hits(rest, u) : Bool}) -> {Env.matched.go(p <> rest, u, b) == Bool.or(b, ChildEnv.ce_hits(rest, u)) : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      ih

def pcs.matched(ps: List<&2, String>, +u: String) -> {Env.matched(ps, u) == ChildEnv.ce_hits(ps, u) : Bool}:
  match ps:
    case Nil{}:
      {==}
    case +p <> +rest:
      pcs.mstep(String.contains(u, p), p, rest, u, pcs.matched(rest, u))

def pcs.cred(+reg: List<&2, String>, +n: String) -> {Env.cred(reg, n) == ChildEnv.ce_cred(reg, n) : Bool}:
  %pcs.up(n) : {Bool.or(Env.listed(reg, Env.up(n)), Env.matched(Env.patterns(), Env.up(n))) == Bool.or(ChildEnv.ce_has(reg, _), ChildEnv.ce_hits(ChildEnv.ce_pats(), _)) : Bool}
  %pcs.listed(reg, Env.up(n)) : {Bool.or(Env.listed(reg, Env.up(n)), Env.matched(Env.patterns(), Env.up(n))) == Bool.or(_, ChildEnv.ce_hits(ChildEnv.ce_pats(), Env.up(n))) : Bool}
  %pcs.matched(Env.patterns(), Env.up(n)) : {Bool.or(Env.listed(reg, Env.up(n)), Env.matched(Env.patterns(), Env.up(n))) == Bool.or(Env.listed(reg, Env.up(n)), _) : Bool}
  {==}

def pcs.registered(+reg: List<&2, String>, +n: String) -> {Env.registered(reg, n) == ChildEnv.ce_provider(reg, n) : Bool}:
  %pcs.up(n) : {Env.listed(reg, Env.up(n)) == ChildEnv.ce_has(reg, _) : Bool}
  pcs.listed(reg, Env.up(n))

def pcs.pat(m: Bool, +keep: List<&2, String>, +n: String) -> {Env.passes.pat(m, keep, n) == Bool.or(Bool.not(m), ChildEnv.ce_has(keep, n)) : Bool}:
  match m:
    case True{}:
      pcs.listed(keep, n)
    case False{}:
      {==}

def pcs.regb(h: Bool, +u: String, +keep: List<&2, String>, +n: String) -> {Env.passes.reg(h, u, keep, n) == Bool.or(Bool.not(Bool.or(h, ChildEnv.ce_hits(ChildEnv.ce_pats(), u))), Bool.and(Bool.not(h), ChildEnv.ce_has(keep, n))) : Bool}:
  match h:
    case True{}:
      {==}
    case False{}:
      %pcs.matched(Env.patterns(), u) : {Env.passes.pat(Env.matched(Env.patterns(), u), keep, n) == Bool.or(Bool.not(_), ChildEnv.ce_has(keep, n)) : Bool}
      pcs.pat(Env.matched(Env.patterns(), u), keep, n)

def pcs.passes(+reg: List<&2, String>, +keep: List<&2, String>, +n: String) -> {Env.passes(reg, keep, n) == ChildEnv.ce_passes(reg, keep, n) : Bool}:
  %pcs.up(n) : {Env.passes.reg(Env.listed(reg, Env.up(n)), Env.up(n), keep, n) == Bool.or(Bool.not(Bool.or(ChildEnv.ce_has(reg, _), ChildEnv.ce_hits(ChildEnv.ce_pats(), _))), Bool.and(Bool.not(ChildEnv.ce_has(reg, _)), ChildEnv.ce_has(keep, n))) : Bool}
  %pcs.listed(reg, Env.up(n)) : {Env.passes.reg(Env.listed(reg, Env.up(n)), Env.up(n), keep, n) == Bool.or(Bool.not(Bool.or(_, ChildEnv.ce_hits(ChildEnv.ce_pats(), Env.up(n)))), Bool.and(Bool.not(_), ChildEnv.ce_has(keep, n))) : Bool}
  pcs.regb(Env.listed(reg, Env.up(n)), Env.up(n), keep, n)

def pcs.named(+n: String, xs: List<&2, Env.Var>) -> {Env.named(n, xs) == ChildEnv.ce_named(n, xs) : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Env.Var{+m, +x} <> +t:
      %pcs.named(n, t) : {Bool.or(String.eq(m, n), Env.named(n, t)) == Bool.or(String.eq(m, n), _) : Bool}
      {==}

def pcs.hpick(b: Bool, v: Env.Var, r: List<&2, Env.Var>) -> {Env.under.put(b, v, r) == ChildEnv.ce_hidden.pick(b, v, r) : List<&2, Env.Var>}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def pcs.under(base: List<&2, Env.Var>, +over: List<&2, Env.Var>) -> {Env.under(base, over) == ChildEnv.ce_hidden(base, over) : List<&2, Env.Var>}:
  match base:
    case Nil{}:
      {==}
    case Env.Var{+m, +x} <> +t:
      %pcs.under(t, over) : {Env.under.put(Env.named(m, over), Env.Var{m, x}, Env.under(t, over)) == ChildEnv.ce_hidden.pick(ChildEnv.ce_named(m, over), Env.Var{m, x}, _) : List<&2, Env.Var>}
      %pcs.named(m, over) : {Env.under.put(Env.named(m, over), Env.Var{m, x}, Env.under(t, over)) == ChildEnv.ce_hidden.pick(_, Env.Var{m, x}, Env.under(t, over)) : List<&2, Env.Var>}
      pcs.hpick(Env.named(m, over), Env.Var{m, x}, Env.under(t, over))

def pcs.merge(+base: List<&2, Env.Var>, +over: List<&2, Env.Var>) -> {Env.merge(base, over) == ChildEnv.ce_merge(base, over) : List<&2, Env.Var>}:
  %pcs.under(base, over) : {List.append(&2, Env.Var, over, Env.under(base, over)) == List.append(&2, Env.Var, over, _) : List<&2, Env.Var>}
  {==}

def pcs.kpick(b: Bool, v: Env.Var, r: List<&2, Env.Var>) -> {Env.keep.put(b, v, r) == ChildEnv.ce_keep.pick(b, v, r) : List<&2, Env.Var>}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def pcs.keep(+reg: List<&2, String>, +keep: List<&2, String>, xs: List<&2, Env.Var>) -> {Env.keep(reg, keep, xs) == ChildEnv.ce_keep(reg, keep, xs) : List<&2, Env.Var>}:
  match xs:
    case Nil{}:
      {==}
    case Env.Var{+m, +x} <> +t:
      %pcs.keep(reg, keep, t) : {Env.keep.put(Env.passes(reg, keep, m), Env.Var{m, x}, Env.keep(reg, keep, t)) == ChildEnv.ce_keep.pick(ChildEnv.ce_passes(reg, keep, m), Env.Var{m, x}, _) : List<&2, Env.Var>}
      %pcs.passes(reg, keep, m) : {Env.keep.put(Env.passes(reg, keep, m), Env.Var{m, x}, Env.keep(reg, keep, t)) == ChildEnv.ce_keep.pick(_, Env.Var{m, x}, Env.keep(reg, keep, t)) : List<&2, Env.Var>}
      pcs.kpick(Env.passes(reg, keep, m), Env.Var{m, x}, Env.keep(reg, keep, t))

def pcs.child(+reg: List<&2, String>, +keep: List<&2, String>, +base: List<&2, Env.Var>, +over: List<&2, Env.Var>) -> {Env.child(reg, keep, base, over) == ChildEnv.ce_child(reg, keep, base, over) : List<&2, Env.Var>}:
  %pcs.merge(base, over) : {Env.keep(reg, keep, Env.merge(base, over)) == ChildEnv.ce_keep(reg, keep, _) : List<&2, Env.Var>}
  pcs.keep(reg, keep, Env.merge(base, over))

def pcs.in(+x: Env.Var, xs: List<&2, Env.Var>) -> {Env.In(x, xs) == ChildEnv.ce_in(x, xs) : Type}:
  match xs:
    case Nil{}:
      {==}
    case +w <> +t:
      %pcs.in(x, t) : {Or({x == w : Env.Var}, Env.In(x, t)) == Or({x == w : Env.Var}, _) : Type}
      {==}

# Encoders
# --------

def pcs.put_var(v: Env.Var, rest: String) -> {FEnv.put_var(v, rest) == ChildEnv.ce_spell_var(v, rest) : String}:
  match v:
    case Env.Var{n, x}:
      {==}

def pcs.vars_step(+x: Env.Var, r: Nat & String) -> {Wr.put_list.step(~Env.Var, ~FEnv.put_var, x, r) == Wr.put_list.step(~Env.Var, ~ChildEnv.ce_spell_var, x, r) : Nat & String}:
  match r:
    case (n, +s):
      %pcs.put_var(x, s) : {(1n+n, FEnv.put_var(x, s)) == (1n+n, _) : Nat & String}
      {==}

def pcs.vars_go(xs: List<&2, Env.Var>, +rest: String) -> {Wr.put_list.go(~Env.Var, ~FEnv.put_var, xs, rest) == Wr.put_list.go(~Env.Var, ~ChildEnv.ce_spell_var, xs, rest) : Nat & String}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      %pcs.vars_go(t, rest) : {Wr.put_list.step(~Env.Var, ~FEnv.put_var, x, Wr.put_list.go(~Env.Var, ~FEnv.put_var, t, rest)) == Wr.put_list.step(~Env.Var, ~ChildEnv.ce_spell_var, x, _) : Nat & String}
      pcs.vars_step(x, Wr.put_list.go(~Env.Var, ~FEnv.put_var, t, rest))

def pcs.put_vars(xs: List<&2, Env.Var>, +rest: String) -> {Wr.put_list(~Env.Var, ~FEnv.put_var, xs, rest) == Wr.put_list(~Env.Var, ~ChildEnv.ce_spell_var, xs, rest) : String}:
  %pcs.vars_go(xs, rest) : {Wr.put_list.fin(Wr.put_list.go(~Env.Var, ~FEnv.put_var, xs, rest)) == Wr.put_list.fin(_) : String}
  {==}

def pcs.put_req(q: FEnv.Req, +rest: String) -> {FEnv.put_req(q, rest) == ChildEnv.ce_spell_req(q, rest) : String}:
  match q:
    case FEnv.Req{+r, +k, +b, +o}:
      %pcs.put_vars(o, rest) : {Wr.put_list(~String, ~Wr.put_str, r, Wr.put_list(~String, ~Wr.put_str, k, Wr.put_list(~Env.Var, ~FEnv.put_var, b, Wr.put_list(~Env.Var, ~FEnv.put_var, o, rest)))) == Wr.put_list(~String, ~Wr.put_str, r, Wr.put_list(~String, ~Wr.put_str, k, Wr.put_list(~Env.Var, ~ChildEnv.ce_spell_var, b, _))) : String}
      %pcs.put_vars(b, Wr.put_list(~Env.Var, ~FEnv.put_var, o, rest)) : {Wr.put_list(~String, ~Wr.put_str, r, Wr.put_list(~String, ~Wr.put_str, k, Wr.put_list(~Env.Var, ~FEnv.put_var, b, Wr.put_list(~Env.Var, ~FEnv.put_var, o, rest)))) == Wr.put_list(~String, ~Wr.put_str, r, Wr.put_list(~String, ~Wr.put_str, k, _)) : String}
      {==}

# the entry's answer to a request is the spec's reply
def pcs.run(q: FEnv.Req) -> {FEnv.ffi.run(q) == ChildEnv.ce_reply(q) : String}:
  match q:
    case FEnv.Req{+r, +k, +b, +o}:
      %pcs.child(r, k, b, o) : {Wr.put_list(~Env.Var, ~FEnv.put_var, Env.child(r, k, b, o), "") == Wr.put_list(~Env.Var, ~ChildEnv.ce_spell_var, _, "") : String}
      pcs.put_vars(Env.child(r, k, b, o), "")

# Decoders
# --------

def pcs.var_value(n: String, d: Wr.Dec<String>) -> {FEnv.get_var.value(n, d) == ChildEnv.ce_read_var.value(n, d) : Wr.Dec<Env.Var>}:
  match d:
    case Wr.Got{x, s}:
      {==}
    case Wr.Bad{}:
      {==}

def pcs.var_name(d: Wr.Dec<String>) -> {FEnv.get_var.name(d) == ChildEnv.ce_read_var.name(d) : Wr.Dec<Env.Var>}:
  match d:
    case Wr.Got{n, s}:
      pcs.var_value(n, Wr.get_str(s))
    case Wr.Bad{}:
      {==}

def pcs.var(s: String) -> {FEnv.get_var(s) == ChildEnv.ce_read_var(s) : Wr.Dec<Env.Var>}:
  pcs.var_name(Wr.get_str(s))

def pcs.vars_lgo(n: Nat, cur: Wr.Dec<Env.Var>) -> {Wr.get_list.go(~Env.Var, ~FEnv.get_var, n, cur) == Wr.get_list.go(~Env.Var, ~ChildEnv.ce_read_var, n, cur) : Wr.Dec<List<&2, Env.Var>>}:
  match n cur:
    case 0n Wr.Got{x, s}:
      {==}
    case 0n Wr.Bad{}:
      {==}
    case 1n+m Wr.Got{+x, +s}:
      %pcs.var(s) : {Wr.get_list.cons(Env.Var, x, Wr.get_list.go(~Env.Var, ~FEnv.get_var, m, FEnv.get_var(s))) == Wr.get_list.cons(Env.Var, x, Wr.get_list.go(~Env.Var, ~ChildEnv.ce_read_var, m, _)) : Wr.Dec<List<&2, Env.Var>>}
      %pcs.vars_lgo(m, FEnv.get_var(s)) : {Wr.get_list.cons(Env.Var, x, Wr.get_list.go(~Env.Var, ~FEnv.get_var, m, FEnv.get_var(s))) == Wr.get_list.cons(Env.Var, x, _) : Wr.Dec<List<&2, Env.Var>>}
      {==}
    case 1n+m Wr.Bad{}:
      {==}

def pcs.vars_start(r: Wr.Dec<Nat>) -> {Wr.get_list.start(~Env.Var, ~FEnv.get_var, r) == Wr.get_list.start(~Env.Var, ~ChildEnv.ce_read_var, r) : Wr.Dec<List<&2, Env.Var>>}:
  match r:
    case Wr.Got{n, +s}:
      match n:
        case 0n:
          {==}
        case 1n+m:
          %pcs.var(s) : {Wr.get_list.go(~Env.Var, ~FEnv.get_var, m, FEnv.get_var(s)) == Wr.get_list.go(~Env.Var, ~ChildEnv.ce_read_var, m, _) : Wr.Dec<List<&2, Env.Var>>}
          pcs.vars_lgo(m, FEnv.get_var(s))
    case Wr.Bad{}:
      {==}

def pcs.vars(s: String) -> {Wr.get_list(~Env.Var, ~FEnv.get_var, s) == Wr.get_list(~Env.Var, ~ChildEnv.ce_read_var, s) : Wr.Dec<List<&2, Env.Var>>}:
  pcs.vars_start(Wr.get_nat(s))

def pcs.over(r: List<&2, String>, k: List<&2, String>, b: List<&2, Env.Var>, d: Wr.Dec<List<&2, Env.Var>>) -> {FEnv.get_req.over(r, k, b, d) == ChildEnv.ce_read_req.over(r, k, b, d) : Wr.Dec<FEnv.Req>}:
  match d:
    case Wr.Got{o, s}:
      {==}
    case Wr.Bad{}:
      {==}

def pcs.base(+r: List<&2, String>, +k: List<&2, String>, d: Wr.Dec<List<&2, Env.Var>>) -> {FEnv.get_req.base(r, k, d) == ChildEnv.ce_read_req.base(r, k, d) : Wr.Dec<FEnv.Req>}:
  match d:
    case Wr.Got{+b, +s}:
      %pcs.vars(s) : {FEnv.get_req.over(r, k, b, Wr.get_list(~Env.Var, ~FEnv.get_var, s)) == ChildEnv.ce_read_req.over(r, k, b, _) : Wr.Dec<FEnv.Req>}
      pcs.over(r, k, b, Wr.get_list(~Env.Var, ~FEnv.get_var, s))
    case Wr.Bad{}:
      {==}

def pcs.keep_r(+r: List<&2, String>, d: Wr.Dec<List<&2, String>>) -> {FEnv.get_req.keep(r, d) == ChildEnv.ce_read_req.keep(r, d) : Wr.Dec<FEnv.Req>}:
  match d:
    case Wr.Got{+k, +s}:
      %pcs.vars(s) : {FEnv.get_req.base(r, k, Wr.get_list(~Env.Var, ~FEnv.get_var, s)) == ChildEnv.ce_read_req.base(r, k, _) : Wr.Dec<FEnv.Req>}
      pcs.base(r, k, Wr.get_list(~Env.Var, ~FEnv.get_var, s))
    case Wr.Bad{}:
      {==}

def pcs.reg(d: Wr.Dec<List<&2, String>>) -> {FEnv.get_req.reg(d) == ChildEnv.ce_read_req.reg(d) : Wr.Dec<FEnv.Req>}:
  match d:
    case Wr.Got{r, s}:
      pcs.keep_r(r, Wr.get_list(~String, ~Wr.get_str, s))
    case Wr.Bad{}:
      {==}

def pcs.req(s: String) -> {FEnv.get_req(s) == ChildEnv.ce_read_req(s) : Wr.Dec<FEnv.Req>}:
  pcs.reg(Wr.get_list(~String, ~Wr.get_str, s))

# The entry
# ---------

def pcs.whole(q: FEnv.Req, b: Bool) -> {FEnv.ffi.whole(q, b) == ChildEnv.ce_entry.end(b, q) : String}:
  match b:
    case True{}:
      pcs.run(q)
    case False{}:
      {==}

def pcs.go(d: Wr.Dec<FEnv.Req>) -> {FEnv.ffi.go(d) == ChildEnv.ce_entry.go(d) : String}:
  match d:
    case Wr.Got{q, s}:
      pcs.whole(q, Wr.end(s))
    case Wr.Bad{}:
      {==}

def pcs.ffi(+s: String) -> {FEnv.ffi(s) == ChildEnv.ce_entry(s) : String}:
  %pcs.req(s) : {FEnv.ffi.go(FEnv.get_req(s)) == ChildEnv.ce_entry.go(_) : String}
  pcs.go(FEnv.get_req(s))
