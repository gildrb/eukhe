# eukhe: lemmas of LAW env_ffi_reads_only_requests (and
# env_ffi_malformed_unless_request): whatever the entry's decoder reads is
# the laws' spelling of what it read, then its rest, and fits the wire
#
# A variable: two strings (dcw.str: each decoded string is spelled and
# fits). A list of variables: its count (wire_nat_exact,
# wire_nat_decoded_fits), then as many spelled variables (pex.vs.loop, as
# dcw.strs.loop). A list of strings: wire_strs_exact,
# wire_strs_decoded_fit. The request: the four lists in order (pex.req.*,
# each stage carrying the input spelled up to its field: `pre`).

import Base
import ../../../bend/child_env.bend as Env
import ../../../bend/ffi_child_env.bend as FEnv
import ../../../bend/wire.bend as Wr
import ../../../laws/child_env.bend as ChildEnv
import ../../../laws/base.bend as LawsBase
import ../../../laws/wire.bend as Wire
import ../../wire/wire_nat_exact.bend as PWireNatExact
import ../../wire/wire_nat_decoded_fits.bend as PWireNatDecodedFits
import ../../wire/wire_strs_exact.bend as PWireStrsExact
import ../../wire/wire_strs_decoded_fit.bend as PWireStrsDecodedFit
import ../../wire/base/spell.bend as LAWireSpell
import ../../base/wire_dec.bend as LE

# s spelled up to a field a is s spelled up to its spelling b
def pex.step(-F: String -> String, -s: String, -a: String, -b: String, pre: {s == F(a) : String}, e: {a == b : String}) -> {s == F(b) : String}:
  Equal.trans(String, s, F(a), F(b), pre, Equal.cong(String, String, F, a, b, e))

# A variable
# ----------

def pex.VP(s: String, d: Wr.Dec<Env.Var>) -> Type:
  match d:
    case Wr.Got{v, r}:
      {s == ChildEnv.env_spell_var(v, r) : String} & {ChildEnv.env_var_fits(v) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def pex.var.value(-s: String, +n: String, -s1: String, pre: {s == Wr.put_str(n, s1) : String}, fn: {LawsBase.wire_fits(String.length(n)) == True{} : Bool}, d: Wr.Dec<String>, sp: LE.dcw.SP(s1, d)) -> pex.VP(s, FEnv.get_var.value(n, d)):
  match d:
    case Wr.Got{+x, +r}:
      (e, f) = sp
      (pex.step(z => Wr.put_str(n, z), s, s1, Wr.put_str(x, r), pre, e), LAWireSpell.ws_and_tt(ChildEnv.env_str_fits(n), ChildEnv.env_str_fits(x), fn, f))
    case Wr.Bad{}:
      Unit{}

def pex.var.name(-s: String, d: Wr.Dec<String>, sp: LE.dcw.SP(s, d)) -> pex.VP(s, FEnv.get_var.name(d)):
  match d:
    case Wr.Got{+n, +s1}:
      (e, f) = sp
      pex.var.value(s, n, s1, e, f, Wr.get_str(s1), LE.dcw.str(s1))
    case Wr.Bad{}:
      Unit{}

# a variable decoded is spelled, and fits
def pex.var(+s: String) -> pex.VP(s, FEnv.get_var(s)):
  pex.var.name(s, Wr.get_str(s), LE.dcw.str(s))

# A list of variables
# -------------------

# what the item loop's answer says about its input s (m + 1 items)
def pex.vs.PL(s: String, m: Nat, d: Wr.Dec<List<&2, Env.Var>>) -> Type:
  match d:
    case Wr.Got{+xs, r}:
      {s == ChildEnv.env_spell_vars.items(xs, r) : String} & ({List.length(&2, Env.Var, xs) == 1n+m : Nat} & {ChildEnv.env_vars_fit(xs) == True{} : Bool})
    case Wr.Bad{}:
      Unit

def pex.vs.step(-s: String, +x: Env.Var, +s3: String, -k: Nat, ex: {s == ChildEnv.env_spell_var(x, s3) : String}, fx: {ChildEnv.env_var_fits(x) == True{} : Bool}, d: Wr.Dec<List<&2, Env.Var>>, ih: pex.vs.PL(s3, k, d)) -> pex.vs.PL(s, 1n+k, Wr.get_list.cons(Env.Var, x, d)):
  match d:
    case Wr.Got{+ys, +r}:
      (e1, e23) = ih
      (e2, e3) = e23
      (pex.step(z => ChildEnv.env_spell_var(x, z), s, s3, ChildEnv.env_spell_vars.items(ys, r), ex, e1), (Equal.cong(Nat, Nat, k2 => 1n+k2, List.length(&2, Env.Var, ys), 1n+k, e2), LAWireSpell.ws_and_tt(ChildEnv.env_var_fits(x), ChildEnv.env_vars_fit(ys), fx, e3)))
    case Wr.Bad{}:
      Unit{}

# the item loop accepts only spelled variables that fit
def pex.vs.loop(m: Nat, cur: Wr.Dec<Env.Var>, +s: String, pc: pex.VP(s, cur)) -> pex.vs.PL(s, m, Wr.get_list.go(~Env.Var, ~FEnv.get_var, m, cur)):
  match m cur:
    case 0n Wr.Got{+x, +s3}:
      (e, f) = pc
      (e, ({==}, LAWireSpell.ws_and_tt(ChildEnv.env_var_fits(x), True{}, f, {==})))
    case 0n Wr.Bad{}:
      Unit{}
    case 1n++k Wr.Got{+x, +s3}:
      (e, f) = pc
      pex.vs.step(s, x, s3, k, e, f, Wr.get_list.go(~Env.Var, ~FEnv.get_var, k, FEnv.get_var(s3)), pex.vs.loop(k, FEnv.get_var(s3), s3, pex.var(s3)))
    case 1n++k Wr.Bad{}:
      Unit{}

# what a list decoder's answer says about its input s
def pex.vs.LS(s: String, d: Wr.Dec<List<&2, Env.Var>>) -> Type:
  match d:
    case Wr.Got{+xs, r}:
      {s == ChildEnv.env_spell_vars(xs, r) : String} & ({LawsBase.wire_fits(List.length(&2, Env.Var, xs)) == True{} : Bool} & {ChildEnv.env_vars_fit(xs) == True{} : Bool})
    case Wr.Bad{}:
      Unit

def pex.vs.conv_s(-s: String, -s2: String, -m: Nat, +xs: List<&2, Env.Var>, -r: String, en: {s == Wr.put_nat(1n+m, s2) : String}, e1: {s2 == ChildEnv.env_spell_vars.items(xs, r) : String}, e2: {List.length(&2, Env.Var, xs) == 1n+m : Nat}) -> {s == ChildEnv.env_spell_vars(xs, r) : String}:
  %Equal.sym(Nat, List.length(&2, Env.Var, xs), 1n+m, e2) : {s == Wr.put_nat(_, ChildEnv.env_spell_vars.items(xs, r)) : String}
  %e1 : {s == Wr.put_nat(1n+m, _) : String}
  en

def pex.vs.conv_f(-m: Nat, -xs: List<&2, Env.Var>, fn: {LawsBase.wire_fits(1n+m) == True{} : Bool}, e2: {List.length(&2, Env.Var, xs) == 1n+m : Nat}) -> {LawsBase.wire_fits(List.length(&2, Env.Var, xs)) == True{} : Bool}:
  %Equal.sym(Nat, List.length(&2, Env.Var, xs), 1n+m, e2) : {LawsBase.wire_fits(_) == True{} : Bool}
  fn

def pex.vs.conv(-s: String, -s2: String, -m: Nat, en: {s == Wr.put_nat(1n+m, s2) : String}, fn: {LawsBase.wire_fits(1n+m) == True{} : Bool}, d: Wr.Dec<List<&2, Env.Var>>, pl: pex.vs.PL(s2, m, d)) -> pex.vs.LS(s, d):
  match d:
    case Wr.Got{+xs, +r}:
      (e1, e23) = pl
      (+e2, e3) = e23
      (pex.vs.conv_s(s, s2, m, xs, r, en, e1, e2), (pex.vs.conv_f(m, xs, fn, e2), e3))
    case Wr.Bad{}:
      Unit{}

def pex.vs.nat(-s: String, n: Nat, +s2: String, en: {s == Wr.put_nat(n, s2) : String}, fn: {LawsBase.wire_fits(n) == True{} : Bool}) -> pex.vs.LS(s, Wr.get_list.start(~Env.Var, ~FEnv.get_var, Wr.Got{n, s2})):
  match n:
    case 0n:
      (en, (fn, {==}))
    case 1n++m:
      pex.vs.conv(s, s2, m, en, fn, Wr.get_list.go(~Env.Var, ~FEnv.get_var, m, FEnv.get_var(s2)), pex.vs.loop(m, FEnv.get_var(s2), s2, pex.var(s2)))

def pex.vs.top(+s: String, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s) == d : Wr.Dec<Nat>}) -> pex.vs.LS(s, Wr.get_list.start(~Env.Var, ~FEnv.get_var, d)):
  match d:
    case Wr.Got{+n, +s2}:
      +e = ed
      pex.vs.nat(s, n, s2, Wire.wire_nat_exact(s, n, s2, e), Wire.wire_nat_decoded_fits(s, n, s2, e))
    case Wr.Bad{}:
      Unit{}

# a list of variables decoded is spelled, and its count and every
# variable fit
def pex.vs.list(+s: String) -> pex.vs.LS(s, Wr.get_list(~Env.Var, ~FEnv.get_var, s)):
  pex.vs.top(s, Wr.get_nat(s), {==})

# A list of strings
# -----------------

# the wire's test of every string is the laws' of the area
def pex.ss.all(xs: List<&2, String>) -> {LawsBase.wire_strs_all(xs) == ChildEnv.env_strs_fit(xs) : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      Equal.cong(Bool, Bool, z => Bool.and(LawsBase.wire_fits(String.length(x)), z), LawsBase.wire_strs_all(t), ChildEnv.env_strs_fit(t), pex.ss.all(t))

def pex.ss.fit(+xs: List<&2, String>, h: {LawsBase.wire_strs_fit(xs) == True{} : Bool}) -> {Bool.and(LawsBase.wire_fits(List.length(&2, String, xs)), ChildEnv.env_strs_fit(xs)) == True{} : Bool}:
  %pex.ss.all(xs) : {Bool.and(LawsBase.wire_fits(List.length(&2, String, xs)), _) == True{} : Bool}
  h

# The request
# -----------

def pex.RP(s: String, d: Wr.Dec<FEnv.Req>) -> Type:
  match d:
    case Wr.Got{q, r}:
      {s == ChildEnv.env_spell_req(q, r) : String} & {ChildEnv.env_req_fits(q) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def pex.req.over(-s: String, +r: List<&2, String>, +k: List<&2, String>, +b: List<&2, Env.Var>, -s3: String, pre: {s == LawsBase.wire_spell_strs(r, LawsBase.wire_spell_strs(k, ChildEnv.env_spell_vars(b, s3))) : String}, f1: {Bool.and(LawsBase.wire_fits(List.length(&2, String, r)), ChildEnv.env_strs_fit(r)) == True{} : Bool}, f2: {Bool.and(LawsBase.wire_fits(List.length(&2, String, k)), ChildEnv.env_strs_fit(k)) == True{} : Bool}, f3: {Bool.and(LawsBase.wire_fits(List.length(&2, Env.Var, b)), ChildEnv.env_vars_fit(b)) == True{} : Bool}, d: Wr.Dec<List<&2, Env.Var>>, ls: pex.vs.LS(s3, d)) -> pex.RP(s, FEnv.get_req.over(r, k, b, d)):
  match d:
    case Wr.Got{+o, +s4}:
      (e4, g4) = ls
      (gn, gi) = g4
      +f4 = LAWireSpell.ws_and_tt(LawsBase.wire_fits(List.length(&2, Env.Var, o)), ChildEnv.env_vars_fit(o), gn, gi)
      +f34 = LAWireSpell.ws_and_tt(Bool.and(LawsBase.wire_fits(List.length(&2, Env.Var, b)), ChildEnv.env_vars_fit(b)), Bool.and(LawsBase.wire_fits(List.length(&2, Env.Var, o)), ChildEnv.env_vars_fit(o)), f3, f4)
      +f234 = LAWireSpell.ws_and_tt(Bool.and(LawsBase.wire_fits(List.length(&2, String, k)), ChildEnv.env_strs_fit(k)), Bool.and(Bool.and(LawsBase.wire_fits(List.length(&2, Env.Var, b)), ChildEnv.env_vars_fit(b)), Bool.and(LawsBase.wire_fits(List.length(&2, Env.Var, o)), ChildEnv.env_vars_fit(o))), f2, f34)
      (pex.step(z => LawsBase.wire_spell_strs(r, LawsBase.wire_spell_strs(k, ChildEnv.env_spell_vars(b, z))), s, s3, ChildEnv.env_spell_vars(o, s4), pre, e4), LAWireSpell.ws_and_tt(Bool.and(LawsBase.wire_fits(List.length(&2, String, r)), ChildEnv.env_strs_fit(r)), Bool.and(Bool.and(LawsBase.wire_fits(List.length(&2, String, k)), ChildEnv.env_strs_fit(k)), Bool.and(Bool.and(LawsBase.wire_fits(List.length(&2, Env.Var, b)), ChildEnv.env_vars_fit(b)), Bool.and(LawsBase.wire_fits(List.length(&2, Env.Var, o)), ChildEnv.env_vars_fit(o)))), f1, f234))
    case Wr.Bad{}:
      Unit{}

def pex.req.base(-s: String, +r: List<&2, String>, +k: List<&2, String>, -s2: String, pre: {s == LawsBase.wire_spell_strs(r, LawsBase.wire_spell_strs(k, s2)) : String}, f1: {Bool.and(LawsBase.wire_fits(List.length(&2, String, r)), ChildEnv.env_strs_fit(r)) == True{} : Bool}, f2: {Bool.and(LawsBase.wire_fits(List.length(&2, String, k)), ChildEnv.env_strs_fit(k)) == True{} : Bool}, d: Wr.Dec<List<&2, Env.Var>>, ls: pex.vs.LS(s2, d)) -> pex.RP(s, FEnv.get_req.base(r, k, d)):
  match d:
    case Wr.Got{+b, +s3}:
      (e3, g3) = ls
      (gn, gi) = g3
      pex.req.over(s, r, k, b, s3, pex.step(z => LawsBase.wire_spell_strs(r, LawsBase.wire_spell_strs(k, z)), s, s2, ChildEnv.env_spell_vars(b, s3), pre, e3), f1, f2, LAWireSpell.ws_and_tt(LawsBase.wire_fits(List.length(&2, Env.Var, b)), ChildEnv.env_vars_fit(b), gn, gi), Wr.get_list(~Env.Var, ~FEnv.get_var, s3), pex.vs.list(s3))
    case Wr.Bad{}:
      Unit{}

def pex.req.keep(-s: String, +r: List<&2, String>, +s1: String, pre: {s == LawsBase.wire_spell_strs(r, s1) : String}, f1: {Bool.and(LawsBase.wire_fits(List.length(&2, String, r)), ChildEnv.env_strs_fit(r)) == True{} : Bool}, d: Wr.Dec<List<&2, String>>, ed: {Wr.get_list(~String, ~Wr.get_str, s1) == d : Wr.Dec<List<&2, String>>}) -> pex.RP(s, FEnv.get_req.keep(r, d)):
  match d:
    case Wr.Got{+k, +s2}:
      +e = ed
      pex.req.base(s, r, k, s2, pex.step(z => LawsBase.wire_spell_strs(r, z), s, s1, LawsBase.wire_spell_strs(k, s2), pre, Wire.wire_strs_exact(s1, k, s2, e)), f1, pex.ss.fit(k, Wire.wire_strs_decoded_fit(s1, k, s2, e)), Wr.get_list(~Env.Var, ~FEnv.get_var, s2), pex.vs.list(s2))
    case Wr.Bad{}:
      Unit{}

def pex.req.reg(+s: String, d: Wr.Dec<List<&2, String>>, ed: {Wr.get_list(~String, ~Wr.get_str, s) == d : Wr.Dec<List<&2, String>>}) -> pex.RP(s, FEnv.get_req.reg(d)):
  match d:
    case Wr.Got{+r, +s1}:
      +e = ed
      pex.req.keep(s, r, s1, Wire.wire_strs_exact(s, r, s1, e), pex.ss.fit(r, Wire.wire_strs_decoded_fit(s, r, s1, e)), Wr.get_list(~String, ~Wr.get_str, s1), {==})
    case Wr.Bad{}:
      Unit{}

# whatever the entry's decoder reads is a spelled request that fits, then
# the rest
def pex.req(+s: String) -> pex.RP(s, FEnv.get_req(s)):
  pex.req.reg(s, Wr.get_list(~String, ~Wr.get_str, s), {==})
