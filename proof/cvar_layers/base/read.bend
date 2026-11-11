# eukhe: lemmas of the cvar_layers proofs: whatever the entry's decoder
# reads is the laws' spelling of what it read (laws/cvar_layers.bend
# spell_*), then its rest, and every number of it fits the wire. Stage by
# stage with the wire's exactness laws (wire_nat_exact, wire_bool_exact,
# wire_nat_decoded_fits): an unknown tag reads Bad; a list's count is its
# length (as proof/cvar/base/read.bend).

import Base
import ../../../bend/cvar.bend as Cv
import ../../../bend/ffi_cvar_layers.bend as FCL
import ../../../bend/wire.bend as Wr
import ../../../laws/cvar_layers.bend as Cl
import ../../../laws/base.bend as LawsBase
import ../../../laws/wire.bend as Wire
import ../../wire/wire_nat_exact.bend as PWireNatExact
import ../../wire/wire_nat_decoded_fits.bend as PWireNatDecodedFits
import ../../wire/wire_bool_exact.bend as PWireBoolExact
import ../../wire/base/spell.bend as LAWireSpell

# s spelled up to a field a is s spelled up to its spelling b
def clr.step(-F: String -> String, -s: String, -a: String, -b: String, pre: {s == F(a) : String}, e: {a == b : String}) -> {s == F(b) : String}:
  Equal.trans(String, s, F(a), F(b), pre, Equal.cong(String, String, F, a, b, e))

# n read with a count of 1 + m is a list of length 1 + m
def clr.len(-A: Data, -xs: List<&2, A>, -m: Nat, -G: Nat -> Type, g: G(1n+m), e: {List.length(&2, A, xs) == 1n+m : Nat}) -> G(List.length(&2, A, xs)):
  %Equal.sym(Nat, List.length(&2, A, xs), 1n+m, e) : G(_)
  g

# Values
# ------

def clr.Val(s: String, d: Wr.Dec<Cv.Val>) -> Type:
  match d:
    case Wr.Got{v, r}:
      {s == Cl.spell_val(v, r) : String} & {Cl.val_fits(v) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def clr.val.nat(+s: String, +s0: String, pre: {s == Wr.put_nat(0n, s0) : String}, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s0) == d : Wr.Dec<Nat>}) -> clr.Val(s, FCL.get_val.nat(d)):
  match d:
    case Wr.Got{+n, +s1}:
      +ee = ed
      (clr.step(z => Wr.put_nat(0n, z), s, s0, Wr.put_nat(n, s1), pre, Wire.wire_nat_exact(s0, n, s1, ee)), Wire.wire_nat_decoded_fits(s0, n, s1, ee))
    case Wr.Bad{}:
      Unit{}

def clr.val.bool(+s: String, +s0: String, pre: {s == Wr.put_nat(1n, s0) : String}, d: Wr.Dec<Bool>, ed: {Wr.get_bool(s0) == d : Wr.Dec<Bool>}) -> clr.Val(s, FCL.get_val.bool(d)):
  match d:
    case Wr.Got{+b, +s1}:
      (clr.step(z => Wr.put_nat(1n, z), s, s0, Wr.put_bool(b, s1), pre, Wire.wire_bool_exact(s0, b, s1, ed)), {==})
    case Wr.Bad{}:
      Unit{}

def clr.val.go(+s: String, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s) == d : Wr.Dec<Nat>}) -> clr.Val(s, FCL.get_val.go(d)):
  match d:
    case Wr.Got{+t, +s0}:
      match t:
        case 0n:
          clr.val.nat(s, s0, Wire.wire_nat_exact(s, 0n, s0, ed), Wr.get_nat(s0), {==})
        case 1n:
          clr.val.bool(s, s0, Wire.wire_nat_exact(s, 1n, s0, ed), Wr.get_bool(s0), {==})
        case 2n+k:
          Unit{}
    case Wr.Bad{}:
      Unit{}

# a value read is spelled and fits
def clr.val(+s: String) -> clr.Val(s, FCL.get_val(s)):
  clr.val.go(s, Wr.get_nat(s), {==})

# Types, scopes, layers, flags
# ----------------------------

def clr.Ty(s: String, d: Wr.Dec<Cv.Ty>) -> Type:
  match d:
    case Wr.Got{x, r}:
      {s == Cl.spell_ty(x, r) : String}
    case Wr.Bad{}:
      Unit

# a ty read is spelled
def clr.ty(+s: String, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s) == d : Wr.Dec<Nat>}) -> clr.Ty(s, FCL.get_ty.go(d)):
  match d:
    case Wr.Got{+t, +s0}:
      match t:
        case 0n:
          Wire.wire_nat_exact(s, 0n, s0, ed)
        case 1n:
          Wire.wire_nat_exact(s, 1n, s0, ed)
        case 2n+k:
          Unit{}
    case Wr.Bad{}:
      Unit{}

def clr.Scope(s: String, d: Wr.Dec<Cv.Scope>) -> Type:
  match d:
    case Wr.Got{x, r}:
      {s == Cl.spell_scope(x, r) : String}
    case Wr.Bad{}:
      Unit

# a scope read is spelled
def clr.scope(+s: String, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s) == d : Wr.Dec<Nat>}) -> clr.Scope(s, FCL.get_scope.go(d)):
  match d:
    case Wr.Got{+t, +s0}:
      match t:
        case 0n:
          Wire.wire_nat_exact(s, 0n, s0, ed)
        case 1n:
          Wire.wire_nat_exact(s, 1n, s0, ed)
        case 2n+k:
          Unit{}
    case Wr.Bad{}:
      Unit{}

def clr.Layer(s: String, d: Wr.Dec<Cv.Layer>) -> Type:
  match d:
    case Wr.Got{x, r}:
      {s == Cl.spell_layer(x, r) : String}
    case Wr.Bad{}:
      Unit

# a layer read is spelled
def clr.layer(+s: String, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s) == d : Wr.Dec<Nat>}) -> clr.Layer(s, FCL.get_layer.go(d)):
  match d:
    case Wr.Got{+t, +s0}:
      match t:
        case 0n:
          Wire.wire_nat_exact(s, 0n, s0, ed)
        case 1n:
          Wire.wire_nat_exact(s, 1n, s0, ed)
        case 2n+k:
          Unit{}
    case Wr.Bad{}:
      Unit{}

def clr.Flag(s: String, d: Wr.Dec<Cv.Flag>) -> Type:
  match d:
    case Wr.Got{x, r}:
      {s == Cl.spell_flag(x, r) : String}
    case Wr.Bad{}:
      Unit

# a flag read is spelled
def clr.flag(+s: String, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s) == d : Wr.Dec<Nat>}) -> clr.Flag(s, FCL.get_flag.go(d)):
  match d:
    case Wr.Got{+t, +s0}:
      match t:
        case 0n:
          Wire.wire_nat_exact(s, 0n, s0, ed)
        case 1n:
          Wire.wire_nat_exact(s, 1n, s0, ed)
        case 2n+k:
          Unit{}
    case Wr.Bad{}:
      Unit{}

# Declarations
# ------------

def clr.Decl(s: String, d: Wr.Dec<Cv.Decl>) -> Type:
  match d:
    case Wr.Got{x, r}:
      {s == Cl.spell_decl(x, r) : String} & {Cl.decl_fits(x) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def clr.decl.init(+s: String, +i: Nat, +t: Cv.Ty, +c: Cv.Scope, +p: Bool, +q: Bool, +s5: String, pre: {s == Wr.put_nat(i, Cl.spell_ty(t, Cl.spell_scope(c, Wr.put_bool(p, Wr.put_bool(q, s5))))) : String}, fi: {LawsBase.wire_fits(i) == True{} : Bool}, d: Wr.Dec<Cv.Val>, xd: clr.Val(s5, d)) -> clr.Decl(s, FCL.get_decl.init(i, t, c, p, q, d)):
  match d:
    case Wr.Got{+v, +s6}:
      (e, f) = xd
      (clr.step(z => Wr.put_nat(i, Cl.spell_ty(t, Cl.spell_scope(c, Wr.put_bool(p, Wr.put_bool(q, z))))), s, s5, Cl.spell_val(v, s6), pre, e), LAWireSpell.ws_and_tt(LawsBase.wire_fits(i), Cl.val_fits(v), fi, f))
    case Wr.Bad{}:
      Unit{}

def clr.decl.rep(+s: String, +i: Nat, +t: Cv.Ty, +c: Cv.Scope, +p: Bool, +s4: String, pre: {s == Wr.put_nat(i, Cl.spell_ty(t, Cl.spell_scope(c, Wr.put_bool(p, s4)))) : String}, fi: {LawsBase.wire_fits(i) == True{} : Bool}, d: Wr.Dec<Bool>, ed: {Wr.get_bool(s4) == d : Wr.Dec<Bool>}) -> clr.Decl(s, FCL.get_decl.rep(i, t, c, p, d)):
  match d:
    case Wr.Got{+q, +s5}:
      clr.decl.init(s, i, t, c, p, q, s5, clr.step(z => Wr.put_nat(i, Cl.spell_ty(t, Cl.spell_scope(c, Wr.put_bool(p, z)))), s, s4, Wr.put_bool(q, s5), pre, Wire.wire_bool_exact(s4, q, s5, ed)), fi, FCL.get_val(s5), clr.val(s5))
    case Wr.Bad{}:
      Unit{}

def clr.decl.per(+s: String, +i: Nat, +t: Cv.Ty, +c: Cv.Scope, +s3: String, pre: {s == Wr.put_nat(i, Cl.spell_ty(t, Cl.spell_scope(c, s3))) : String}, fi: {LawsBase.wire_fits(i) == True{} : Bool}, d: Wr.Dec<Bool>, ed: {Wr.get_bool(s3) == d : Wr.Dec<Bool>}) -> clr.Decl(s, FCL.get_decl.per(i, t, c, d)):
  match d:
    case Wr.Got{+p, +s4}:
      clr.decl.rep(s, i, t, c, p, s4, clr.step(z => Wr.put_nat(i, Cl.spell_ty(t, Cl.spell_scope(c, z))), s, s3, Wr.put_bool(p, s4), pre, Wire.wire_bool_exact(s3, p, s4, ed)), fi, Wr.get_bool(s4), {==})
    case Wr.Bad{}:
      Unit{}

def clr.decl.scope(+s: String, +i: Nat, +t: Cv.Ty, +s2: String, pre: {s == Wr.put_nat(i, Cl.spell_ty(t, s2)) : String}, fi: {LawsBase.wire_fits(i) == True{} : Bool}, d: Wr.Dec<Cv.Scope>, xd: clr.Scope(s2, d)) -> clr.Decl(s, FCL.get_decl.scope(i, t, d)):
  match d:
    case Wr.Got{+c, +s3}:
      clr.decl.per(s, i, t, c, s3, clr.step(z => Wr.put_nat(i, Cl.spell_ty(t, z)), s, s2, Cl.spell_scope(c, s3), pre, xd), fi, Wr.get_bool(s3), {==})
    case Wr.Bad{}:
      Unit{}

def clr.decl.ty(+s: String, +i: Nat, +s1: String, pre: {s == Wr.put_nat(i, s1) : String}, fi: {LawsBase.wire_fits(i) == True{} : Bool}, d: Wr.Dec<Cv.Ty>, xd: clr.Ty(s1, d)) -> clr.Decl(s, FCL.get_decl.ty(i, d)):
  match d:
    case Wr.Got{+t, +s2}:
      clr.decl.scope(s, i, t, s2, clr.step(z => Wr.put_nat(i, z), s, s1, Cl.spell_ty(t, s2), pre, xd), fi, FCL.get_scope.go(Wr.get_nat(s2)), clr.scope(s2, Wr.get_nat(s2), {==}))
    case Wr.Bad{}:
      Unit{}

def clr.decl.id(+s: String, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s) == d : Wr.Dec<Nat>}) -> clr.Decl(s, FCL.get_decl.id(d)):
  match d:
    case Wr.Got{+i, +s1}:
      +e = ed
      clr.decl.ty(s, i, s1, Wire.wire_nat_exact(s, i, s1, e), Wire.wire_nat_decoded_fits(s, i, s1, e), FCL.get_ty.go(Wr.get_nat(s1)), clr.ty(s1, Wr.get_nat(s1), {==}))
    case Wr.Bad{}:
      Unit{}

# a declaration read is spelled and fits
def clr.decl(+s: String) -> clr.Decl(s, FCL.get_decl(s)):
  clr.decl.id(s, Wr.get_nat(s), {==})

# Declaration lists
# -----------------

# what the item loop's answer says about its input s (m + 1 items)
def clr.decls.PL(s: String, m: Nat, d: Wr.Dec<List<&2, Cv.Decl>>) -> Type:
  match d:
    case Wr.Got{+xs, r}:
      {s == Cl.spell_decls.items(xs, r) : String} & ({List.length(&2, Cv.Decl, xs) == 1n+m : Nat} & {Cl.decls_all(xs) == True{} : Bool})
    case Wr.Bad{}:
      Unit

def clr.decls.step(-s: String, +x: Cv.Decl, +s3: String, -k: Nat, ex: {s == Cl.spell_decl(x, s3) : String}, fx: {Cl.decl_fits(x) == True{} : Bool}, d: Wr.Dec<List<&2, Cv.Decl>>, ih: clr.decls.PL(s3, k, d)) -> clr.decls.PL(s, 1n+k, FCL.get_decls.cons(x, d)):
  match d:
    case Wr.Got{+ys, +r}:
      (e1, e23) = ih
      (e2, e3) = e23
      (Equal.trans(String, s, Cl.spell_decl(x, s3), Cl.spell_decl(x, Cl.spell_decls.items(ys, r)), ex, Equal.cong(String, String, z => Cl.spell_decl(x, z), s3, Cl.spell_decls.items(ys, r), e1)), (Equal.cong(Nat, Nat, k2 => 1n+k2, List.length(&2, Cv.Decl, ys), 1n+k, e2), LAWireSpell.ws_and_tt(Cl.decl_fits(x), Cl.decls_all(ys), fx, e3)))
    case Wr.Bad{}:
      Unit{}

def clr.decls.loop(m: Nat, cur: Wr.Dec<Cv.Decl>, +s: String, pc: clr.Decl(s, cur)) -> clr.decls.PL(s, m, FCL.get_decls.go(m, cur)):
  match m cur:
    case 0n Wr.Got{+x, +s3}:
      (e, f) = pc
      (e, ({==}, LAWireSpell.ws_and_tt(Cl.decl_fits(x), True{}, f, {==})))
    case 0n Wr.Bad{}:
      Unit{}
    case 1n++k Wr.Got{+x, +s3}:
      (e, f) = pc
      clr.decls.step(s, x, s3, k, e, f, FCL.get_decls.go(k, FCL.get_decl(s3)), clr.decls.loop(k, FCL.get_decl(s3), s3, clr.decl(s3)))
    case 1n++k Wr.Bad{}:
      Unit{}

def clr.Decls(s: String, d: Wr.Dec<List<&2, Cv.Decl>>) -> Type:
  match d:
    case Wr.Got{+xs, r}:
      {s == Cl.spell_decls(xs, r) : String} & {Cl.decls_fit(xs) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def clr.decls.conv(-s: String, -s2: String, -m: Nat, en: {s == Wr.put_nat(1n+m, s2) : String}, fn: {LawsBase.wire_fits(1n+m) == True{} : Bool}, d: Wr.Dec<List<&2, Cv.Decl>>, pl: clr.decls.PL(s2, m, d)) -> clr.Decls(s, d):
  match d:
    case Wr.Got{+xs, +r}:
      (e1, e23) = pl
      (+e2, e3) = e23
      +es = clr.step(z => Wr.put_nat(1n+m, z), s, s2, Cl.spell_decls.items(xs, r), en, e1)
      (clr.len(Cv.Decl, xs, m, n => {s == Wr.put_nat(n, Cl.spell_decls.items(xs, r)) : String}, es, e2), LAWireSpell.ws_and_tt(LawsBase.wire_fits(List.length(&2, Cv.Decl, xs)), Cl.decls_all(xs), clr.len(Cv.Decl, xs, m, n => {LawsBase.wire_fits(n) == True{} : Bool}, fn, e2), e3))
    case Wr.Bad{}:
      Unit{}

def clr.decls.nat(-s: String, n: Nat, +s2: String, en: {s == Wr.put_nat(n, s2) : String}, fn: {LawsBase.wire_fits(n) == True{} : Bool}) -> clr.Decls(s, FCL.get_decls(Wr.Got{n, s2})):
  match n:
    case 0n:
      (en, LAWireSpell.ws_and_tt(LawsBase.wire_fits(0n), True{}, fn, {==}))
    case 1n++m:
      clr.decls.conv(s, s2, m, en, fn, FCL.get_decls.go(m, FCL.get_decl(s2)), clr.decls.loop(m, FCL.get_decl(s2), s2, clr.decl(s2)))

def clr.decls.top(+s: String, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s) == d : Wr.Dec<Nat>}) -> clr.Decls(s, FCL.get_decls(d)):
  match d:
    case Wr.Got{+n, +s2}:
      +e = ed
      clr.decls.nat(s, n, s2, Wire.wire_nat_exact(s, n, s2, e), Wire.wire_nat_decoded_fits(s, n, s2, e))
    case Wr.Bad{}:
      Unit{}

# a list of declarations read is spelled and fits
def clr.decls(+s: String) -> clr.Decls(s, FCL.get_decls(Wr.get_nat(s))):
  clr.decls.top(s, Wr.get_nat(s), {==})

# Sets
# ----

def clr.Bind(s: String, d: Wr.Dec<Cv.Bind>) -> Type:
  match d:
    case Wr.Got{x, r}:
      {s == Cl.spell_bind(x, r) : String} & {Cl.bind_fits(x) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def clr.bind.val(+s: String, +i: Nat, +s1: String, pre: {s == Wr.put_nat(i, s1) : String}, fi: {LawsBase.wire_fits(i) == True{} : Bool}, d: Wr.Dec<Cv.Val>, xd: clr.Val(s1, d)) -> clr.Bind(s, FCL.get_bind.val(i, d)):
  match d:
    case Wr.Got{+v, +s2}:
      (e, f) = xd
      (clr.step(z => Wr.put_nat(i, z), s, s1, Cl.spell_val(v, s2), pre, e), LAWireSpell.ws_and_tt(LawsBase.wire_fits(i), Cl.val_fits(v), fi, f))
    case Wr.Bad{}:
      Unit{}

def clr.bind.id(+s: String, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s) == d : Wr.Dec<Nat>}) -> clr.Bind(s, FCL.get_bind.id(d)):
  match d:
    case Wr.Got{+i, +s1}:
      +e = ed
      clr.bind.val(s, i, s1, Wire.wire_nat_exact(s, i, s1, e), Wire.wire_nat_decoded_fits(s, i, s1, e), FCL.get_val(s1), clr.val(s1))
    case Wr.Bad{}:
      Unit{}

# a set read is spelled and fits
def clr.bind(+s: String) -> clr.Bind(s, FCL.get_bind(s)):
  clr.bind.id(s, Wr.get_nat(s), {==})

# Set lists
# ---------

# what the item loop's answer says about its input s (m + 1 items)
def clr.binds.PL(s: String, m: Nat, d: Wr.Dec<List<&2, Cv.Bind>>) -> Type:
  match d:
    case Wr.Got{+xs, r}:
      {s == Cl.spell_binds.items(xs, r) : String} & ({List.length(&2, Cv.Bind, xs) == 1n+m : Nat} & {Cl.binds_all(xs) == True{} : Bool})
    case Wr.Bad{}:
      Unit

def clr.binds.step(-s: String, +x: Cv.Bind, +s3: String, -k: Nat, ex: {s == Cl.spell_bind(x, s3) : String}, fx: {Cl.bind_fits(x) == True{} : Bool}, d: Wr.Dec<List<&2, Cv.Bind>>, ih: clr.binds.PL(s3, k, d)) -> clr.binds.PL(s, 1n+k, FCL.get_binds.cons(x, d)):
  match d:
    case Wr.Got{+ys, +r}:
      (e1, e23) = ih
      (e2, e3) = e23
      (Equal.trans(String, s, Cl.spell_bind(x, s3), Cl.spell_bind(x, Cl.spell_binds.items(ys, r)), ex, Equal.cong(String, String, z => Cl.spell_bind(x, z), s3, Cl.spell_binds.items(ys, r), e1)), (Equal.cong(Nat, Nat, k2 => 1n+k2, List.length(&2, Cv.Bind, ys), 1n+k, e2), LAWireSpell.ws_and_tt(Cl.bind_fits(x), Cl.binds_all(ys), fx, e3)))
    case Wr.Bad{}:
      Unit{}

def clr.binds.loop(m: Nat, cur: Wr.Dec<Cv.Bind>, +s: String, pc: clr.Bind(s, cur)) -> clr.binds.PL(s, m, FCL.get_binds.go(m, cur)):
  match m cur:
    case 0n Wr.Got{+x, +s3}:
      (e, f) = pc
      (e, ({==}, LAWireSpell.ws_and_tt(Cl.bind_fits(x), True{}, f, {==})))
    case 0n Wr.Bad{}:
      Unit{}
    case 1n++k Wr.Got{+x, +s3}:
      (e, f) = pc
      clr.binds.step(s, x, s3, k, e, f, FCL.get_binds.go(k, FCL.get_bind(s3)), clr.binds.loop(k, FCL.get_bind(s3), s3, clr.bind(s3)))
    case 1n++k Wr.Bad{}:
      Unit{}

def clr.Binds(s: String, d: Wr.Dec<List<&2, Cv.Bind>>) -> Type:
  match d:
    case Wr.Got{+xs, r}:
      {s == Cl.spell_binds(xs, r) : String} & {Cl.binds_fit(xs) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def clr.binds.conv(-s: String, -s2: String, -m: Nat, en: {s == Wr.put_nat(1n+m, s2) : String}, fn: {LawsBase.wire_fits(1n+m) == True{} : Bool}, d: Wr.Dec<List<&2, Cv.Bind>>, pl: clr.binds.PL(s2, m, d)) -> clr.Binds(s, d):
  match d:
    case Wr.Got{+xs, +r}:
      (e1, e23) = pl
      (+e2, e3) = e23
      +es = clr.step(z => Wr.put_nat(1n+m, z), s, s2, Cl.spell_binds.items(xs, r), en, e1)
      (clr.len(Cv.Bind, xs, m, n => {s == Wr.put_nat(n, Cl.spell_binds.items(xs, r)) : String}, es, e2), LAWireSpell.ws_and_tt(LawsBase.wire_fits(List.length(&2, Cv.Bind, xs)), Cl.binds_all(xs), clr.len(Cv.Bind, xs, m, n => {LawsBase.wire_fits(n) == True{} : Bool}, fn, e2), e3))
    case Wr.Bad{}:
      Unit{}

def clr.binds.nat(-s: String, n: Nat, +s2: String, en: {s == Wr.put_nat(n, s2) : String}, fn: {LawsBase.wire_fits(n) == True{} : Bool}) -> clr.Binds(s, FCL.get_binds(Wr.Got{n, s2})):
  match n:
    case 0n:
      (en, LAWireSpell.ws_and_tt(LawsBase.wire_fits(0n), True{}, fn, {==}))
    case 1n++m:
      clr.binds.conv(s, s2, m, en, fn, FCL.get_binds.go(m, FCL.get_bind(s2)), clr.binds.loop(m, FCL.get_bind(s2), s2, clr.bind(s2)))

def clr.binds.top(+s: String, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s) == d : Wr.Dec<Nat>}) -> clr.Binds(s, FCL.get_binds(d)):
  match d:
    case Wr.Got{+n, +s2}:
      +e = ed
      clr.binds.nat(s, n, s2, Wire.wire_nat_exact(s, n, s2, e), Wire.wire_nat_decoded_fits(s, n, s2, e))
    case Wr.Bad{}:
      Unit{}

# a list of sets read is spelled and fits
def clr.binds(+s: String) -> clr.Binds(s, FCL.get_binds(Wr.get_nat(s))):
  clr.binds.top(s, Wr.get_nat(s), {==})

# Agents
# ------

def clr.Ag(s: String, d: Wr.Dec<Cv.Ag>) -> Type:
  match d:
    case Wr.Got{x, r}:
      {s == Cl.spell_ag(x, r) : String} & {Cl.ag_fits(x) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def clr.ag.sets(+s: String, +p: List<&2, Cv.Bind>, +s1: String, pre: {s == Cl.spell_binds(p, s1) : String}, fp: {Cl.binds_fit(p) == True{} : Bool}, d: Wr.Dec<List<&2, Cv.Bind>>, xd: clr.Binds(s1, d)) -> clr.Ag(s, FCL.get_ag.sets(p, d)):
  match d:
    case Wr.Got{+ss, +s2}:
      (e, f) = xd
      (clr.step(z => Cl.spell_binds(p, z), s, s1, Cl.spell_binds(ss, s2), pre, e), LAWireSpell.ws_and_tt(Cl.binds_fit(p), Cl.binds_fit(ss), fp, f))
    case Wr.Bad{}:
      Unit{}

def clr.ag.profile(+s: String, d: Wr.Dec<List<&2, Cv.Bind>>, xd: clr.Binds(s, d)) -> clr.Ag(s, FCL.get_ag.profile(d)):
  match d:
    case Wr.Got{+p, +s1}:
      (e, f) = xd
      clr.ag.sets(s, p, s1, e, f, FCL.get_binds(Wr.get_nat(s1)), clr.binds(s1))
    case Wr.Bad{}:
      Unit{}

# an agent read is spelled and fits
def clr.ag(+s: String) -> clr.Ag(s, FCL.get_ag(s)):
  clr.ag.profile(s, FCL.get_binds(Wr.get_nat(s)), clr.binds(s))

# Agent lists
# -----------

# what the item loop's answer says about its input s (m + 1 items)
def clr.ags.PL(s: String, m: Nat, d: Wr.Dec<List<&2, Cv.Ag>>) -> Type:
  match d:
    case Wr.Got{+xs, r}:
      {s == Cl.spell_ags.items(xs, r) : String} & ({List.length(&2, Cv.Ag, xs) == 1n+m : Nat} & {Cl.ags_all(xs) == True{} : Bool})
    case Wr.Bad{}:
      Unit

def clr.ags.step(-s: String, +x: Cv.Ag, +s3: String, -k: Nat, ex: {s == Cl.spell_ag(x, s3) : String}, fx: {Cl.ag_fits(x) == True{} : Bool}, d: Wr.Dec<List<&2, Cv.Ag>>, ih: clr.ags.PL(s3, k, d)) -> clr.ags.PL(s, 1n+k, FCL.get_ags.cons(x, d)):
  match d:
    case Wr.Got{+ys, +r}:
      (e1, e23) = ih
      (e2, e3) = e23
      (Equal.trans(String, s, Cl.spell_ag(x, s3), Cl.spell_ag(x, Cl.spell_ags.items(ys, r)), ex, Equal.cong(String, String, z => Cl.spell_ag(x, z), s3, Cl.spell_ags.items(ys, r), e1)), (Equal.cong(Nat, Nat, k2 => 1n+k2, List.length(&2, Cv.Ag, ys), 1n+k, e2), LAWireSpell.ws_and_tt(Cl.ag_fits(x), Cl.ags_all(ys), fx, e3)))
    case Wr.Bad{}:
      Unit{}

def clr.ags.loop(m: Nat, cur: Wr.Dec<Cv.Ag>, +s: String, pc: clr.Ag(s, cur)) -> clr.ags.PL(s, m, FCL.get_ags.go(m, cur)):
  match m cur:
    case 0n Wr.Got{+x, +s3}:
      (e, f) = pc
      (e, ({==}, LAWireSpell.ws_and_tt(Cl.ag_fits(x), True{}, f, {==})))
    case 0n Wr.Bad{}:
      Unit{}
    case 1n++k Wr.Got{+x, +s3}:
      (e, f) = pc
      clr.ags.step(s, x, s3, k, e, f, FCL.get_ags.go(k, FCL.get_ag(s3)), clr.ags.loop(k, FCL.get_ag(s3), s3, clr.ag(s3)))
    case 1n++k Wr.Bad{}:
      Unit{}

def clr.Ags(s: String, d: Wr.Dec<List<&2, Cv.Ag>>) -> Type:
  match d:
    case Wr.Got{+xs, r}:
      {s == Cl.spell_ags(xs, r) : String} & {Cl.ags_fit(xs) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def clr.ags.conv(-s: String, -s2: String, -m: Nat, en: {s == Wr.put_nat(1n+m, s2) : String}, fn: {LawsBase.wire_fits(1n+m) == True{} : Bool}, d: Wr.Dec<List<&2, Cv.Ag>>, pl: clr.ags.PL(s2, m, d)) -> clr.Ags(s, d):
  match d:
    case Wr.Got{+xs, +r}:
      (e1, e23) = pl
      (+e2, e3) = e23
      +es = clr.step(z => Wr.put_nat(1n+m, z), s, s2, Cl.spell_ags.items(xs, r), en, e1)
      (clr.len(Cv.Ag, xs, m, n => {s == Wr.put_nat(n, Cl.spell_ags.items(xs, r)) : String}, es, e2), LAWireSpell.ws_and_tt(LawsBase.wire_fits(List.length(&2, Cv.Ag, xs)), Cl.ags_all(xs), clr.len(Cv.Ag, xs, m, n => {LawsBase.wire_fits(n) == True{} : Bool}, fn, e2), e3))
    case Wr.Bad{}:
      Unit{}

def clr.ags.nat(-s: String, n: Nat, +s2: String, en: {s == Wr.put_nat(n, s2) : String}, fn: {LawsBase.wire_fits(n) == True{} : Bool}) -> clr.Ags(s, FCL.get_ags(Wr.Got{n, s2})):
  match n:
    case 0n:
      (en, LAWireSpell.ws_and_tt(LawsBase.wire_fits(0n), True{}, fn, {==}))
    case 1n++m:
      clr.ags.conv(s, s2, m, en, fn, FCL.get_ags.go(m, FCL.get_ag(s2)), clr.ags.loop(m, FCL.get_ag(s2), s2, clr.ag(s2)))

def clr.ags.top(+s: String, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s) == d : Wr.Dec<Nat>}) -> clr.Ags(s, FCL.get_ags(d)):
  match d:
    case Wr.Got{+n, +s2}:
      +e = ed
      clr.ags.nat(s, n, s2, Wire.wire_nat_exact(s, n, s2, e), Wire.wire_nat_decoded_fits(s, n, s2, e))
    case Wr.Bad{}:
      Unit{}

# a list of agents read is spelled and fits
def clr.ags(+s: String) -> clr.Ags(s, FCL.get_ags(Wr.get_nat(s))):
  clr.ags.top(s, Wr.get_nat(s), {==})

# Requests
# --------

# the request a spelled as the grammar spells it, then rest (spell_ask is
# this with nothing after it: clr.ask_onto_nil)
def clr.ask_onto(a: FCL.Ask, rest: String) -> String:
  match a:
    case FCL.AskRegistry{ds}:
      Wr.put_nat(0n, Cl.spell_decls(ds, rest))
    case FCL.AskValues{ds, c, f}:
      Wr.put_nat(1n, Cl.spell_decls(ds, Cl.spell_binds(c, Cl.spell_ags(f, rest))))
    case FCL.AskToggle{ds, c, f, l, x}:
      Wr.put_nat(2n, Cl.spell_decls(ds, Cl.spell_binds(c, Cl.spell_ags(f, Cl.spell_layer(l, Wr.put_nat(x, rest))))))
    case FCL.AskCheck{ds, l, b}:
      Wr.put_nat(3n, Cl.spell_decls(ds, Cl.spell_layer(l, Cl.spell_bind(b, rest))))
    case FCL.AskWritten{ds, ss, g}:
      Wr.put_nat(4n, Cl.spell_decls(ds, Cl.spell_binds(ss, Cl.spell_flag(g, rest))))
    case FCL.AskDocument{ds, m, g}:
      Wr.put_nat(5n, Cl.spell_decls(ds, Cl.spell_binds(m, Cl.spell_binds(g, rest))))

def clr.ask_onto_nil(a: FCL.Ask) -> {clr.ask_onto(a, "") == Cl.spell_ask(a) : String}:
  match a:
    case FCL.AskRegistry{ds}:
      {==}
    case FCL.AskValues{ds, c, f}:
      {==}
    case FCL.AskToggle{ds, c, f, l, x}:
      {==}
    case FCL.AskCheck{ds, l, b}:
      {==}
    case FCL.AskWritten{ds, ss, g}:
      {==}
    case FCL.AskDocument{ds, m, g}:
      {==}

def clr.Ask(s: String, d: Wr.Dec<FCL.Ask>) -> Type:
  match d:
    case Wr.Got{a, r}:
      {s == clr.ask_onto(a, r) : String} & {Cl.ask_fits(a) == True{} : Bool}
    case Wr.Bad{}:
      Unit

# 0: the registry
def clr.ask.reg(+s: String, +s0: String, pre: {s == Wr.put_nat(0n, s0) : String}, d: Wr.Dec<List<&2, Cv.Decl>>, xd: clr.Decls(s0, d)) -> clr.Ask(s, FCL.get_reg(d)):
  match d:
    case Wr.Got{+ds, +s1}:
      (e, f) = xd
      (clr.step(z => Wr.put_nat(0n, z), s, s0, Cl.spell_decls(ds, s1), pre, e), f)
    case Wr.Bad{}:
      Unit{}

# 1: the values
def clr.ask.vals_fam(+s: String, +ds: List<&2, Cv.Decl>, +c: List<&2, Cv.Bind>, +s2: String, pre: {s == Wr.put_nat(1n, Cl.spell_decls(ds, Cl.spell_binds(c, s2))) : String}, fd: {Cl.decls_fit(ds) == True{} : Bool}, fc: {Cl.binds_fit(c) == True{} : Bool}, d: Wr.Dec<List<&2, Cv.Ag>>, xd: clr.Ags(s2, d)) -> clr.Ask(s, FCL.get_vals.fam(ds, c, d)):
  match d:
    case Wr.Got{+f, +s3}:
      (e, g) = xd
      (clr.step(z => Wr.put_nat(1n, Cl.spell_decls(ds, Cl.spell_binds(c, z))), s, s2, Cl.spell_ags(f, s3), pre, e), LAWireSpell.ws_and_tt(Cl.decls_fit(ds), Bool.and(Cl.binds_fit(c), Cl.ags_fit(f)), fd, LAWireSpell.ws_and_tt(Cl.binds_fit(c), Cl.ags_fit(f), fc, g)))
    case Wr.Bad{}:
      Unit{}

def clr.ask.vals_cfg(+s: String, +ds: List<&2, Cv.Decl>, +s1: String, pre: {s == Wr.put_nat(1n, Cl.spell_decls(ds, s1)) : String}, fd: {Cl.decls_fit(ds) == True{} : Bool}, d: Wr.Dec<List<&2, Cv.Bind>>, xd: clr.Binds(s1, d)) -> clr.Ask(s, FCL.get_vals.cfg(ds, d)):
  match d:
    case Wr.Got{+c, +s2}:
      (e, f) = xd
      clr.ask.vals_fam(s, ds, c, s2, clr.step(z => Wr.put_nat(1n, Cl.spell_decls(ds, z)), s, s1, Cl.spell_binds(c, s2), pre, e), fd, f, FCL.get_ags(Wr.get_nat(s2)), clr.ags(s2))
    case Wr.Bad{}:
      Unit{}

def clr.ask.vals(+s: String, +s0: String, pre: {s == Wr.put_nat(1n, s0) : String}, d: Wr.Dec<List<&2, Cv.Decl>>, xd: clr.Decls(s0, d)) -> clr.Ask(s, FCL.get_vals(d)):
  match d:
    case Wr.Got{+ds, +s1}:
      (e, f) = xd
      clr.ask.vals_cfg(s, ds, s1, clr.step(z => Wr.put_nat(1n, z), s, s0, Cl.spell_decls(ds, s1), pre, e), f, FCL.get_binds(Wr.get_nat(s1)), clr.binds(s1))
    case Wr.Bad{}:
      Unit{}

# 2: a toggle
def clr.ask.tog_id(+s: String, +ds: List<&2, Cv.Decl>, +c: List<&2, Cv.Bind>, +f: List<&2, Cv.Ag>, +l: Cv.Layer, +s4: String, pre: {s == Wr.put_nat(2n, Cl.spell_decls(ds, Cl.spell_binds(c, Cl.spell_ags(f, Cl.spell_layer(l, s4))))) : String}, fd: {Cl.decls_fit(ds) == True{} : Bool}, fc: {Cl.binds_fit(c) == True{} : Bool}, ff: {Cl.ags_fit(f) == True{} : Bool}, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s4) == d : Wr.Dec<Nat>}) -> clr.Ask(s, FCL.get_tog.id(ds, c, f, l, d)):
  match d:
    case Wr.Got{+x, +s5}:
      +e = ed
      (clr.step(z => Wr.put_nat(2n, Cl.spell_decls(ds, Cl.spell_binds(c, Cl.spell_ags(f, Cl.spell_layer(l, z))))), s, s4, Wr.put_nat(x, s5), pre, Wire.wire_nat_exact(s4, x, s5, e)), LAWireSpell.ws_and_tt(Cl.decls_fit(ds), Bool.and(Cl.binds_fit(c), Bool.and(Cl.ags_fit(f), LawsBase.wire_fits(x))), fd, LAWireSpell.ws_and_tt(Cl.binds_fit(c), Bool.and(Cl.ags_fit(f), LawsBase.wire_fits(x)), fc, LAWireSpell.ws_and_tt(Cl.ags_fit(f), LawsBase.wire_fits(x), ff, Wire.wire_nat_decoded_fits(s4, x, s5, e)))))
    case Wr.Bad{}:
      Unit{}

def clr.ask.tog_layer(+s: String, +ds: List<&2, Cv.Decl>, +c: List<&2, Cv.Bind>, +f: List<&2, Cv.Ag>, +s3: String, pre: {s == Wr.put_nat(2n, Cl.spell_decls(ds, Cl.spell_binds(c, Cl.spell_ags(f, s3)))) : String}, fd: {Cl.decls_fit(ds) == True{} : Bool}, fc: {Cl.binds_fit(c) == True{} : Bool}, ff: {Cl.ags_fit(f) == True{} : Bool}, d: Wr.Dec<Cv.Layer>, xd: clr.Layer(s3, d)) -> clr.Ask(s, FCL.get_tog.layer(ds, c, f, d)):
  match d:
    case Wr.Got{+l, +s4}:
      clr.ask.tog_id(s, ds, c, f, l, s4, clr.step(z => Wr.put_nat(2n, Cl.spell_decls(ds, Cl.spell_binds(c, Cl.spell_ags(f, z)))), s, s3, Cl.spell_layer(l, s4), pre, xd), fd, fc, ff, Wr.get_nat(s4), {==})
    case Wr.Bad{}:
      Unit{}

def clr.ask.tog_fam(+s: String, +ds: List<&2, Cv.Decl>, +c: List<&2, Cv.Bind>, +s2: String, pre: {s == Wr.put_nat(2n, Cl.spell_decls(ds, Cl.spell_binds(c, s2))) : String}, fd: {Cl.decls_fit(ds) == True{} : Bool}, fc: {Cl.binds_fit(c) == True{} : Bool}, d: Wr.Dec<List<&2, Cv.Ag>>, xd: clr.Ags(s2, d)) -> clr.Ask(s, FCL.get_tog.fam(ds, c, d)):
  match d:
    case Wr.Got{+f, +s3}:
      (e, g) = xd
      clr.ask.tog_layer(s, ds, c, f, s3, clr.step(z => Wr.put_nat(2n, Cl.spell_decls(ds, Cl.spell_binds(c, z))), s, s2, Cl.spell_ags(f, s3), pre, e), fd, fc, g, FCL.get_layer.go(Wr.get_nat(s3)), clr.layer(s3, Wr.get_nat(s3), {==}))
    case Wr.Bad{}:
      Unit{}

def clr.ask.tog_cfg(+s: String, +ds: List<&2, Cv.Decl>, +s1: String, pre: {s == Wr.put_nat(2n, Cl.spell_decls(ds, s1)) : String}, fd: {Cl.decls_fit(ds) == True{} : Bool}, d: Wr.Dec<List<&2, Cv.Bind>>, xd: clr.Binds(s1, d)) -> clr.Ask(s, FCL.get_tog.cfg(ds, d)):
  match d:
    case Wr.Got{+c, +s2}:
      (e, g) = xd
      clr.ask.tog_fam(s, ds, c, s2, clr.step(z => Wr.put_nat(2n, Cl.spell_decls(ds, z)), s, s1, Cl.spell_binds(c, s2), pre, e), fd, g, FCL.get_ags(Wr.get_nat(s2)), clr.ags(s2))
    case Wr.Bad{}:
      Unit{}

def clr.ask.tog(+s: String, +s0: String, pre: {s == Wr.put_nat(2n, s0) : String}, d: Wr.Dec<List<&2, Cv.Decl>>, xd: clr.Decls(s0, d)) -> clr.Ask(s, FCL.get_tog(d)):
  match d:
    case Wr.Got{+ds, +s1}:
      (e, f) = xd
      clr.ask.tog_cfg(s, ds, s1, clr.step(z => Wr.put_nat(2n, z), s, s0, Cl.spell_decls(ds, s1), pre, e), f, FCL.get_binds(Wr.get_nat(s1)), clr.binds(s1))
    case Wr.Bad{}:
      Unit{}

# 3: a check
def clr.ask.chk_set(+s: String, +ds: List<&2, Cv.Decl>, +l: Cv.Layer, +s2: String, pre: {s == Wr.put_nat(3n, Cl.spell_decls(ds, Cl.spell_layer(l, s2))) : String}, fd: {Cl.decls_fit(ds) == True{} : Bool}, d: Wr.Dec<Cv.Bind>, xd: clr.Bind(s2, d)) -> clr.Ask(s, FCL.get_chk.set(ds, l, d)):
  match d:
    case Wr.Got{+b, +s3}:
      (e, g) = xd
      (clr.step(z => Wr.put_nat(3n, Cl.spell_decls(ds, Cl.spell_layer(l, z))), s, s2, Cl.spell_bind(b, s3), pre, e), LAWireSpell.ws_and_tt(Cl.decls_fit(ds), Cl.bind_fits(b), fd, g))
    case Wr.Bad{}:
      Unit{}

def clr.ask.chk_layer(+s: String, +ds: List<&2, Cv.Decl>, +s1: String, pre: {s == Wr.put_nat(3n, Cl.spell_decls(ds, s1)) : String}, fd: {Cl.decls_fit(ds) == True{} : Bool}, d: Wr.Dec<Cv.Layer>, xd: clr.Layer(s1, d)) -> clr.Ask(s, FCL.get_chk.layer(ds, d)):
  match d:
    case Wr.Got{+l, +s2}:
      clr.ask.chk_set(s, ds, l, s2, clr.step(z => Wr.put_nat(3n, Cl.spell_decls(ds, z)), s, s1, Cl.spell_layer(l, s2), pre, xd), fd, FCL.get_bind(s2), clr.bind(s2))
    case Wr.Bad{}:
      Unit{}

def clr.ask.chk(+s: String, +s0: String, pre: {s == Wr.put_nat(3n, s0) : String}, d: Wr.Dec<List<&2, Cv.Decl>>, xd: clr.Decls(s0, d)) -> clr.Ask(s, FCL.get_chk(d)):
  match d:
    case Wr.Got{+ds, +s1}:
      (e, f) = xd
      clr.ask.chk_layer(s, ds, s1, clr.step(z => Wr.put_nat(3n, z), s, s0, Cl.spell_decls(ds, s1), pre, e), f, FCL.get_layer.go(Wr.get_nat(s1)), clr.layer(s1, Wr.get_nat(s1), {==}))
    case Wr.Bad{}:
      Unit{}

# 4: the sets written
def clr.ask.wr_flag(+s: String, +ds: List<&2, Cv.Decl>, +ss: List<&2, Cv.Bind>, +s2: String, pre: {s == Wr.put_nat(4n, Cl.spell_decls(ds, Cl.spell_binds(ss, s2))) : String}, fd: {Cl.decls_fit(ds) == True{} : Bool}, fs: {Cl.binds_fit(ss) == True{} : Bool}, d: Wr.Dec<Cv.Flag>, xd: clr.Flag(s2, d)) -> clr.Ask(s, FCL.get_wr.flag(ds, ss, d)):
  match d:
    case Wr.Got{+g, +s3}:
      (clr.step(z => Wr.put_nat(4n, Cl.spell_decls(ds, Cl.spell_binds(ss, z))), s, s2, Cl.spell_flag(g, s3), pre, xd), LAWireSpell.ws_and_tt(Cl.decls_fit(ds), Cl.binds_fit(ss), fd, fs))
    case Wr.Bad{}:
      Unit{}

def clr.ask.wr_sets(+s: String, +ds: List<&2, Cv.Decl>, +s1: String, pre: {s == Wr.put_nat(4n, Cl.spell_decls(ds, s1)) : String}, fd: {Cl.decls_fit(ds) == True{} : Bool}, d: Wr.Dec<List<&2, Cv.Bind>>, xd: clr.Binds(s1, d)) -> clr.Ask(s, FCL.get_wr.sets(ds, d)):
  match d:
    case Wr.Got{+ss, +s2}:
      (e, f) = xd
      clr.ask.wr_flag(s, ds, ss, s2, clr.step(z => Wr.put_nat(4n, Cl.spell_decls(ds, z)), s, s1, Cl.spell_binds(ss, s2), pre, e), fd, f, FCL.get_flag.go(Wr.get_nat(s2)), clr.flag(s2, Wr.get_nat(s2), {==}))
    case Wr.Bad{}:
      Unit{}

def clr.ask.wr(+s: String, +s0: String, pre: {s == Wr.put_nat(4n, s0) : String}, d: Wr.Dec<List<&2, Cv.Decl>>, xd: clr.Decls(s0, d)) -> clr.Ask(s, FCL.get_wr(d)):
  match d:
    case Wr.Got{+ds, +s1}:
      (e, f) = xd
      clr.ask.wr_sets(s, ds, s1, clr.step(z => Wr.put_nat(4n, z), s, s0, Cl.spell_decls(ds, s1), pre, e), f, FCL.get_binds(Wr.get_nat(s1)), clr.binds(s1))
    case Wr.Bad{}:
      Unit{}

# 5: a settings document
def clr.ask.doc_global(+s: String, +ds: List<&2, Cv.Decl>, +m: List<&2, Cv.Bind>, +s2: String, pre: {s == Wr.put_nat(5n, Cl.spell_decls(ds, Cl.spell_binds(m, s2))) : String}, fd: {Cl.decls_fit(ds) == True{} : Bool}, fm: {Cl.binds_fit(m) == True{} : Bool}, d: Wr.Dec<List<&2, Cv.Bind>>, xd: clr.Binds(s2, d)) -> clr.Ask(s, FCL.get_doc.global(ds, m, d)):
  match d:
    case Wr.Got{+g, +s3}:
      (e, f) = xd
      (clr.step(z => Wr.put_nat(5n, Cl.spell_decls(ds, Cl.spell_binds(m, z))), s, s2, Cl.spell_binds(g, s3), pre, e), LAWireSpell.ws_and_tt(Cl.decls_fit(ds), Bool.and(Cl.binds_fit(m), Cl.binds_fit(g)), fd, LAWireSpell.ws_and_tt(Cl.binds_fit(m), Cl.binds_fit(g), fm, f)))
    case Wr.Bad{}:
      Unit{}

def clr.ask.doc_merged(+s: String, +ds: List<&2, Cv.Decl>, +s1: String, pre: {s == Wr.put_nat(5n, Cl.spell_decls(ds, s1)) : String}, fd: {Cl.decls_fit(ds) == True{} : Bool}, d: Wr.Dec<List<&2, Cv.Bind>>, xd: clr.Binds(s1, d)) -> clr.Ask(s, FCL.get_doc.merged(ds, d)):
  match d:
    case Wr.Got{+m, +s2}:
      (e, f) = xd
      clr.ask.doc_global(s, ds, m, s2, clr.step(z => Wr.put_nat(5n, Cl.spell_decls(ds, z)), s, s1, Cl.spell_binds(m, s2), pre, e), fd, f, FCL.get_binds(Wr.get_nat(s2)), clr.binds(s2))
    case Wr.Bad{}:
      Unit{}

def clr.ask.doc(+s: String, +s0: String, pre: {s == Wr.put_nat(5n, s0) : String}, d: Wr.Dec<List<&2, Cv.Decl>>, xd: clr.Decls(s0, d)) -> clr.Ask(s, FCL.get_doc(d)):
  match d:
    case Wr.Got{+ds, +s1}:
      (e, f) = xd
      clr.ask.doc_merged(s, ds, s1, clr.step(z => Wr.put_nat(5n, z), s, s0, Cl.spell_decls(ds, s1), pre, e), f, FCL.get_binds(Wr.get_nat(s1)), clr.binds(s1))
    case Wr.Bad{}:
      Unit{}

def clr.ask.go(+s: String, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s) == d : Wr.Dec<Nat>}) -> clr.Ask(s, FCL.get_ask.go(d)):
  match d:
    case Wr.Got{+t, +s0}:
      match t:
        case 0n:
          clr.ask.reg(s, s0, Wire.wire_nat_exact(s, 0n, s0, ed), FCL.get_decls(Wr.get_nat(s0)), clr.decls(s0))
        case 1n:
          clr.ask.vals(s, s0, Wire.wire_nat_exact(s, 1n, s0, ed), FCL.get_decls(Wr.get_nat(s0)), clr.decls(s0))
        case 2n:
          clr.ask.tog(s, s0, Wire.wire_nat_exact(s, 2n, s0, ed), FCL.get_decls(Wr.get_nat(s0)), clr.decls(s0))
        case 3n:
          clr.ask.chk(s, s0, Wire.wire_nat_exact(s, 3n, s0, ed), FCL.get_decls(Wr.get_nat(s0)), clr.decls(s0))
        case 4n:
          clr.ask.wr(s, s0, Wire.wire_nat_exact(s, 4n, s0, ed), FCL.get_decls(Wr.get_nat(s0)), clr.decls(s0))
        case 5n:
          clr.ask.doc(s, s0, Wire.wire_nat_exact(s, 5n, s0, ed), FCL.get_decls(Wr.get_nat(s0)), clr.decls(s0))
        case 6n+k:
          Unit{}
    case Wr.Bad{}:
      Unit{}

# a request read is spelled and fits, then its rest
def clr.ask(+s: String) -> clr.Ask(s, FCL.get_ask(s)):
  clr.ask.go(s, Wr.get_nat(s), {==})
