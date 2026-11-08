# eukhe: lemmas of the cvar entry proofs: whatever a decoder of the entry
# reads is the laws' spelling of what it read (laws/cvar/entry.bend
# cvar_spell_*), then its rest, and every number of it fits the wire. Tag
# by tag with the wire's exactness laws (wire_nat_exact, wire_bool_exact,
# wire_nat_decoded_fits): an unknown tag reads Bad; a list's count is its
# length (the item loop, as proof/base/wire_strs.bend).

import Base
import ../../../bend/cvar.bend as Cv
import ../../../bend/ffi_cvar.bend as FCv
import ../../../bend/wire.bend as Wr
import ../../../laws/cvar/entry.bend as CvarEntry
import ../../../laws/base.bend as LawsBase
import ../../../laws/wire.bend as Wire
import ../../wire/wire_nat_exact.bend as PWireNatExact
import ../../wire/wire_nat_decoded_fits.bend as PWireNatDecodedFits
import ../../wire/wire_bool_exact.bend as PWireBoolExact
import ../../wire/base/spell.bend as LAWireSpell

# s spelled up to a field a is s spelled up to its spelling b
def cvr.step(-F: String -> String, -s: String, -a: String, -b: String, pre: {s == F(a) : String}, e: {a == b : String}) -> {s == F(b) : String}:
  Equal.trans(String, s, F(a), F(b), pre, Equal.cong(String, String, F, a, b, e))

# n read with a count of 1 + m is a list of length 1 + m
def cvr.len(-A: Data, -xs: List<&2, A>, -m: Nat, -G: Nat -> Type, g: G(1n+m), e: {List.length(&2, A, xs) == 1n+m : Nat}) -> G(List.length(&2, A, xs)):
  %Equal.sym(Nat, List.length(&2, A, xs), 1n+m, e) : G(_)
  g

# Values
# ------

def cvr.Val(s: String, d: Wr.Dec<Cv.Val>) -> Type:
  match d:
    case Wr.Got{v, r}:
      {s == CvarEntry.cvar_spell_val(v, r) : String} & {CvarEntry.cvar_val_fits(v) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def cvr.val.nat(+s: String, +s0: String, pre: {s == Wr.put_nat(0n, s0) : String}, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s0) == d : Wr.Dec<Nat>}) -> cvr.Val(s, FCv.get_val.nat(d)):
  match d:
    case Wr.Got{+n, +s1}:
      +ee = ed
      (cvr.step(z => Wr.put_nat(0n, z), s, s0, Wr.put_nat(n, s1), pre, Wire.wire_nat_exact(s0, n, s1, ee)), Wire.wire_nat_decoded_fits(s0, n, s1, ee))
    case Wr.Bad{}:
      Unit{}

def cvr.val.bool(+s: String, +s0: String, pre: {s == Wr.put_nat(1n, s0) : String}, d: Wr.Dec<Bool>, ed: {Wr.get_bool(s0) == d : Wr.Dec<Bool>}) -> cvr.Val(s, FCv.get_val.bool(d)):
  match d:
    case Wr.Got{+b, +s1}:
      (cvr.step(z => Wr.put_nat(1n, z), s, s0, Wr.put_bool(b, s1), pre, Wire.wire_bool_exact(s0, b, s1, ed)), {==})
    case Wr.Bad{}:
      Unit{}

def cvr.val.go(+s: String, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s) == d : Wr.Dec<Nat>}) -> cvr.Val(s, FCv.get_val.go(d)):
  match d:
    case Wr.Got{+t, +s0}:
      match t:
        case 0n:
          cvr.val.nat(s, s0, Wire.wire_nat_exact(s, 0n, s0, ed), Wr.get_nat(s0), {==})
        case 1n:
          cvr.val.bool(s, s0, Wire.wire_nat_exact(s, 1n, s0, ed), Wr.get_bool(s0), {==})
        case 2n+k:
          Unit{}
    case Wr.Bad{}:
      Unit{}

# a value read is spelled and fits
def cvr.val(+s: String) -> cvr.Val(s, FCv.get_val(s)):
  cvr.val.go(s, Wr.get_nat(s), {==})

# Commands
# --------

def cvr.Cmd(s: String, d: Wr.Dec<Cv.Cmd>) -> Type:
  match d:
    case Wr.Got{c, r}:
      {s == CvarEntry.cvar_spell_cmd(c, r) : String} & {CvarEntry.cvar_cmd_fits(c) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def cvr.cmd.setv(+s: String, +i: Nat, +s1: String, pre: {s == Wr.put_nat(0n, Wr.put_nat(i, s1)) : String}, fi: {LawsBase.wire_fits(i) == True{} : Bool}, d: Wr.Dec<Cv.Val>, xd: cvr.Val(s1, d)) -> cvr.Cmd(s, FCv.get_cmd.set.v(i, d)):
  match d:
    case Wr.Got{+v, +s2}:
      (e, f) = xd
      (cvr.step(z => Wr.put_nat(0n, Wr.put_nat(i, z)), s, s1, CvarEntry.cvar_spell_val(v, s2), pre, e), LAWireSpell.ws_and_tt(LawsBase.wire_fits(i), CvarEntry.cvar_val_fits(v), fi, f))
    case Wr.Bad{}:
      Unit{}

def cvr.cmd.set(+s: String, +s0: String, pre: {s == Wr.put_nat(0n, s0) : String}, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s0) == d : Wr.Dec<Nat>}) -> cvr.Cmd(s, FCv.get_cmd.set(d)):
  match d:
    case Wr.Got{+i, +s1}:
      +ee = ed
      cvr.cmd.setv(s, i, s1, cvr.step(z => Wr.put_nat(0n, z), s, s0, Wr.put_nat(i, s1), pre, Wire.wire_nat_exact(s0, i, s1, ee)), Wire.wire_nat_decoded_fits(s0, i, s1, ee), FCv.get_val(s1), cvr.val(s1))
    case Wr.Bad{}:
      Unit{}

def cvr.cmd.toggle(+s: String, +s0: String, pre: {s == Wr.put_nat(1n, s0) : String}, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s0) == d : Wr.Dec<Nat>}) -> cvr.Cmd(s, FCv.get_cmd.toggle(d)):
  match d:
    case Wr.Got{+i, +s1}:
      +ee = ed
      (cvr.step(z => Wr.put_nat(1n, z), s, s0, Wr.put_nat(i, s1), pre, Wire.wire_nat_exact(s0, i, s1, ee)), Wire.wire_nat_decoded_fits(s0, i, s1, ee))
    case Wr.Bad{}:
      Unit{}

def cvr.cmd.run(+s: String, +s0: String, pre: {s == Wr.put_nat(2n, s0) : String}, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s0) == d : Wr.Dec<Nat>}) -> cvr.Cmd(s, FCv.get_cmd.run(d)):
  match d:
    case Wr.Got{+n, +s1}:
      +ee = ed
      (cvr.step(z => Wr.put_nat(2n, z), s, s0, Wr.put_nat(n, s1), pre, Wire.wire_nat_exact(s0, n, s1, ee)), Wire.wire_nat_decoded_fits(s0, n, s1, ee))
    case Wr.Bad{}:
      Unit{}

def cvr.cmd.gone(+s: String, +s0: String, pre: {s == Wr.put_nat(3n, s0) : String}, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s0) == d : Wr.Dec<Nat>}) -> cvr.Cmd(s, FCv.get_cmd.gone(d)):
  match d:
    case Wr.Got{+n, +s1}:
      +ee = ed
      (cvr.step(z => Wr.put_nat(3n, z), s, s0, Wr.put_nat(n, s1), pre, Wire.wire_nat_exact(s0, n, s1, ee)), Wire.wire_nat_decoded_fits(s0, n, s1, ee))
    case Wr.Bad{}:
      Unit{}

def cvr.cmd.go(+s: String, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s) == d : Wr.Dec<Nat>}) -> cvr.Cmd(s, FCv.get_cmd.go(d)):
  match d:
    case Wr.Got{+t, +s0}:
      match t:
        case 0n:
          cvr.cmd.set(s, s0, Wire.wire_nat_exact(s, 0n, s0, ed), Wr.get_nat(s0), {==})
        case 1n:
          cvr.cmd.toggle(s, s0, Wire.wire_nat_exact(s, 1n, s0, ed), Wr.get_nat(s0), {==})
        case 2n:
          cvr.cmd.run(s, s0, Wire.wire_nat_exact(s, 2n, s0, ed), Wr.get_nat(s0), {==})
        case 3n:
          cvr.cmd.gone(s, s0, Wire.wire_nat_exact(s, 3n, s0, ed), Wr.get_nat(s0), {==})
        case 4n+k:
          Unit{}
    case Wr.Bad{}:
      Unit{}

# a command read is spelled and fits
def cvr.cmd(+s: String) -> cvr.Cmd(s, FCv.get_cmd(s)):
  cvr.cmd.go(s, Wr.get_nat(s), {==})

# Command lists
# -------------

# what the item loop's answer says about its input s (m + 1 items)
def cvr.cs.PL(s: String, m: Nat, d: Wr.Dec<List<&2, Cv.Cmd>>) -> Type:
  match d:
    case Wr.Got{+xs, r}:
      {s == CvarEntry.cvar_spell_cmds.items(xs, r) : String} & ({List.length(&2, Cv.Cmd, xs) == 1n+m : Nat} & {CvarEntry.cvar_cmds_all(xs) == True{} : Bool})
    case Wr.Bad{}:
      Unit

def cvr.cs.step(-s: String, +x: Cv.Cmd, +s3: String, -k: Nat, ex: {s == CvarEntry.cvar_spell_cmd(x, s3) : String}, fx: {CvarEntry.cvar_cmd_fits(x) == True{} : Bool}, d: Wr.Dec<List<&2, Cv.Cmd>>, ih: cvr.cs.PL(s3, k, d)) -> cvr.cs.PL(s, 1n+k, Wr.get_list.cons(Cv.Cmd, x, d)):
  match d:
    case Wr.Got{+ys, +r}:
      (e1, e23) = ih
      (e2, e3) = e23
      (Equal.trans(String, s, CvarEntry.cvar_spell_cmd(x, s3), CvarEntry.cvar_spell_cmd(x, CvarEntry.cvar_spell_cmds.items(ys, r)), ex, Equal.cong(String, String, z => CvarEntry.cvar_spell_cmd(x, z), s3, CvarEntry.cvar_spell_cmds.items(ys, r), e1)), (Equal.cong(Nat, Nat, k2 => 1n+k2, List.length(&2, Cv.Cmd, ys), 1n+k, e2), LAWireSpell.ws_and_tt(CvarEntry.cvar_cmd_fits(x), CvarEntry.cvar_cmds_all(ys), fx, e3)))
    case Wr.Bad{}:
      Unit{}

def cvr.cs.loop(m: Nat, cur: Wr.Dec<Cv.Cmd>, +s: String, pc: cvr.Cmd(s, cur)) -> cvr.cs.PL(s, m, Wr.get_list.go(~Cv.Cmd, ~FCv.get_cmd, m, cur)):
  match m cur:
    case 0n Wr.Got{+x, +s3}:
      (e, f) = pc
      (e, ({==}, LAWireSpell.ws_and_tt(CvarEntry.cvar_cmd_fits(x), True{}, f, {==})))
    case 0n Wr.Bad{}:
      Unit{}
    case 1n++k Wr.Got{+x, +s3}:
      (e, f) = pc
      cvr.cs.step(s, x, s3, k, e, f, Wr.get_list.go(~Cv.Cmd, ~FCv.get_cmd, k, FCv.get_cmd(s3)), cvr.cs.loop(k, FCv.get_cmd(s3), s3, cvr.cmd(s3)))
    case 1n++k Wr.Bad{}:
      Unit{}

def cvr.Cmds(s: String, d: Wr.Dec<List<&2, Cv.Cmd>>) -> Type:
  match d:
    case Wr.Got{+xs, r}:
      {s == CvarEntry.cvar_spell_cmds(xs, r) : String} & {CvarEntry.cvar_cmds_fit(xs) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def cvr.cs.conv(-s: String, -s2: String, -m: Nat, en: {s == Wr.put_nat(1n+m, s2) : String}, fn: {LawsBase.wire_fits(1n+m) == True{} : Bool}, d: Wr.Dec<List<&2, Cv.Cmd>>, pl: cvr.cs.PL(s2, m, d)) -> cvr.Cmds(s, d):
  match d:
    case Wr.Got{+xs, +r}:
      (e1, e23) = pl
      (+e2, e3) = e23
      +es = cvr.step(z => Wr.put_nat(1n+m, z), s, s2, CvarEntry.cvar_spell_cmds.items(xs, r), en, e1)
      (cvr.len(Cv.Cmd, xs, m, n => {s == Wr.put_nat(n, CvarEntry.cvar_spell_cmds.items(xs, r)) : String}, es, e2), LAWireSpell.ws_and_tt(LawsBase.wire_fits(List.length(&2, Cv.Cmd, xs)), CvarEntry.cvar_cmds_all(xs), cvr.len(Cv.Cmd, xs, m, n => {LawsBase.wire_fits(n) == True{} : Bool}, fn, e2), e3))
    case Wr.Bad{}:
      Unit{}

def cvr.cs.nat(-s: String, n: Nat, +s2: String, en: {s == Wr.put_nat(n, s2) : String}, fn: {LawsBase.wire_fits(n) == True{} : Bool}) -> cvr.Cmds(s, Wr.get_list.start(~Cv.Cmd, ~FCv.get_cmd, Wr.Got{n, s2})):
  match n:
    case 0n:
      (en, LAWireSpell.ws_and_tt(LawsBase.wire_fits(0n), True{}, fn, {==}))
    case 1n++m:
      cvr.cs.conv(s, s2, m, en, fn, Wr.get_list.go(~Cv.Cmd, ~FCv.get_cmd, m, FCv.get_cmd(s2)), cvr.cs.loop(m, FCv.get_cmd(s2), s2, cvr.cmd(s2)))

def cvr.cs.top(+s: String, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s) == d : Wr.Dec<Nat>}) -> cvr.Cmds(s, Wr.get_list.start(~Cv.Cmd, ~FCv.get_cmd, d)):
  match d:
    case Wr.Got{+n, +s2}:
      +e = ed
      cvr.cs.nat(s, n, s2, Wire.wire_nat_exact(s, n, s2, e), Wire.wire_nat_decoded_fits(s, n, s2, e))
    case Wr.Bad{}:
      Unit{}

# a command list read is spelled and fits
def cvr.cmds(+s: String) -> cvr.Cmds(s, FCv.get_cmds(s)):
  cvr.cs.top(s, Wr.get_nat(s), {==})

# Aliases and binds
# -----------------

def cvr.Alias(s: String, d: Wr.Dec<Cv.Alias>) -> Type:
  match d:
    case Wr.Got{a, r}:
      {s == CvarEntry.cvar_spell_alias(a, r) : String} & {CvarEntry.cvar_alias_fits(a) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def cvr.alias.body(+s: String, +n: Nat, +s1: String, pre: {s == Wr.put_nat(n, s1) : String}, fn: {LawsBase.wire_fits(n) == True{} : Bool}, d: Wr.Dec<List<&2, Cv.Cmd>>, xd: cvr.Cmds(s1, d)) -> cvr.Alias(s, FCv.get_alias.body(n, d)):
  match d:
    case Wr.Got{+b, +s2}:
      (e, f) = xd
      (cvr.step(z => Wr.put_nat(n, z), s, s1, CvarEntry.cvar_spell_cmds(b, s2), pre, e), LAWireSpell.ws_and_tt(LawsBase.wire_fits(n), CvarEntry.cvar_cmds_fit(b), fn, f))
    case Wr.Bad{}:
      Unit{}

def cvr.alias.name(+s: String, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s) == d : Wr.Dec<Nat>}) -> cvr.Alias(s, FCv.get_alias.name(d)):
  match d:
    case Wr.Got{+n, +s1}:
      +e = ed
      cvr.alias.body(s, n, s1, Wire.wire_nat_exact(s, n, s1, e), Wire.wire_nat_decoded_fits(s, n, s1, e), FCv.get_cmds(s1), cvr.cmds(s1))
    case Wr.Bad{}:
      Unit{}

# an alias read is spelled and fits
def cvr.alias(+s: String) -> cvr.Alias(s, FCv.get_alias(s)):
  cvr.alias.name(s, Wr.get_nat(s), {==})

def cvr.Bind(s: String, d: Wr.Dec<Cv.KeyBind>) -> Type:
  match d:
    case Wr.Got{k, r}:
      {s == CvarEntry.cvar_spell_bind(k, r) : String} & {CvarEntry.cvar_bind_fits(k) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def cvr.bind.cmds(+s: String, +n: Nat, +s1: String, pre: {s == Wr.put_nat(n, s1) : String}, fn: {LawsBase.wire_fits(n) == True{} : Bool}, d: Wr.Dec<List<&2, Cv.Cmd>>, xd: cvr.Cmds(s1, d)) -> cvr.Bind(s, FCv.get_bind.cmds(n, d)):
  match d:
    case Wr.Got{+c, +s2}:
      (e, f) = xd
      (cvr.step(z => Wr.put_nat(n, z), s, s1, CvarEntry.cvar_spell_cmds(c, s2), pre, e), LAWireSpell.ws_and_tt(LawsBase.wire_fits(n), CvarEntry.cvar_cmds_fit(c), fn, f))
    case Wr.Bad{}:
      Unit{}

def cvr.bind.key(+s: String, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s) == d : Wr.Dec<Nat>}) -> cvr.Bind(s, FCv.get_bind.key(d)):
  match d:
    case Wr.Got{+n, +s1}:
      +e = ed
      cvr.bind.cmds(s, n, s1, Wire.wire_nat_exact(s, n, s1, e), Wire.wire_nat_decoded_fits(s, n, s1, e), FCv.get_cmds(s1), cvr.cmds(s1))
    case Wr.Bad{}:
      Unit{}

# a bind read is spelled and fits
def cvr.bind(+s: String) -> cvr.Bind(s, FCv.get_bind(s)):
  cvr.bind.key(s, Wr.get_nat(s), {==})

# Alias lists
# -----------

def cvr.as.PL(s: String, m: Nat, d: Wr.Dec<List<&2, Cv.Alias>>) -> Type:
  match d:
    case Wr.Got{+xs, r}:
      {s == CvarEntry.cvar_spell_aliases.items(xs, r) : String} & ({List.length(&2, Cv.Alias, xs) == 1n+m : Nat} & {CvarEntry.cvar_aliases_all(xs) == True{} : Bool})
    case Wr.Bad{}:
      Unit

def cvr.as.step(-s: String, +x: Cv.Alias, +s3: String, -k: Nat, ex: {s == CvarEntry.cvar_spell_alias(x, s3) : String}, fx: {CvarEntry.cvar_alias_fits(x) == True{} : Bool}, d: Wr.Dec<List<&2, Cv.Alias>>, ih: cvr.as.PL(s3, k, d)) -> cvr.as.PL(s, 1n+k, Wr.get_list.cons(Cv.Alias, x, d)):
  match d:
    case Wr.Got{+ys, +r}:
      (e1, e23) = ih
      (e2, e3) = e23
      (Equal.trans(String, s, CvarEntry.cvar_spell_alias(x, s3), CvarEntry.cvar_spell_alias(x, CvarEntry.cvar_spell_aliases.items(ys, r)), ex, Equal.cong(String, String, z => CvarEntry.cvar_spell_alias(x, z), s3, CvarEntry.cvar_spell_aliases.items(ys, r), e1)), (Equal.cong(Nat, Nat, k2 => 1n+k2, List.length(&2, Cv.Alias, ys), 1n+k, e2), LAWireSpell.ws_and_tt(CvarEntry.cvar_alias_fits(x), CvarEntry.cvar_aliases_all(ys), fx, e3)))
    case Wr.Bad{}:
      Unit{}

def cvr.as.loop(m: Nat, cur: Wr.Dec<Cv.Alias>, +s: String, pc: cvr.Alias(s, cur)) -> cvr.as.PL(s, m, Wr.get_list.go(~Cv.Alias, ~FCv.get_alias, m, cur)):
  match m cur:
    case 0n Wr.Got{+x, +s3}:
      (e, f) = pc
      (e, ({==}, LAWireSpell.ws_and_tt(CvarEntry.cvar_alias_fits(x), True{}, f, {==})))
    case 0n Wr.Bad{}:
      Unit{}
    case 1n++k Wr.Got{+x, +s3}:
      (e, f) = pc
      cvr.as.step(s, x, s3, k, e, f, Wr.get_list.go(~Cv.Alias, ~FCv.get_alias, k, FCv.get_alias(s3)), cvr.as.loop(k, FCv.get_alias(s3), s3, cvr.alias(s3)))
    case 1n++k Wr.Bad{}:
      Unit{}

def cvr.Aliases(s: String, d: Wr.Dec<List<&2, Cv.Alias>>) -> Type:
  match d:
    case Wr.Got{+xs, r}:
      {s == CvarEntry.cvar_spell_aliases(xs, r) : String} & {CvarEntry.cvar_aliases_fit(xs) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def cvr.as.conv(-s: String, -s2: String, -m: Nat, en: {s == Wr.put_nat(1n+m, s2) : String}, fn: {LawsBase.wire_fits(1n+m) == True{} : Bool}, d: Wr.Dec<List<&2, Cv.Alias>>, pl: cvr.as.PL(s2, m, d)) -> cvr.Aliases(s, d):
  match d:
    case Wr.Got{+xs, +r}:
      (e1, e23) = pl
      (+e2, e3) = e23
      +es = cvr.step(z => Wr.put_nat(1n+m, z), s, s2, CvarEntry.cvar_spell_aliases.items(xs, r), en, e1)
      (cvr.len(Cv.Alias, xs, m, n => {s == Wr.put_nat(n, CvarEntry.cvar_spell_aliases.items(xs, r)) : String}, es, e2), LAWireSpell.ws_and_tt(LawsBase.wire_fits(List.length(&2, Cv.Alias, xs)), CvarEntry.cvar_aliases_all(xs), cvr.len(Cv.Alias, xs, m, n => {LawsBase.wire_fits(n) == True{} : Bool}, fn, e2), e3))
    case Wr.Bad{}:
      Unit{}

def cvr.as.nat(-s: String, n: Nat, +s2: String, en: {s == Wr.put_nat(n, s2) : String}, fn: {LawsBase.wire_fits(n) == True{} : Bool}) -> cvr.Aliases(s, Wr.get_list.start(~Cv.Alias, ~FCv.get_alias, Wr.Got{n, s2})):
  match n:
    case 0n:
      (en, LAWireSpell.ws_and_tt(LawsBase.wire_fits(0n), True{}, fn, {==}))
    case 1n++m:
      cvr.as.conv(s, s2, m, en, fn, Wr.get_list.go(~Cv.Alias, ~FCv.get_alias, m, FCv.get_alias(s2)), cvr.as.loop(m, FCv.get_alias(s2), s2, cvr.alias(s2)))

def cvr.as.top(+s: String, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s) == d : Wr.Dec<Nat>}) -> cvr.Aliases(s, Wr.get_list.start(~Cv.Alias, ~FCv.get_alias, d)):
  match d:
    case Wr.Got{+n, +s2}:
      +e = ed
      cvr.as.nat(s, n, s2, Wire.wire_nat_exact(s, n, s2, e), Wire.wire_nat_decoded_fits(s, n, s2, e))
    case Wr.Bad{}:
      Unit{}

# an alias table read is spelled and fits
def cvr.aliases(+s: String) -> cvr.Aliases(s, Wr.get_list(~Cv.Alias, ~FCv.get_alias, s)):
  cvr.as.top(s, Wr.get_nat(s), {==})

# Bind lists
# ----------

def cvr.bs.PL(s: String, m: Nat, d: Wr.Dec<List<&2, Cv.KeyBind>>) -> Type:
  match d:
    case Wr.Got{+xs, r}:
      {s == CvarEntry.cvar_spell_binds.items(xs, r) : String} & ({List.length(&2, Cv.KeyBind, xs) == 1n+m : Nat} & {CvarEntry.cvar_binds_all(xs) == True{} : Bool})
    case Wr.Bad{}:
      Unit

def cvr.bs.step(-s: String, +x: Cv.KeyBind, +s3: String, -k: Nat, ex: {s == CvarEntry.cvar_spell_bind(x, s3) : String}, fx: {CvarEntry.cvar_bind_fits(x) == True{} : Bool}, d: Wr.Dec<List<&2, Cv.KeyBind>>, ih: cvr.bs.PL(s3, k, d)) -> cvr.bs.PL(s, 1n+k, Wr.get_list.cons(Cv.KeyBind, x, d)):
  match d:
    case Wr.Got{+ys, +r}:
      (e1, e23) = ih
      (e2, e3) = e23
      (Equal.trans(String, s, CvarEntry.cvar_spell_bind(x, s3), CvarEntry.cvar_spell_bind(x, CvarEntry.cvar_spell_binds.items(ys, r)), ex, Equal.cong(String, String, z => CvarEntry.cvar_spell_bind(x, z), s3, CvarEntry.cvar_spell_binds.items(ys, r), e1)), (Equal.cong(Nat, Nat, k2 => 1n+k2, List.length(&2, Cv.KeyBind, ys), 1n+k, e2), LAWireSpell.ws_and_tt(CvarEntry.cvar_bind_fits(x), CvarEntry.cvar_binds_all(ys), fx, e3)))
    case Wr.Bad{}:
      Unit{}

def cvr.bs.loop(m: Nat, cur: Wr.Dec<Cv.KeyBind>, +s: String, pc: cvr.Bind(s, cur)) -> cvr.bs.PL(s, m, Wr.get_list.go(~Cv.KeyBind, ~FCv.get_bind, m, cur)):
  match m cur:
    case 0n Wr.Got{+x, +s3}:
      (e, f) = pc
      (e, ({==}, LAWireSpell.ws_and_tt(CvarEntry.cvar_bind_fits(x), True{}, f, {==})))
    case 0n Wr.Bad{}:
      Unit{}
    case 1n++k Wr.Got{+x, +s3}:
      (e, f) = pc
      cvr.bs.step(s, x, s3, k, e, f, Wr.get_list.go(~Cv.KeyBind, ~FCv.get_bind, k, FCv.get_bind(s3)), cvr.bs.loop(k, FCv.get_bind(s3), s3, cvr.bind(s3)))
    case 1n++k Wr.Bad{}:
      Unit{}

def cvr.Binds(s: String, d: Wr.Dec<List<&2, Cv.KeyBind>>) -> Type:
  match d:
    case Wr.Got{+xs, r}:
      {s == CvarEntry.cvar_spell_binds(xs, r) : String} & {CvarEntry.cvar_binds_fit(xs) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def cvr.bs.conv(-s: String, -s2: String, -m: Nat, en: {s == Wr.put_nat(1n+m, s2) : String}, fn: {LawsBase.wire_fits(1n+m) == True{} : Bool}, d: Wr.Dec<List<&2, Cv.KeyBind>>, pl: cvr.bs.PL(s2, m, d)) -> cvr.Binds(s, d):
  match d:
    case Wr.Got{+xs, +r}:
      (e1, e23) = pl
      (+e2, e3) = e23
      +es = cvr.step(z => Wr.put_nat(1n+m, z), s, s2, CvarEntry.cvar_spell_binds.items(xs, r), en, e1)
      (cvr.len(Cv.KeyBind, xs, m, n => {s == Wr.put_nat(n, CvarEntry.cvar_spell_binds.items(xs, r)) : String}, es, e2), LAWireSpell.ws_and_tt(LawsBase.wire_fits(List.length(&2, Cv.KeyBind, xs)), CvarEntry.cvar_binds_all(xs), cvr.len(Cv.KeyBind, xs, m, n => {LawsBase.wire_fits(n) == True{} : Bool}, fn, e2), e3))
    case Wr.Bad{}:
      Unit{}

def cvr.bs.nat(-s: String, n: Nat, +s2: String, en: {s == Wr.put_nat(n, s2) : String}, fn: {LawsBase.wire_fits(n) == True{} : Bool}) -> cvr.Binds(s, Wr.get_list.start(~Cv.KeyBind, ~FCv.get_bind, Wr.Got{n, s2})):
  match n:
    case 0n:
      (en, LAWireSpell.ws_and_tt(LawsBase.wire_fits(0n), True{}, fn, {==}))
    case 1n++m:
      cvr.bs.conv(s, s2, m, en, fn, Wr.get_list.go(~Cv.KeyBind, ~FCv.get_bind, m, FCv.get_bind(s2)), cvr.bs.loop(m, FCv.get_bind(s2), s2, cvr.bind(s2)))

def cvr.bs.top(+s: String, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s) == d : Wr.Dec<Nat>}) -> cvr.Binds(s, Wr.get_list.start(~Cv.KeyBind, ~FCv.get_bind, d)):
  match d:
    case Wr.Got{+n, +s2}:
      +e = ed
      cvr.bs.nat(s, n, s2, Wire.wire_nat_exact(s, n, s2, e), Wire.wire_nat_decoded_fits(s, n, s2, e))
    case Wr.Bad{}:
      Unit{}

# a bind table read is spelled and fits
def cvr.binds(+s: String) -> cvr.Binds(s, Wr.get_list(~Cv.KeyBind, ~FCv.get_bind, s)):
  cvr.bs.top(s, Wr.get_nat(s), {==})

# The expand request and the press table
# --------------------------------------

def cvr.Xq(s: String, q: FCv.Xreq, r: String) -> Type:
  match q:
    case FCv.Xreq{+as, +cs}:
      {s == CvarEntry.cvar_spell_aliases(as, CvarEntry.cvar_spell_cmds(cs, r)) : String} & {Bool.and(CvarEntry.cvar_aliases_fit(as), CvarEntry.cvar_cmds_fit(cs)) == True{} : Bool}

def cvr.Xreq(s: String, d: Wr.Dec<FCv.Xreq>) -> Type:
  match d:
    case Wr.Got{q, r}:
      cvr.Xq(s, q, r)
    case Wr.Bad{}:
      Unit

def cvr.xreq.cmds(+s: String, +as: List<&2, Cv.Alias>, +s1: String, pre: {s == CvarEntry.cvar_spell_aliases(as, s1) : String}, fa: {CvarEntry.cvar_aliases_fit(as) == True{} : Bool}, d: Wr.Dec<List<&2, Cv.Cmd>>, xd: cvr.Cmds(s1, d)) -> cvr.Xreq(s, FCv.get_xreq.cmds(as, d)):
  match d:
    case Wr.Got{+cs, +s2}:
      (e, f) = xd
      (cvr.step(z => CvarEntry.cvar_spell_aliases(as, z), s, s1, CvarEntry.cvar_spell_cmds(cs, s2), pre, e), LAWireSpell.ws_and_tt(CvarEntry.cvar_aliases_fit(as), CvarEntry.cvar_cmds_fit(cs), fa, f))
    case Wr.Bad{}:
      Unit{}

def cvr.xreq.aliases(+s: String, d: Wr.Dec<List<&2, Cv.Alias>>, xd: cvr.Aliases(s, d)) -> cvr.Xreq(s, FCv.get_xreq.aliases(d)):
  match d:
    case Wr.Got{+as, +s1}:
      (e, f) = xd
      cvr.xreq.cmds(s, as, s1, e, f, FCv.get_cmds(s1), cvr.cmds(s1))
    case Wr.Bad{}:
      Unit{}

# an expand request read is spelled and fits
def cvr.xreq(+s: String) -> cvr.Xreq(s, FCv.get_xreq(s)):
  cvr.xreq.aliases(s, Wr.get_list(~Cv.Alias, ~FCv.get_alias, s), cvr.aliases(s))

# a table read is spelled and fits; the decoder never reads a refused state
def cvr.Tb(s: String, t: FCv.St, r: String) -> Type:
  match t:
    case FCv.Table{+bs, +as}:
      {s == CvarEntry.cvar_spell_binds(bs, CvarEntry.cvar_spell_aliases(as, r)) : String} & {Bool.and(CvarEntry.cvar_binds_fit(bs), CvarEntry.cvar_aliases_fit(as)) == True{} : Bool}
    case FCv.Refused{}:
      Empty

def cvr.Table(s: String, d: Wr.Dec<FCv.St>) -> Type:
  match d:
    case Wr.Got{t, r}:
      cvr.Tb(s, t, r)
    case Wr.Bad{}:
      Unit

def cvr.table.aliases(+s: String, +bs: List<&2, Cv.KeyBind>, +s1: String, pre: {s == CvarEntry.cvar_spell_binds(bs, s1) : String}, fb: {CvarEntry.cvar_binds_fit(bs) == True{} : Bool}, d: Wr.Dec<List<&2, Cv.Alias>>, xd: cvr.Aliases(s1, d)) -> cvr.Table(s, FCv.get_table.aliases(bs, d)):
  match d:
    case Wr.Got{+as, +s2}:
      (e, f) = xd
      (cvr.step(z => CvarEntry.cvar_spell_binds(bs, z), s, s1, CvarEntry.cvar_spell_aliases(as, s2), pre, e), LAWireSpell.ws_and_tt(CvarEntry.cvar_binds_fit(bs), CvarEntry.cvar_aliases_fit(as), fb, f))
    case Wr.Bad{}:
      Unit{}

def cvr.table.binds(+s: String, d: Wr.Dec<List<&2, Cv.KeyBind>>, xd: cvr.Binds(s, d)) -> cvr.Table(s, FCv.get_table.binds(d)):
  match d:
    case Wr.Got{+bs, +s1}:
      (e, f) = xd
      cvr.table.aliases(s, bs, s1, e, f, Wr.get_list(~Cv.Alias, ~FCv.get_alias, s1), cvr.aliases(s1))
    case Wr.Bad{}:
      Unit{}

# a press table read is spelled and fits
def cvr.table(+s: String) -> cvr.Table(s, FCv.get_table(s)):
  cvr.table.binds(s, Wr.get_list(~Cv.KeyBind, ~FCv.get_bind, s), cvr.binds(s))
