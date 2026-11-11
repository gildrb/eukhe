# autoresearch (spec): what a METRIC line of a benchmark's output is: the
# text its parts spell, which parts are well formed, and how many
# significant digits its value has. Grammar (oh-my-pi's regex
# ^METRIC\s+([\w.µ-]+)=(\S+)\s*$, its value narrowed to plain decimals):
#
#   "METRIC" sp name "=" ["-"] int ["." frac] trail
#
# sp: one or more of space (32), tab (9); name: one or more of A-Z a-z
# 0-9 _ . -; int, frac: one or more digits each; trail: zero or more of
# space, tab, CR (13). The value is ±num(int frac) / 10^|frac|
# (spec/autoresearch/decimal.bend). A spec: the shipped code never calls
# it.

import Base
import ../../bend/autoresearch/dec.bend as D
import ../../bend/autoresearch/line.bend as L
import ./decimal.bend as Dec

# Chars
# -----

def code(c: Char) -> Nat:
  match c:
    case Chr{x}:
      U32.to_nat(x)

# the char of code n
def char(n: Nat) -> Char:
  Chr{U32.from_nat(n)}

def is_blank(+n: Nat) -> Bool:
  Bool.or(Nat.is_eq(n, 32n), Nat.is_eq(n, 9n))

def is_trail(+n: Nat) -> Bool:
  Bool.or(is_blank(n), Nat.is_eq(n, 13n))

def is_name(+n: Nat) -> Bool:
  Bool.or(Bool.and(Nat.is_le(65n, n), Nat.is_le(n, 90n)), Bool.or(Bool.and(Nat.is_le(97n, n), Nat.is_le(n, 122n)), Bool.or(Bool.and(Nat.is_le(48n, n), Nat.is_le(n, 57n)), Bool.or(Nat.is_eq(n, 95n), Bool.or(Nat.is_eq(n, 46n), Nat.is_eq(n, 45n))))))

# every char of s has a code k likes (one of the three classes)
def all_blank(s: String) -> Bool:
  match s:
    case SNil{}:
      True{}
    case SCon{c, t}:
      Bool.and(is_blank(code(c)), all_blank(t))

def all_trail(s: String) -> Bool:
  match s:
    case SNil{}:
      True{}
    case SCon{c, t}:
      Bool.and(is_trail(code(c)), all_trail(t))

def all_name(s: String) -> Bool:
  match s:
    case SNil{}:
      True{}
    case SCon{c, t}:
      Bool.and(is_name(code(c)), all_name(t))

def nonempty(s: String) -> Bool:
  match s:
    case SNil{}:
      False{}
    case SCon{c, t}:
      True{}

def nonempty_ds(ds: List<&2, Nat>) -> Bool:
  match ds:
    case Nil{}:
      False{}
    case d <> t:
      True{}

# Spelling
# --------

# the digits' chars, then rest
def spell_ds(ds: List<&2, Nat>, rest: String) -> String:
  match ds:
    case Nil{}:
      rest
    case d <> t:
      SCon{char(Nat.add(48n, d)), spell_ds(t, rest)}

def spell_frac(f: Maybe<&2, List<&2, Nat>>, rest: String) -> String:
  match f:
    case None{}:
      rest
    case Some{fs}:
      SCon{'.', spell_ds(fs, rest)}

def spell_sign(neg: Bool, rest: String) -> String:
  match neg:
    case True{}:
      SCon{'-', rest}
    case False{}:
      rest

# the line the parts spell
def line(p: L.Parts) -> String:
  match p:
    case L.Parts{sp, name, neg, int, frac, trail}:
      String.append("METRIC", String.append(sp, String.append(name, SCon{'=', spell_sign(neg, spell_ds(int, spell_frac(frac, trail)))})))

def frac_ok(f: Maybe<&2, List<&2, Nat>>) -> Bool:
  match f:
    case None{}:
      True{}
    case Some{+fs}:
      Bool.and(nonempty_ds(fs), Dec.digits_ok(fs))

# the parts follow the grammar
def ok(p: L.Parts) -> Bool:
  match p:
    case L.Parts{+sp, +name, neg, +int, frac, trail}:
      Bool.and(Bool.and(nonempty(sp), all_blank(sp)), Bool.and(Bool.and(nonempty(name), all_name(name)), Bool.and(Bool.and(nonempty_ds(int), Dec.digits_ok(int)), Bool.and(frac_ok(frac), all_trail(trail)))))

# The value
# ---------

def frac_of(f: Maybe<&2, List<&2, Nat>>) -> List<&2, Nat>:
  match f:
    case None{}:
      Nil{}
    case Some{fs}:
      fs

def dlen(ds: List<&2, Nat>) -> Nat:
  match ds:
    case Nil{}:
      0n
    case d <> t:
      1n+dlen(t)

# the value as written: ±num(int frac) / 10^|frac| (not canonical)
def raw(p: L.Parts) -> D.Dec:
  match p:
    case L.Parts{sp, name, neg, int, frac, trail}:
      +fs = frac_of(frac)
      D.Dec{neg, List.append(&2, Nat, int, fs), dlen(fs)}

# ds without its leading zeros
def trim_lead(ds: List<&2, Nat>) -> List<&2, Nat>:
  match ds:
    case Nil{}:
      Nil{}
    case d <> t:
      match d:
        case 0n:
          trim_lead(t)
        case 1n+e:
          (1n+e) <> t

def rev(ds: List<&2, Nat>, acc: List<&2, Nat>) -> List<&2, Nat>:
  match ds:
    case Nil{}:
      acc
    case d <> t:
      rev(t, d <> acc)

# ds without its trailing zeros
def trim_trail(ds: List<&2, Nat>) -> List<&2, Nat>:
  rev(trim_lead(rev(ds, Nil{})), Nil{})

# the value's significant digits: from the first non-zero digit to the
# last digit that is not a trailing zero of the fraction
def sig(p: L.Parts) -> Nat:
  match p:
    case L.Parts{sp, name, neg, int, frac, trail}:
      dlen(trim_lead(List.append(&2, Nat, int, trim_trail(frac_of(frac)))))

# what the line means: none past 15 significant digits; else the name
# and a canonical decimal worth the value as written
def Means(r: Maybe<&2, L.Kv>, +p: L.Parts) -> Type:
  match r:
    case None{}:
      {Nat.is_le(sig(p), 15n) == False{} : Bool}
    case Some{L.Kv{n, d}}:
      {Nat.is_le(sig(p), 15n) == True{} : Bool} & {n == L.Parts.name(p) : String} & {Dec.Canon(d) == True{} : Bool} & {Dec.same(d, raw(p)) == True{} : Bool}
