# eukhe: lemmas of area listing: a stem and its `.jsonl` name
#
# text_unsuffix answers Some{st} only for st then the suffix (lst.conv),
# so a file named `<n>.jsonl` is the file whose stem is n (lst.same_stem),
# and no file without the suffix has that name (lst.no_stem).

import Base
import ../../../bend/staging.bend as Sg
import ../../../laws/base.bend as LawsBase
import ../../base/staging.bend as LStg

def lst.get(m: Maybe<&2, String>, d: String) -> String:
  match m:
    case None{}:
      d
    case Some{x}:
      x

def lst.some_inj(-a: String, -b: String, e: {Some{a} == Some{b} : Maybe<&2, String>}) -> {a == b : String}:
  Equal.cong(Maybe<&2, String>, String, m => lst.get(m, a), Some{a}, Some{b}, e)

def lst.MD(m: Maybe<&2, String>, G: Type) -> Type:
  match m:
    case None{}:
      Unit
    case Some{x}:
      G

def lst.none_some(-G: Type, -b: String, e: {None{} == Some{b} : Maybe<&2, String>}) -> G:
  %e : lst.MD(_, G)
  Unit{}

def lst.empty(p: String, e: {String.is_empty(p) == True{} : Bool}) -> {p == "" : String}:
  match p:
    case SNil{}:
      {==}
    case SCon{c, t}:
      LStg.stg.absurdF({SCon{c, t} == "" : String}, e)

def lst.conv.nil(+p: String, b: Bool, eb: {String.is_empty(p) == b : Bool}, -st: String, e: {LawsBase.text_found(b, None{}) == Some{st} : Maybe<&2, String>}) -> {"" == String.append(st, p) : String}:
  match b:
    case True{}:
      %lst.some_inj("", st, e) : {"" == String.append(_, p) : String}
      Equal.sym(String, p, "", lst.empty(p, eb))
    case False{}:
      lst.none_some({"" == String.append(st, p) : String}, st, e)

def lst.conv.cons(+p: String, +c: Char, +t: String, b: Bool, eb: {LawsBase.text_same(SCon{c, t}, p) == b : Bool}, m: Maybe<&2, String>, em: {LawsBase.text_unsuffix(p, t) == m : Maybe<&2, String>}, -st: String, e: {LawsBase.text_found(b, LawsBase.text_cons(c, m)) == Some{st} : Maybe<&2, String>},
  ih: @r: String -> {LawsBase.text_unsuffix(p, t) == Some{r} : Maybe<&2, String>} -> {t == String.append(r, p) : String}) -> {SCon{c, t} == String.append(st, p) : String}:
  match b:
    case True{}:
      %lst.some_inj("", st, e) : {SCon{c, t} == String.append(_, p) : String}
      LStg.stg.same_eq(SCon{c, t}, p, eb)
    case False{}:
      match m:
        case None{}:
          lst.none_some({SCon{c, t} == String.append(st, p) : String}, st, e)
        case Some{+r}:
          %lst.some_inj(SCon{c, r}, st, e) : {SCon{c, t} == String.append(_, p) : String}
          Equal.cong(String, String, z => SCon{c, z}, t, String.append(r, p), ih(r, em))

# a text p is cut off s leaving st only when s is st then p
def lst.conv(+p: String, s: String, -st: String, e: {LawsBase.text_unsuffix(p, s) == Some{st} : Maybe<&2, String>}) -> {s == String.append(st, p) : String}:
  match s:
    case SNil{}:
      lst.conv.nil(p, String.is_empty(p), {==}, st, e)
    case SCon{+c, +t}:
      lst.conv.cons(p, c, t, LawsBase.text_same(SCon{c, t}, p), {==}, LawsBase.text_unsuffix(p, t), {==}, st, e, r => h => lst.conv(p, t, r, h))

# s is `<n>.jsonl`: then it ends with `.jsonl`, n before it
def lst.cut(+s: String, +n: String, h: {LawsBase.text_same(s, String.append(n, ".jsonl")) == True{} : Bool}) -> {LawsBase.text_unsuffix(".jsonl", s) == Some{n} : Maybe<&2, String>}:
  Equal.trans(Maybe<&2, String>, LawsBase.text_unsuffix(".jsonl", s), LawsBase.text_unsuffix(".jsonl", String.append(n, ".jsonl")), Some{n},
    Equal.cong(String, Maybe<&2, String>, z => LawsBase.text_unsuffix(".jsonl", z), s, String.append(n, ".jsonl"), LStg.stg.same_eq(s, String.append(n, ".jsonl"), h)),
    LStg.stg.unsuffix_app(n, ".jsonl"))

def lst.no_stem.b(b: Bool, +f: String, +n: String, eb: {LawsBase.text_same(f, String.append(n, ".jsonl")) == b : Bool}, em: {LawsBase.text_unsuffix(".jsonl", f) == None{} : Maybe<&2, String>}) -> {b == False{} : Bool}:
  match b:
    case False{}:
      {==}
    case True{}:
      lst.none_some({True{} == False{} : Bool}, n, Equal.trans(Maybe<&2, String>, None{}, LawsBase.text_unsuffix(".jsonl", f), Some{n}, Equal.sym(Maybe<&2, String>, LawsBase.text_unsuffix(".jsonl", f), None{}, em), lst.cut(f, n, eb)))

# a name without the suffix is no `<n>.jsonl`
def lst.no_stem(+f: String, +n: String, em: {LawsBase.text_unsuffix(".jsonl", f) == None{} : Maybe<&2, String>}) -> {LawsBase.text_same(f, String.append(n, ".jsonl")) == False{} : Bool}:
  lst.no_stem.b(LawsBase.text_same(f, String.append(n, ".jsonl")), f, n, {==}, em)

def lst.same_stem.b(b: Bool, +f: String, +st: String, +n: String, eb: {LawsBase.text_same(f, String.append(n, ".jsonl")) == b : Bool}, em: {LawsBase.text_unsuffix(".jsonl", f) == Some{st} : Maybe<&2, String>}, ec: {LawsBase.text_same(st, n) == False{} : Bool}) -> {b == False{} : Bool}:
  match b:
    case False{}:
      {==}
    case True{}:
      +esn = lst.some_inj(st, n, Equal.trans(Maybe<&2, String>, Some{st}, LawsBase.text_unsuffix(".jsonl", f), Some{n}, Equal.sym(Maybe<&2, String>, LawsBase.text_unsuffix(".jsonl", f), Some{st}, em), lst.cut(f, n, eb)))
      +r = Equal.trans(Bool, True{}, LawsBase.text_same(n, n), LawsBase.text_same(st, n), Equal.sym(Bool, LawsBase.text_same(n, n), True{}, LStg.stg.same_refl(n)), Equal.cong(String, Bool, z => LawsBase.text_same(z, n), n, st, Equal.sym(String, st, n, esn)))
      LStg.stg.absurd({True{} == False{} : Bool}, Equal.trans(Bool, True{}, LawsBase.text_same(st, n), False{}, r, ec))

def lst.same_stem.at(c: Bool, +f: String, +st: String, +n: String, ec: {LawsBase.text_same(st, n) == c : Bool}, +em: {LawsBase.text_unsuffix(".jsonl", f) == Some{st} : Maybe<&2, String>}) -> {LawsBase.text_same(f, String.append(n, ".jsonl")) == c : Bool}:
  match c:
    case True{}:
      +ef = Equal.trans(String, f, String.append(st, ".jsonl"), String.append(n, ".jsonl"), lst.conv(".jsonl", f, st, em), Equal.cong(String, String, z => String.append(z, ".jsonl"), st, n, LStg.stg.same_eq(st, n, ec)))
      %Equal.sym(String, f, String.append(n, ".jsonl"), ef) : {LawsBase.text_same(_, String.append(n, ".jsonl")) == True{} : Bool}
      LStg.stg.same_refl(String.append(n, ".jsonl"))
    case False{}:
      lst.same_stem.b(LawsBase.text_same(f, String.append(n, ".jsonl")), f, st, n, {==}, em, ec)

# the file of stem st is `<n>.jsonl` exactly when st is n
def lst.same_stem(+f: String, +st: String, +n: String, em: {LawsBase.text_unsuffix(".jsonl", f) == Some{st} : Maybe<&2, String>}) -> {LawsBase.text_same(f, String.append(n, ".jsonl")) == LawsBase.text_same(st, n) : Bool}:
  lst.same_stem.at(LawsBase.text_same(st, n), f, st, n, {==}, em)
