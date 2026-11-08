# eukhe: lemmas of area semver: the tag reader (Sv.Tag.after) is the
# spec's prefix test

import Base
import ../../../bend/semver.bend as Sv
import ../../base/staging.bend as LStaging

def pt.get(m: Maybe<&2, String>, d: String) -> String:
  match m:
    case Some{x}:
      x
    case None{}:
      d

def pt.some_inj(+a: String, -b: String, e: {Some{a} == Some{b} : Maybe<&2, String>}) -> {a == b : String}:
  Equal.cong(Maybe<&2, String>, String, m => pt.get(m, a), Some{a}, Some{b}, e)

# G for an answer, nothing for none
def pt.if_some(m: Maybe<&2, String>, G: Type) -> Type:
  match m:
    case Some{x}:
      G
    case None{}:
      Unit

# no answer is an answer
def pt.none_some(-G: Type, -r: String, e: {None{} == Some{r} : Maybe<&2, String>}) -> G:
  %e : pt.if_some(_, G)
  Unit{}

# Tag.after(p, t) answers r only when t is p then r
def pt.after_at(b: Bool, +c: Char, +d: Char, +pr: String, +tr: String, +r: String, eb: {Char.is_eq(c, d) == b : Bool}, h: {Sv.Tag.after.when(b, Sv.Tag.after(pr, tr)) == Some{r} : Maybe<&2, String>}, ih: {Sv.Tag.after(pr, tr) == Some{r} : Maybe<&2, String>} -> {tr == String.append(pr, r) : String}) -> {SCon{d, tr} == SCon{c, String.append(pr, r)} : String}:
  match b:
    case True{}:
      +ec = LStaging.stg.char_sound(c, d, eb)
      %ec : {SCon{_, tr} == SCon{c, String.append(pr, r)} : String}
      %Equal.sym(String, tr, String.append(pr, r), ih(h)) : {SCon{c, _} == SCon{c, String.append(pr, r)} : String}
      {==}
    case False{}:
      pt.none_some({SCon{d, tr} == SCon{c, String.append(pr, r)} : String}, r, h)

def pt.after_exact(p: String, +t: String, +r: String, h: {Sv.Tag.after(p, t) == Some{r} : Maybe<&2, String>}) -> {t == String.append(p, r) : String}:
  match p t:
    case SNil{} _:
      pt.some_inj(t, r, h)
    case SCon{c, pr} SNil{}:
      pt.none_some({SNil{} == String.append(SCon{c, pr}, r) : String}, r, h)
    case SCon{+c, +pr} SCon{+d, +tr}:
      pt.after_at(Char.is_eq(c, d), c, d, pr, tr, r, {==}, h, e => pt.after_exact(pr, tr, r, e))

# Tag.after(p, p then r) answers r
def pt.after_spelled(p: String, +r: String) -> {Sv.Tag.after(p, String.append(p, r)) == Some{r} : Maybe<&2, String>}:
  match p:
    case SNil{}:
      {==}
    case SCon{+c, +pr}:
      %Equal.sym(Bool, Char.is_eq(c, c), True{}, LStaging.stg.char_refl(c)) : {Sv.Tag.after.when(_, Sv.Tag.after(pr, String.append(pr, r))) == Some{r} : Maybe<&2, String>}
      pt.after_spelled(pr, r)
