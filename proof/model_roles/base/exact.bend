# eukhe: lemmas of area model_roles on the exactness of the request
# decoders: every decoder layer that answers Got{..} read the prefix of
# an encoding, down to a choice, whose selector Wr.get_nat reads only in
# its canonical spelling (Wire.wire_nat_exact).

import Base
import ../../../bend/model_roles.bend as Mr
import ../../../bend/ffi_model_roles.bend as FMr
import ../../../bend/wire.bend as Wr
import ../../../laws/wire.bend as Wire

# Decoder answers
# ---------------

def mx.DG(-A: Data, d: Wr.Dec<A>, G: Type) -> Type:
  match d:
    case Wr.Got{v, r}:
      G
    case Wr.Bad{}:
      Unit

def mx.val(-A: Data, d: Wr.Dec<A>, x: A) -> A:
  match d:
    case Wr.Got{v, r}:
      v
    case Wr.Bad{}:
      x

def mx.rst(-A: Data, d: Wr.Dec<A>) -> String:
  match d:
    case Wr.Got{v, r}:
      r
    case Wr.Bad{}:
      ""

def mx.bad_got(-A: Data, -G: Type, -x: A, -s: String, e: {Wr.Bad{} == Wr.Got{x, s} : Wr.Dec<A>}) -> G:
  %e : mx.DG(A, _, G)
  Unit{}

def mx.got_v(-A: Data, +a: A, -b: A, -s: String, -r: String, e: {Wr.Got{a, s} == Wr.Got{b, r} : Wr.Dec<A>}) -> {a == b : A}:
  Equal.cong(Wr.Dec<A>, A, d => mx.val(A, d, a), Wr.Got{a, s}, Wr.Got{b, r}, e)

def mx.got_r(-A: Data, -a: A, -b: A, -s: String, -r: String, e: {Wr.Got{a, s} == Wr.Got{b, r} : Wr.Dec<A>}) -> {s == r : String}:
  Equal.cong(Wr.Dec<A>, String, d => mx.rst(A, d), Wr.Got{a, s}, Wr.Got{b, r}, e)

# A choice
# --------

def mx.choice_n(d: Wr.Dec<Nat>, +s1: String, +c: Mr.Choice, +rest: String, ed: {Wr.get_nat(s1) == d : Wr.Dec<Nat>}, +h: {FMr.get_choice.n(d) == Wr.Got{c, rest} : Wr.Dec<Mr.Choice>}) -> {Wr.put_nat(1n, s1) == FMr.put_choice(c, rest) : String}:
  match d:
    case Wr.Got{+n, +s2}:
      %mx.got_v(Mr.Choice, Mr.Sel{n}, c, s2, rest, h) : {Wr.put_nat(1n, s1) == FMr.put_choice(_, rest) : String}
      %mx.got_r(Mr.Choice, Mr.Sel{n}, c, s2, rest, h) : {Wr.put_nat(1n, s1) == FMr.put_choice(Mr.Sel{n}, _) : String}
      %Equal.sym(String, s1, Wr.put_nat(n, s2), Wire.wire_nat_exact(s1, n, s2, ed)) : {Wr.put_nat(1n, _) == FMr.put_choice(Mr.Sel{n}, s2) : String}
      {==}
    case Wr.Bad{}:
      mx.bad_got(Mr.Choice, {Wr.put_nat(1n, s1) == FMr.put_choice(c, rest) : String}, c, rest, h)

# a decoded choice is its encoding (the law mrw_choice_exact)
def mx.choice(d: Wr.Dec<Nat>, +s: String, +c: Mr.Choice, +rest: String, ed: {Wr.get_nat(s) == d : Wr.Dec<Nat>}, +h: {FMr.get_choice.go(d) == Wr.Got{c, rest} : Wr.Dec<Mr.Choice>}) -> {s == FMr.put_choice(c, rest) : String}:
  match d:
    case Wr.Got{+tg, +s1}:
      match tg:
        case 0n:
          %mx.got_v(Mr.Choice, Mr.Unset{}, c, s1, rest, h) : {s == FMr.put_choice(_, rest) : String}
          %mx.got_r(Mr.Choice, Mr.Unset{}, c, s1, rest, h) : {s == FMr.put_choice(Mr.Unset{}, _) : String}
          Wire.wire_nat_exact(s, 0n, s1, ed)
        case 1n:
          Equal.trans(String, s, Wr.put_nat(1n, s1), FMr.put_choice(c, rest), Wire.wire_nat_exact(s, 1n, s1, ed), mx.choice_n(Wr.get_nat(s1), s1, c, rest, {==}, h))
        case 2n+k:
          mx.bad_got(Mr.Choice, {s == FMr.put_choice(c, rest) : String}, c, rest, h)
    case Wr.Bad{}:
      mx.bad_got(Mr.Choice, {s == FMr.put_choice(c, rest) : String}, c, rest, h)

# the same, turned around for rewriting
def mx.cex(+s: String, +c: Mr.Choice, +rest: String, h: {FMr.get_choice(s) == Wr.Got{c, rest} : Wr.Dec<Mr.Choice>}) -> {FMr.put_choice(c, rest) == s : String}:
  Equal.sym(String, s, FMr.put_choice(c, rest), mx.choice(Wr.get_nat(s), s, c, rest, {==}, h))

# The own settings, one layer per role (last role first)
# -----------------------------------------------------
def mx.owns_11(d: Wr.Dec<Mr.Choice>, +s: String, +c0: Mr.Choice, +c1: Mr.Choice, +c2: Mr.Choice, +c3: Mr.Choice, +c4: Mr.Choice, +c5: Mr.Choice, +c6: Mr.Choice, +c7: Mr.Choice, +c8: Mr.Choice, +c9: Mr.Choice, +c10: Mr.Choice, +o: Mr.Owns, +rest: String, ed: {FMr.get_choice(s) == d : Wr.Dec<Mr.Choice>}, +h: {FMr.get_owns.dictation(c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, d) == Wr.Got{o, rest} : Wr.Dec<Mr.Owns>}) -> {FMr.put_choice(c0, FMr.put_choice(c1, FMr.put_choice(c2, FMr.put_choice(c3, FMr.put_choice(c4, FMr.put_choice(c5, FMr.put_choice(c6, FMr.put_choice(c7, FMr.put_choice(c8, FMr.put_choice(c9, FMr.put_choice(c10, s))))))))))) == FMr.put_owns(o, rest) : String}:
  match d:
    case Wr.Got{+c11, +s1}:
      %mx.cex(s, c11, s1, ed) : {FMr.put_choice(c0, FMr.put_choice(c1, FMr.put_choice(c2, FMr.put_choice(c3, FMr.put_choice(c4, FMr.put_choice(c5, FMr.put_choice(c6, FMr.put_choice(c7, FMr.put_choice(c8, FMr.put_choice(c9, FMr.put_choice(c10, _))))))))))) == FMr.put_owns(o, rest) : String}
      %mx.got_v(Mr.Owns, Mr.Owns{c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11}, o, s1, rest, h) : {FMr.put_choice(c0, FMr.put_choice(c1, FMr.put_choice(c2, FMr.put_choice(c3, FMr.put_choice(c4, FMr.put_choice(c5, FMr.put_choice(c6, FMr.put_choice(c7, FMr.put_choice(c8, FMr.put_choice(c9, FMr.put_choice(c10, FMr.put_choice(c11, s1)))))))))))) == FMr.put_owns(_, rest) : String}
      %mx.got_r(Mr.Owns, Mr.Owns{c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11}, o, s1, rest, h) : {FMr.put_choice(c0, FMr.put_choice(c1, FMr.put_choice(c2, FMr.put_choice(c3, FMr.put_choice(c4, FMr.put_choice(c5, FMr.put_choice(c6, FMr.put_choice(c7, FMr.put_choice(c8, FMr.put_choice(c9, FMr.put_choice(c10, FMr.put_choice(c11, s1)))))))))))) == FMr.put_owns(Mr.Owns{c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11}, _) : String}
      {==}
    case Wr.Bad{}:
      mx.bad_got(Mr.Owns, {FMr.put_choice(c0, FMr.put_choice(c1, FMr.put_choice(c2, FMr.put_choice(c3, FMr.put_choice(c4, FMr.put_choice(c5, FMr.put_choice(c6, FMr.put_choice(c7, FMr.put_choice(c8, FMr.put_choice(c9, FMr.put_choice(c10, s))))))))))) == FMr.put_owns(o, rest) : String}, o, rest, h)

def mx.owns_10(d: Wr.Dec<Mr.Choice>, +s: String, +c0: Mr.Choice, +c1: Mr.Choice, +c2: Mr.Choice, +c3: Mr.Choice, +c4: Mr.Choice, +c5: Mr.Choice, +c6: Mr.Choice, +c7: Mr.Choice, +c8: Mr.Choice, +c9: Mr.Choice, +o: Mr.Owns, +rest: String, ed: {FMr.get_choice(s) == d : Wr.Dec<Mr.Choice>}, +h: {FMr.get_owns.speech(c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, d) == Wr.Got{o, rest} : Wr.Dec<Mr.Owns>}) -> {FMr.put_choice(c0, FMr.put_choice(c1, FMr.put_choice(c2, FMr.put_choice(c3, FMr.put_choice(c4, FMr.put_choice(c5, FMr.put_choice(c6, FMr.put_choice(c7, FMr.put_choice(c8, FMr.put_choice(c9, s)))))))))) == FMr.put_owns(o, rest) : String}:
  match d:
    case Wr.Got{+c10, +s1}:
      %mx.cex(s, c10, s1, ed) : {FMr.put_choice(c0, FMr.put_choice(c1, FMr.put_choice(c2, FMr.put_choice(c3, FMr.put_choice(c4, FMr.put_choice(c5, FMr.put_choice(c6, FMr.put_choice(c7, FMr.put_choice(c8, FMr.put_choice(c9, _)))))))))) == FMr.put_owns(o, rest) : String}
      mx.owns_11(FMr.get_choice(s1), s1, c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, o, rest, {==}, h)
    case Wr.Bad{}:
      mx.bad_got(Mr.Owns, {FMr.put_choice(c0, FMr.put_choice(c1, FMr.put_choice(c2, FMr.put_choice(c3, FMr.put_choice(c4, FMr.put_choice(c5, FMr.put_choice(c6, FMr.put_choice(c7, FMr.put_choice(c8, FMr.put_choice(c9, s)))))))))) == FMr.put_owns(o, rest) : String}, o, rest, h)

def mx.owns_9(d: Wr.Dec<Mr.Choice>, +s: String, +c0: Mr.Choice, +c1: Mr.Choice, +c2: Mr.Choice, +c3: Mr.Choice, +c4: Mr.Choice, +c5: Mr.Choice, +c6: Mr.Choice, +c7: Mr.Choice, +c8: Mr.Choice, +o: Mr.Owns, +rest: String, ed: {FMr.get_choice(s) == d : Wr.Dec<Mr.Choice>}, +h: {FMr.get_owns.translate(c0, c1, c2, c3, c4, c5, c6, c7, c8, d) == Wr.Got{o, rest} : Wr.Dec<Mr.Owns>}) -> {FMr.put_choice(c0, FMr.put_choice(c1, FMr.put_choice(c2, FMr.put_choice(c3, FMr.put_choice(c4, FMr.put_choice(c5, FMr.put_choice(c6, FMr.put_choice(c7, FMr.put_choice(c8, s))))))))) == FMr.put_owns(o, rest) : String}:
  match d:
    case Wr.Got{+c9, +s1}:
      %mx.cex(s, c9, s1, ed) : {FMr.put_choice(c0, FMr.put_choice(c1, FMr.put_choice(c2, FMr.put_choice(c3, FMr.put_choice(c4, FMr.put_choice(c5, FMr.put_choice(c6, FMr.put_choice(c7, FMr.put_choice(c8, _))))))))) == FMr.put_owns(o, rest) : String}
      mx.owns_10(FMr.get_choice(s1), s1, c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, o, rest, {==}, h)
    case Wr.Bad{}:
      mx.bad_got(Mr.Owns, {FMr.put_choice(c0, FMr.put_choice(c1, FMr.put_choice(c2, FMr.put_choice(c3, FMr.put_choice(c4, FMr.put_choice(c5, FMr.put_choice(c6, FMr.put_choice(c7, FMr.put_choice(c8, s))))))))) == FMr.put_owns(o, rest) : String}, o, rest, h)

def mx.owns_8(d: Wr.Dec<Mr.Choice>, +s: String, +c0: Mr.Choice, +c1: Mr.Choice, +c2: Mr.Choice, +c3: Mr.Choice, +c4: Mr.Choice, +c5: Mr.Choice, +c6: Mr.Choice, +c7: Mr.Choice, +o: Mr.Owns, +rest: String, ed: {FMr.get_choice(s) == d : Wr.Dec<Mr.Choice>}, +h: {FMr.get_owns.judge(c0, c1, c2, c3, c4, c5, c6, c7, d) == Wr.Got{o, rest} : Wr.Dec<Mr.Owns>}) -> {FMr.put_choice(c0, FMr.put_choice(c1, FMr.put_choice(c2, FMr.put_choice(c3, FMr.put_choice(c4, FMr.put_choice(c5, FMr.put_choice(c6, FMr.put_choice(c7, s)))))))) == FMr.put_owns(o, rest) : String}:
  match d:
    case Wr.Got{+c8, +s1}:
      %mx.cex(s, c8, s1, ed) : {FMr.put_choice(c0, FMr.put_choice(c1, FMr.put_choice(c2, FMr.put_choice(c3, FMr.put_choice(c4, FMr.put_choice(c5, FMr.put_choice(c6, FMr.put_choice(c7, _)))))))) == FMr.put_owns(o, rest) : String}
      mx.owns_9(FMr.get_choice(s1), s1, c0, c1, c2, c3, c4, c5, c6, c7, c8, o, rest, {==}, h)
    case Wr.Bad{}:
      mx.bad_got(Mr.Owns, {FMr.put_choice(c0, FMr.put_choice(c1, FMr.put_choice(c2, FMr.put_choice(c3, FMr.put_choice(c4, FMr.put_choice(c5, FMr.put_choice(c6, FMr.put_choice(c7, s)))))))) == FMr.put_owns(o, rest) : String}, o, rest, h)

def mx.owns_7(d: Wr.Dec<Mr.Choice>, +s: String, +c0: Mr.Choice, +c1: Mr.Choice, +c2: Mr.Choice, +c3: Mr.Choice, +c4: Mr.Choice, +c5: Mr.Choice, +c6: Mr.Choice, +o: Mr.Owns, +rest: String, ed: {FMr.get_choice(s) == d : Wr.Dec<Mr.Choice>}, +h: {FMr.get_owns.titles(c0, c1, c2, c3, c4, c5, c6, d) == Wr.Got{o, rest} : Wr.Dec<Mr.Owns>}) -> {FMr.put_choice(c0, FMr.put_choice(c1, FMr.put_choice(c2, FMr.put_choice(c3, FMr.put_choice(c4, FMr.put_choice(c5, FMr.put_choice(c6, s))))))) == FMr.put_owns(o, rest) : String}:
  match d:
    case Wr.Got{+c7, +s1}:
      %mx.cex(s, c7, s1, ed) : {FMr.put_choice(c0, FMr.put_choice(c1, FMr.put_choice(c2, FMr.put_choice(c3, FMr.put_choice(c4, FMr.put_choice(c5, FMr.put_choice(c6, _))))))) == FMr.put_owns(o, rest) : String}
      mx.owns_8(FMr.get_choice(s1), s1, c0, c1, c2, c3, c4, c5, c6, c7, o, rest, {==}, h)
    case Wr.Bad{}:
      mx.bad_got(Mr.Owns, {FMr.put_choice(c0, FMr.put_choice(c1, FMr.put_choice(c2, FMr.put_choice(c3, FMr.put_choice(c4, FMr.put_choice(c5, FMr.put_choice(c6, s))))))) == FMr.put_owns(o, rest) : String}, o, rest, h)

def mx.owns_6(d: Wr.Dec<Mr.Choice>, +s: String, +c0: Mr.Choice, +c1: Mr.Choice, +c2: Mr.Choice, +c3: Mr.Choice, +c4: Mr.Choice, +c5: Mr.Choice, +o: Mr.Owns, +rest: String, ed: {FMr.get_choice(s) == d : Wr.Dec<Mr.Choice>}, +h: {FMr.get_owns.query(c0, c1, c2, c3, c4, c5, d) == Wr.Got{o, rest} : Wr.Dec<Mr.Owns>}) -> {FMr.put_choice(c0, FMr.put_choice(c1, FMr.put_choice(c2, FMr.put_choice(c3, FMr.put_choice(c4, FMr.put_choice(c5, s)))))) == FMr.put_owns(o, rest) : String}:
  match d:
    case Wr.Got{+c6, +s1}:
      %mx.cex(s, c6, s1, ed) : {FMr.put_choice(c0, FMr.put_choice(c1, FMr.put_choice(c2, FMr.put_choice(c3, FMr.put_choice(c4, FMr.put_choice(c5, _)))))) == FMr.put_owns(o, rest) : String}
      mx.owns_7(FMr.get_choice(s1), s1, c0, c1, c2, c3, c4, c5, c6, o, rest, {==}, h)
    case Wr.Bad{}:
      mx.bad_got(Mr.Owns, {FMr.put_choice(c0, FMr.put_choice(c1, FMr.put_choice(c2, FMr.put_choice(c3, FMr.put_choice(c4, FMr.put_choice(c5, s)))))) == FMr.put_owns(o, rest) : String}, o, rest, h)

def mx.owns_5(d: Wr.Dec<Mr.Choice>, +s: String, +c0: Mr.Choice, +c1: Mr.Choice, +c2: Mr.Choice, +c3: Mr.Choice, +c4: Mr.Choice, +o: Mr.Owns, +rest: String, ed: {FMr.get_choice(s) == d : Wr.Dec<Mr.Choice>}, +h: {FMr.get_owns.gateway(c0, c1, c2, c3, c4, d) == Wr.Got{o, rest} : Wr.Dec<Mr.Owns>}) -> {FMr.put_choice(c0, FMr.put_choice(c1, FMr.put_choice(c2, FMr.put_choice(c3, FMr.put_choice(c4, s))))) == FMr.put_owns(o, rest) : String}:
  match d:
    case Wr.Got{+c5, +s1}:
      %mx.cex(s, c5, s1, ed) : {FMr.put_choice(c0, FMr.put_choice(c1, FMr.put_choice(c2, FMr.put_choice(c3, FMr.put_choice(c4, _))))) == FMr.put_owns(o, rest) : String}
      mx.owns_6(FMr.get_choice(s1), s1, c0, c1, c2, c3, c4, c5, o, rest, {==}, h)
    case Wr.Bad{}:
      mx.bad_got(Mr.Owns, {FMr.put_choice(c0, FMr.put_choice(c1, FMr.put_choice(c2, FMr.put_choice(c3, FMr.put_choice(c4, s))))) == FMr.put_owns(o, rest) : String}, o, rest, h)

def mx.owns_4(d: Wr.Dec<Mr.Choice>, +s: String, +c0: Mr.Choice, +c1: Mr.Choice, +c2: Mr.Choice, +c3: Mr.Choice, +o: Mr.Owns, +rest: String, ed: {FMr.get_choice(s) == d : Wr.Dec<Mr.Choice>}, +h: {FMr.get_owns.subagent(c0, c1, c2, c3, d) == Wr.Got{o, rest} : Wr.Dec<Mr.Owns>}) -> {FMr.put_choice(c0, FMr.put_choice(c1, FMr.put_choice(c2, FMr.put_choice(c3, s)))) == FMr.put_owns(o, rest) : String}:
  match d:
    case Wr.Got{+c4, +s1}:
      %mx.cex(s, c4, s1, ed) : {FMr.put_choice(c0, FMr.put_choice(c1, FMr.put_choice(c2, FMr.put_choice(c3, _)))) == FMr.put_owns(o, rest) : String}
      mx.owns_5(FMr.get_choice(s1), s1, c0, c1, c2, c3, c4, o, rest, {==}, h)
    case Wr.Bad{}:
      mx.bad_got(Mr.Owns, {FMr.put_choice(c0, FMr.put_choice(c1, FMr.put_choice(c2, FMr.put_choice(c3, s)))) == FMr.put_owns(o, rest) : String}, o, rest, h)

def mx.owns_3(d: Wr.Dec<Mr.Choice>, +s: String, +c0: Mr.Choice, +c1: Mr.Choice, +c2: Mr.Choice, +o: Mr.Owns, +rest: String, ed: {FMr.get_choice(s) == d : Wr.Dec<Mr.Choice>}, +h: {FMr.get_owns.image(c0, c1, c2, d) == Wr.Got{o, rest} : Wr.Dec<Mr.Owns>}) -> {FMr.put_choice(c0, FMr.put_choice(c1, FMr.put_choice(c2, s))) == FMr.put_owns(o, rest) : String}:
  match d:
    case Wr.Got{+c3, +s1}:
      %mx.cex(s, c3, s1, ed) : {FMr.put_choice(c0, FMr.put_choice(c1, FMr.put_choice(c2, _))) == FMr.put_owns(o, rest) : String}
      mx.owns_4(FMr.get_choice(s1), s1, c0, c1, c2, c3, o, rest, {==}, h)
    case Wr.Bad{}:
      mx.bad_got(Mr.Owns, {FMr.put_choice(c0, FMr.put_choice(c1, FMr.put_choice(c2, s))) == FMr.put_owns(o, rest) : String}, o, rest, h)

def mx.owns_2(d: Wr.Dec<Mr.Choice>, +s: String, +c0: Mr.Choice, +c1: Mr.Choice, +o: Mr.Owns, +rest: String, ed: {FMr.get_choice(s) == d : Wr.Dec<Mr.Choice>}, +h: {FMr.get_owns.auxiliary(c0, c1, d) == Wr.Got{o, rest} : Wr.Dec<Mr.Owns>}) -> {FMr.put_choice(c0, FMr.put_choice(c1, s)) == FMr.put_owns(o, rest) : String}:
  match d:
    case Wr.Got{+c2, +s1}:
      %mx.cex(s, c2, s1, ed) : {FMr.put_choice(c0, FMr.put_choice(c1, _)) == FMr.put_owns(o, rest) : String}
      mx.owns_3(FMr.get_choice(s1), s1, c0, c1, c2, o, rest, {==}, h)
    case Wr.Bad{}:
      mx.bad_got(Mr.Owns, {FMr.put_choice(c0, FMr.put_choice(c1, s)) == FMr.put_owns(o, rest) : String}, o, rest, h)

def mx.owns_1(d: Wr.Dec<Mr.Choice>, +s: String, +c0: Mr.Choice, +o: Mr.Owns, +rest: String, ed: {FMr.get_choice(s) == d : Wr.Dec<Mr.Choice>}, +h: {FMr.get_owns.memory(c0, d) == Wr.Got{o, rest} : Wr.Dec<Mr.Owns>}) -> {FMr.put_choice(c0, s) == FMr.put_owns(o, rest) : String}:
  match d:
    case Wr.Got{+c1, +s1}:
      %mx.cex(s, c1, s1, ed) : {FMr.put_choice(c0, _) == FMr.put_owns(o, rest) : String}
      mx.owns_2(FMr.get_choice(s1), s1, c0, c1, o, rest, {==}, h)
    case Wr.Bad{}:
      mx.bad_got(Mr.Owns, {FMr.put_choice(c0, s) == FMr.put_owns(o, rest) : String}, o, rest, h)

def mx.owns_0(d: Wr.Dec<Mr.Choice>, +s: String, +o: Mr.Owns, +rest: String, ed: {FMr.get_choice(s) == d : Wr.Dec<Mr.Choice>}, +h: {FMr.get_owns.chat(d) == Wr.Got{o, rest} : Wr.Dec<Mr.Owns>}) -> {s == FMr.put_owns(o, rest) : String}:
  match d:
    case Wr.Got{+c0, +s1}:
      %mx.cex(s, c0, s1, ed) : {_ == FMr.put_owns(o, rest) : String}
      mx.owns_1(FMr.get_choice(s1), s1, c0, o, rest, {==}, h)
    case Wr.Bad{}:
      mx.bad_got(Mr.Owns, {s == FMr.put_owns(o, rest) : String}, o, rest, h)

# decoded own settings are their encoding, turned around
def mx.oex(+s: String, +o: Mr.Owns, +rest: String, h: {FMr.get_owns(s) == Wr.Got{o, rest} : Wr.Dec<Mr.Owns>}) -> {FMr.put_owns(o, rest) == s : String}:
  Equal.sym(String, s, FMr.put_owns(o, rest), mx.owns_0(FMr.get_choice(s), s, o, rest, {==}, h))

# The request
# -----------

def mx.in_all(d: Wr.Dec<Mr.Choice>, +s1: String, +ow: Mr.Owns, +x: Mr.In, +rest: String, ed: {FMr.get_choice(s1) == d : Wr.Dec<Mr.Choice>}, +h: {FMr.get_in.all(ow, d) == Wr.Got{x, rest} : Wr.Dec<Mr.In>}) -> {FMr.put_owns(ow, s1) == FMr.put_in(x, rest) : String}:
  match d:
    case Wr.Got{+al, +s2}:
      %mx.got_v(Mr.In, Mr.In{ow, al}, x, s2, rest, h) : {FMr.put_owns(ow, s1) == FMr.put_in(_, rest) : String}
      %mx.got_r(Mr.In, Mr.In{ow, al}, x, s2, rest, h) : {FMr.put_owns(ow, s1) == FMr.put_in(Mr.In{ow, al}, _) : String}
      %mx.cex(s1, al, s2, ed) : {FMr.put_owns(ow, _) == FMr.put_in(Mr.In{ow, al}, s2) : String}
      {==}
    case Wr.Bad{}:
      mx.bad_got(Mr.In, {FMr.put_owns(ow, s1) == FMr.put_in(x, rest) : String}, x, rest, h)

# a decoded request is its encoding (the law mrw_in_exact)
def mx.in_go(d: Wr.Dec<Mr.Owns>, +s: String, +x: Mr.In, +rest: String, ed: {FMr.get_owns(s) == d : Wr.Dec<Mr.Owns>}, +h: {FMr.get_in.go(d) == Wr.Got{x, rest} : Wr.Dec<Mr.In>}) -> {s == FMr.put_in(x, rest) : String}:
  match d:
    case Wr.Got{+ow, +s1}:
      %mx.oex(s, ow, s1, ed) : {_ == FMr.put_in(x, rest) : String}
      mx.in_all(FMr.get_choice(s1), s1, ow, x, rest, {==}, h)
    case Wr.Bad{}:
      mx.bad_got(Mr.In, {s == FMr.put_in(x, rest) : String}, x, rest, h)
