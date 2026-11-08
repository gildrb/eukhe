# eukhe: lemmas of area model_roles: every setting a request decoder of
# bend/ffi_model_roles.bend answers Got{..} for fits the wire (its
# selector is read by Wr.get_nat: Wire.wire_nat_decoded_fits), carried
# one decoder layer per role (first role first)

import Base
import ../../../bend/model_roles.bend as Mr
import ../../../bend/ffi_model_roles.bend as FMr
import ../../../bend/wire.bend as Wr
import ../../../laws/base.bend as LawsBase
import ../../../laws/wire.bend as Wire
import ../../../laws/model_roles.bend as ModelRoles
import ../../wire/wire_nat_decoded_fits.bend as PWireNatDecodedFits
import ./exact.bend as LX

# both sides true: the conjunction is true
def mf.and_t(-a: Bool, -b: Bool, ha: {a == True{} : Bool}, hb: {b == True{} : Bool}) -> {Bool.and(a, b) == True{} : Bool}:
  %Equal.sym(Bool, a, True{}, ha) : {Bool.and(_, b) == True{} : Bool}
  hb

# A choice
# --------

def mf.choice_n(d: Wr.Dec<Nat>, +s1: String, +c: Mr.Choice, +rest: String, ed: {Wr.get_nat(s1) == d : Wr.Dec<Nat>}, +h: {FMr.get_choice.n(d) == Wr.Got{c, rest} : Wr.Dec<Mr.Choice>}) -> {ModelRoles.mrw_choice_fits(c) == True{} : Bool}:
  match d:
    case Wr.Got{+n, +s2}:
      %LX.mx.got_v(Mr.Choice, Mr.Sel{n}, c, s2, rest, h) : {ModelRoles.mrw_choice_fits(_) == True{} : Bool}
      Wire.wire_nat_decoded_fits(s1, n, s2, ed)
    case Wr.Bad{}:
      LX.mx.bad_got(Mr.Choice, {ModelRoles.mrw_choice_fits(c) == True{} : Bool}, c, rest, h)

def mf.choice_go(d: Wr.Dec<Nat>, +c: Mr.Choice, +rest: String, +h: {FMr.get_choice.go(d) == Wr.Got{c, rest} : Wr.Dec<Mr.Choice>}) -> {ModelRoles.mrw_choice_fits(c) == True{} : Bool}:
  match d:
    case Wr.Got{+tg, +s1}:
      match tg:
        case 0n:
          %LX.mx.got_v(Mr.Choice, Mr.Unset{}, c, s1, rest, h) : {ModelRoles.mrw_choice_fits(_) == True{} : Bool}
          {==}
        case 1n:
          mf.choice_n(Wr.get_nat(s1), s1, c, rest, {==}, h)
        case 2n+k:
          LX.mx.bad_got(Mr.Choice, {ModelRoles.mrw_choice_fits(c) == True{} : Bool}, c, rest, h)
    case Wr.Bad{}:
      LX.mx.bad_got(Mr.Choice, {ModelRoles.mrw_choice_fits(c) == True{} : Bool}, c, rest, h)

# a decoded setting fits the wire
def mf.choice(+s: String, +c: Mr.Choice, +rest: String, h: {FMr.get_choice(s) == Wr.Got{c, rest} : Wr.Dec<Mr.Choice>}) -> {ModelRoles.mrw_choice_fits(c) == True{} : Bool}:
  mf.choice_go(Wr.get_nat(s), c, rest, h)

# The own settings, one layer per role
# ------------------------------------

def mf.owns_12(d: Wr.Dec<Mr.Choice>, +s: String, +c0: Mr.Choice, +c1: Mr.Choice, +c2: Mr.Choice, +c3: Mr.Choice, +c4: Mr.Choice, +c5: Mr.Choice, +c6: Mr.Choice, +c7: Mr.Choice, +c8: Mr.Choice, +c9: Mr.Choice, +c10: Mr.Choice, +c11: Mr.Choice, +o: Mr.Owns, +rest: String, ed: {FMr.get_choice(s) == d : Wr.Dec<Mr.Choice>}, +h: {FMr.get_owns.dictation(c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, d) == Wr.Got{o, rest} : Wr.Dec<Mr.Owns>}, f0: {ModelRoles.mrw_choice_fits(c0) == True{} : Bool}, f1: {ModelRoles.mrw_choice_fits(c1) == True{} : Bool}, f2: {ModelRoles.mrw_choice_fits(c2) == True{} : Bool}, f3: {ModelRoles.mrw_choice_fits(c3) == True{} : Bool}, f4: {ModelRoles.mrw_choice_fits(c4) == True{} : Bool}, f5: {ModelRoles.mrw_choice_fits(c5) == True{} : Bool}, f6: {ModelRoles.mrw_choice_fits(c6) == True{} : Bool}, f7: {ModelRoles.mrw_choice_fits(c7) == True{} : Bool}, f8: {ModelRoles.mrw_choice_fits(c8) == True{} : Bool}, f9: {ModelRoles.mrw_choice_fits(c9) == True{} : Bool}, f10: {ModelRoles.mrw_choice_fits(c10) == True{} : Bool}, f11: {ModelRoles.mrw_choice_fits(c11) == True{} : Bool}) -> {ModelRoles.mrw_owns_fits(o) == True{} : Bool}:
  match d:
    case Wr.Got{+c12, +s1}:
      f12 = mf.choice(s, c12, s1, ed)
      %LX.mx.got_v(Mr.Owns, Mr.Owns{c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12}, o, s1, rest, h) : {ModelRoles.mrw_owns_fits(_) == True{} : Bool}
      mf.and_t(ModelRoles.mrw_choice_fits(c0), Bool.and(ModelRoles.mrw_choice_fits(c1), Bool.and(ModelRoles.mrw_choice_fits(c2), Bool.and(ModelRoles.mrw_choice_fits(c3), Bool.and(ModelRoles.mrw_choice_fits(c4), Bool.and(ModelRoles.mrw_choice_fits(c5), Bool.and(ModelRoles.mrw_choice_fits(c6), Bool.and(ModelRoles.mrw_choice_fits(c7), Bool.and(ModelRoles.mrw_choice_fits(c8), Bool.and(ModelRoles.mrw_choice_fits(c9), Bool.and(ModelRoles.mrw_choice_fits(c10), Bool.and(ModelRoles.mrw_choice_fits(c11), ModelRoles.mrw_choice_fits(c12)))))))))))), f0, mf.and_t(ModelRoles.mrw_choice_fits(c1), Bool.and(ModelRoles.mrw_choice_fits(c2), Bool.and(ModelRoles.mrw_choice_fits(c3), Bool.and(ModelRoles.mrw_choice_fits(c4), Bool.and(ModelRoles.mrw_choice_fits(c5), Bool.and(ModelRoles.mrw_choice_fits(c6), Bool.and(ModelRoles.mrw_choice_fits(c7), Bool.and(ModelRoles.mrw_choice_fits(c8), Bool.and(ModelRoles.mrw_choice_fits(c9), Bool.and(ModelRoles.mrw_choice_fits(c10), Bool.and(ModelRoles.mrw_choice_fits(c11), ModelRoles.mrw_choice_fits(c12))))))))))), f1, mf.and_t(ModelRoles.mrw_choice_fits(c2), Bool.and(ModelRoles.mrw_choice_fits(c3), Bool.and(ModelRoles.mrw_choice_fits(c4), Bool.and(ModelRoles.mrw_choice_fits(c5), Bool.and(ModelRoles.mrw_choice_fits(c6), Bool.and(ModelRoles.mrw_choice_fits(c7), Bool.and(ModelRoles.mrw_choice_fits(c8), Bool.and(ModelRoles.mrw_choice_fits(c9), Bool.and(ModelRoles.mrw_choice_fits(c10), Bool.and(ModelRoles.mrw_choice_fits(c11), ModelRoles.mrw_choice_fits(c12)))))))))), f2, mf.and_t(ModelRoles.mrw_choice_fits(c3), Bool.and(ModelRoles.mrw_choice_fits(c4), Bool.and(ModelRoles.mrw_choice_fits(c5), Bool.and(ModelRoles.mrw_choice_fits(c6), Bool.and(ModelRoles.mrw_choice_fits(c7), Bool.and(ModelRoles.mrw_choice_fits(c8), Bool.and(ModelRoles.mrw_choice_fits(c9), Bool.and(ModelRoles.mrw_choice_fits(c10), Bool.and(ModelRoles.mrw_choice_fits(c11), ModelRoles.mrw_choice_fits(c12))))))))), f3, mf.and_t(ModelRoles.mrw_choice_fits(c4), Bool.and(ModelRoles.mrw_choice_fits(c5), Bool.and(ModelRoles.mrw_choice_fits(c6), Bool.and(ModelRoles.mrw_choice_fits(c7), Bool.and(ModelRoles.mrw_choice_fits(c8), Bool.and(ModelRoles.mrw_choice_fits(c9), Bool.and(ModelRoles.mrw_choice_fits(c10), Bool.and(ModelRoles.mrw_choice_fits(c11), ModelRoles.mrw_choice_fits(c12)))))))), f4, mf.and_t(ModelRoles.mrw_choice_fits(c5), Bool.and(ModelRoles.mrw_choice_fits(c6), Bool.and(ModelRoles.mrw_choice_fits(c7), Bool.and(ModelRoles.mrw_choice_fits(c8), Bool.and(ModelRoles.mrw_choice_fits(c9), Bool.and(ModelRoles.mrw_choice_fits(c10), Bool.and(ModelRoles.mrw_choice_fits(c11), ModelRoles.mrw_choice_fits(c12))))))), f5, mf.and_t(ModelRoles.mrw_choice_fits(c6), Bool.and(ModelRoles.mrw_choice_fits(c7), Bool.and(ModelRoles.mrw_choice_fits(c8), Bool.and(ModelRoles.mrw_choice_fits(c9), Bool.and(ModelRoles.mrw_choice_fits(c10), Bool.and(ModelRoles.mrw_choice_fits(c11), ModelRoles.mrw_choice_fits(c12)))))), f6, mf.and_t(ModelRoles.mrw_choice_fits(c7), Bool.and(ModelRoles.mrw_choice_fits(c8), Bool.and(ModelRoles.mrw_choice_fits(c9), Bool.and(ModelRoles.mrw_choice_fits(c10), Bool.and(ModelRoles.mrw_choice_fits(c11), ModelRoles.mrw_choice_fits(c12))))), f7, mf.and_t(ModelRoles.mrw_choice_fits(c8), Bool.and(ModelRoles.mrw_choice_fits(c9), Bool.and(ModelRoles.mrw_choice_fits(c10), Bool.and(ModelRoles.mrw_choice_fits(c11), ModelRoles.mrw_choice_fits(c12)))), f8, mf.and_t(ModelRoles.mrw_choice_fits(c9), Bool.and(ModelRoles.mrw_choice_fits(c10), Bool.and(ModelRoles.mrw_choice_fits(c11), ModelRoles.mrw_choice_fits(c12))), f9, mf.and_t(ModelRoles.mrw_choice_fits(c10), Bool.and(ModelRoles.mrw_choice_fits(c11), ModelRoles.mrw_choice_fits(c12)), f10, mf.and_t(ModelRoles.mrw_choice_fits(c11), ModelRoles.mrw_choice_fits(c12), f11, f12))))))))))))
    case Wr.Bad{}:
      LX.mx.bad_got(Mr.Owns, {ModelRoles.mrw_owns_fits(o) == True{} : Bool}, o, rest, h)

def mf.owns_11(d: Wr.Dec<Mr.Choice>, +s: String, +c0: Mr.Choice, +c1: Mr.Choice, +c2: Mr.Choice, +c3: Mr.Choice, +c4: Mr.Choice, +c5: Mr.Choice, +c6: Mr.Choice, +c7: Mr.Choice, +c8: Mr.Choice, +c9: Mr.Choice, +c10: Mr.Choice, +o: Mr.Owns, +rest: String, ed: {FMr.get_choice(s) == d : Wr.Dec<Mr.Choice>}, +h: {FMr.get_owns.speech(c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, d) == Wr.Got{o, rest} : Wr.Dec<Mr.Owns>}, f0: {ModelRoles.mrw_choice_fits(c0) == True{} : Bool}, f1: {ModelRoles.mrw_choice_fits(c1) == True{} : Bool}, f2: {ModelRoles.mrw_choice_fits(c2) == True{} : Bool}, f3: {ModelRoles.mrw_choice_fits(c3) == True{} : Bool}, f4: {ModelRoles.mrw_choice_fits(c4) == True{} : Bool}, f5: {ModelRoles.mrw_choice_fits(c5) == True{} : Bool}, f6: {ModelRoles.mrw_choice_fits(c6) == True{} : Bool}, f7: {ModelRoles.mrw_choice_fits(c7) == True{} : Bool}, f8: {ModelRoles.mrw_choice_fits(c8) == True{} : Bool}, f9: {ModelRoles.mrw_choice_fits(c9) == True{} : Bool}, f10: {ModelRoles.mrw_choice_fits(c10) == True{} : Bool}) -> {ModelRoles.mrw_owns_fits(o) == True{} : Bool}:
  match d:
    case Wr.Got{+c11, +s1}:
      f11 = mf.choice(s, c11, s1, ed)
      mf.owns_12(FMr.get_choice(s1), s1, c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, o, rest, {==}, h, f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11)
    case Wr.Bad{}:
      LX.mx.bad_got(Mr.Owns, {ModelRoles.mrw_owns_fits(o) == True{} : Bool}, o, rest, h)

def mf.owns_10(d: Wr.Dec<Mr.Choice>, +s: String, +c0: Mr.Choice, +c1: Mr.Choice, +c2: Mr.Choice, +c3: Mr.Choice, +c4: Mr.Choice, +c5: Mr.Choice, +c6: Mr.Choice, +c7: Mr.Choice, +c8: Mr.Choice, +c9: Mr.Choice, +o: Mr.Owns, +rest: String, ed: {FMr.get_choice(s) == d : Wr.Dec<Mr.Choice>}, +h: {FMr.get_owns.translate(c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, d) == Wr.Got{o, rest} : Wr.Dec<Mr.Owns>}, f0: {ModelRoles.mrw_choice_fits(c0) == True{} : Bool}, f1: {ModelRoles.mrw_choice_fits(c1) == True{} : Bool}, f2: {ModelRoles.mrw_choice_fits(c2) == True{} : Bool}, f3: {ModelRoles.mrw_choice_fits(c3) == True{} : Bool}, f4: {ModelRoles.mrw_choice_fits(c4) == True{} : Bool}, f5: {ModelRoles.mrw_choice_fits(c5) == True{} : Bool}, f6: {ModelRoles.mrw_choice_fits(c6) == True{} : Bool}, f7: {ModelRoles.mrw_choice_fits(c7) == True{} : Bool}, f8: {ModelRoles.mrw_choice_fits(c8) == True{} : Bool}, f9: {ModelRoles.mrw_choice_fits(c9) == True{} : Bool}) -> {ModelRoles.mrw_owns_fits(o) == True{} : Bool}:
  match d:
    case Wr.Got{+c10, +s1}:
      f10 = mf.choice(s, c10, s1, ed)
      mf.owns_11(FMr.get_choice(s1), s1, c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, o, rest, {==}, h, f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10)
    case Wr.Bad{}:
      LX.mx.bad_got(Mr.Owns, {ModelRoles.mrw_owns_fits(o) == True{} : Bool}, o, rest, h)

def mf.owns_9(d: Wr.Dec<Mr.Choice>, +s: String, +c0: Mr.Choice, +c1: Mr.Choice, +c2: Mr.Choice, +c3: Mr.Choice, +c4: Mr.Choice, +c5: Mr.Choice, +c6: Mr.Choice, +c7: Mr.Choice, +c8: Mr.Choice, +o: Mr.Owns, +rest: String, ed: {FMr.get_choice(s) == d : Wr.Dec<Mr.Choice>}, +h: {FMr.get_owns.judge(c0, c1, c2, c3, c4, c5, c6, c7, c8, d) == Wr.Got{o, rest} : Wr.Dec<Mr.Owns>}, f0: {ModelRoles.mrw_choice_fits(c0) == True{} : Bool}, f1: {ModelRoles.mrw_choice_fits(c1) == True{} : Bool}, f2: {ModelRoles.mrw_choice_fits(c2) == True{} : Bool}, f3: {ModelRoles.mrw_choice_fits(c3) == True{} : Bool}, f4: {ModelRoles.mrw_choice_fits(c4) == True{} : Bool}, f5: {ModelRoles.mrw_choice_fits(c5) == True{} : Bool}, f6: {ModelRoles.mrw_choice_fits(c6) == True{} : Bool}, f7: {ModelRoles.mrw_choice_fits(c7) == True{} : Bool}, f8: {ModelRoles.mrw_choice_fits(c8) == True{} : Bool}) -> {ModelRoles.mrw_owns_fits(o) == True{} : Bool}:
  match d:
    case Wr.Got{+c9, +s1}:
      f9 = mf.choice(s, c9, s1, ed)
      mf.owns_10(FMr.get_choice(s1), s1, c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, o, rest, {==}, h, f0, f1, f2, f3, f4, f5, f6, f7, f8, f9)
    case Wr.Bad{}:
      LX.mx.bad_got(Mr.Owns, {ModelRoles.mrw_owns_fits(o) == True{} : Bool}, o, rest, h)

def mf.owns_8(d: Wr.Dec<Mr.Choice>, +s: String, +c0: Mr.Choice, +c1: Mr.Choice, +c2: Mr.Choice, +c3: Mr.Choice, +c4: Mr.Choice, +c5: Mr.Choice, +c6: Mr.Choice, +c7: Mr.Choice, +o: Mr.Owns, +rest: String, ed: {FMr.get_choice(s) == d : Wr.Dec<Mr.Choice>}, +h: {FMr.get_owns.titles(c0, c1, c2, c3, c4, c5, c6, c7, d) == Wr.Got{o, rest} : Wr.Dec<Mr.Owns>}, f0: {ModelRoles.mrw_choice_fits(c0) == True{} : Bool}, f1: {ModelRoles.mrw_choice_fits(c1) == True{} : Bool}, f2: {ModelRoles.mrw_choice_fits(c2) == True{} : Bool}, f3: {ModelRoles.mrw_choice_fits(c3) == True{} : Bool}, f4: {ModelRoles.mrw_choice_fits(c4) == True{} : Bool}, f5: {ModelRoles.mrw_choice_fits(c5) == True{} : Bool}, f6: {ModelRoles.mrw_choice_fits(c6) == True{} : Bool}, f7: {ModelRoles.mrw_choice_fits(c7) == True{} : Bool}) -> {ModelRoles.mrw_owns_fits(o) == True{} : Bool}:
  match d:
    case Wr.Got{+c8, +s1}:
      f8 = mf.choice(s, c8, s1, ed)
      mf.owns_9(FMr.get_choice(s1), s1, c0, c1, c2, c3, c4, c5, c6, c7, c8, o, rest, {==}, h, f0, f1, f2, f3, f4, f5, f6, f7, f8)
    case Wr.Bad{}:
      LX.mx.bad_got(Mr.Owns, {ModelRoles.mrw_owns_fits(o) == True{} : Bool}, o, rest, h)

def mf.owns_7(d: Wr.Dec<Mr.Choice>, +s: String, +c0: Mr.Choice, +c1: Mr.Choice, +c2: Mr.Choice, +c3: Mr.Choice, +c4: Mr.Choice, +c5: Mr.Choice, +c6: Mr.Choice, +o: Mr.Owns, +rest: String, ed: {FMr.get_choice(s) == d : Wr.Dec<Mr.Choice>}, +h: {FMr.get_owns.query(c0, c1, c2, c3, c4, c5, c6, d) == Wr.Got{o, rest} : Wr.Dec<Mr.Owns>}, f0: {ModelRoles.mrw_choice_fits(c0) == True{} : Bool}, f1: {ModelRoles.mrw_choice_fits(c1) == True{} : Bool}, f2: {ModelRoles.mrw_choice_fits(c2) == True{} : Bool}, f3: {ModelRoles.mrw_choice_fits(c3) == True{} : Bool}, f4: {ModelRoles.mrw_choice_fits(c4) == True{} : Bool}, f5: {ModelRoles.mrw_choice_fits(c5) == True{} : Bool}, f6: {ModelRoles.mrw_choice_fits(c6) == True{} : Bool}) -> {ModelRoles.mrw_owns_fits(o) == True{} : Bool}:
  match d:
    case Wr.Got{+c7, +s1}:
      f7 = mf.choice(s, c7, s1, ed)
      mf.owns_8(FMr.get_choice(s1), s1, c0, c1, c2, c3, c4, c5, c6, c7, o, rest, {==}, h, f0, f1, f2, f3, f4, f5, f6, f7)
    case Wr.Bad{}:
      LX.mx.bad_got(Mr.Owns, {ModelRoles.mrw_owns_fits(o) == True{} : Bool}, o, rest, h)

def mf.owns_6(d: Wr.Dec<Mr.Choice>, +s: String, +c0: Mr.Choice, +c1: Mr.Choice, +c2: Mr.Choice, +c3: Mr.Choice, +c4: Mr.Choice, +c5: Mr.Choice, +o: Mr.Owns, +rest: String, ed: {FMr.get_choice(s) == d : Wr.Dec<Mr.Choice>}, +h: {FMr.get_owns.gateway(c0, c1, c2, c3, c4, c5, d) == Wr.Got{o, rest} : Wr.Dec<Mr.Owns>}, f0: {ModelRoles.mrw_choice_fits(c0) == True{} : Bool}, f1: {ModelRoles.mrw_choice_fits(c1) == True{} : Bool}, f2: {ModelRoles.mrw_choice_fits(c2) == True{} : Bool}, f3: {ModelRoles.mrw_choice_fits(c3) == True{} : Bool}, f4: {ModelRoles.mrw_choice_fits(c4) == True{} : Bool}, f5: {ModelRoles.mrw_choice_fits(c5) == True{} : Bool}) -> {ModelRoles.mrw_owns_fits(o) == True{} : Bool}:
  match d:
    case Wr.Got{+c6, +s1}:
      f6 = mf.choice(s, c6, s1, ed)
      mf.owns_7(FMr.get_choice(s1), s1, c0, c1, c2, c3, c4, c5, c6, o, rest, {==}, h, f0, f1, f2, f3, f4, f5, f6)
    case Wr.Bad{}:
      LX.mx.bad_got(Mr.Owns, {ModelRoles.mrw_owns_fits(o) == True{} : Bool}, o, rest, h)

def mf.owns_5(d: Wr.Dec<Mr.Choice>, +s: String, +c0: Mr.Choice, +c1: Mr.Choice, +c2: Mr.Choice, +c3: Mr.Choice, +c4: Mr.Choice, +o: Mr.Owns, +rest: String, ed: {FMr.get_choice(s) == d : Wr.Dec<Mr.Choice>}, +h: {FMr.get_owns.worker(c0, c1, c2, c3, c4, d) == Wr.Got{o, rest} : Wr.Dec<Mr.Owns>}, f0: {ModelRoles.mrw_choice_fits(c0) == True{} : Bool}, f1: {ModelRoles.mrw_choice_fits(c1) == True{} : Bool}, f2: {ModelRoles.mrw_choice_fits(c2) == True{} : Bool}, f3: {ModelRoles.mrw_choice_fits(c3) == True{} : Bool}, f4: {ModelRoles.mrw_choice_fits(c4) == True{} : Bool}) -> {ModelRoles.mrw_owns_fits(o) == True{} : Bool}:
  match d:
    case Wr.Got{+c5, +s1}:
      f5 = mf.choice(s, c5, s1, ed)
      mf.owns_6(FMr.get_choice(s1), s1, c0, c1, c2, c3, c4, c5, o, rest, {==}, h, f0, f1, f2, f3, f4, f5)
    case Wr.Bad{}:
      LX.mx.bad_got(Mr.Owns, {ModelRoles.mrw_owns_fits(o) == True{} : Bool}, o, rest, h)

def mf.owns_4(d: Wr.Dec<Mr.Choice>, +s: String, +c0: Mr.Choice, +c1: Mr.Choice, +c2: Mr.Choice, +c3: Mr.Choice, +o: Mr.Owns, +rest: String, ed: {FMr.get_choice(s) == d : Wr.Dec<Mr.Choice>}, +h: {FMr.get_owns.subagent(c0, c1, c2, c3, d) == Wr.Got{o, rest} : Wr.Dec<Mr.Owns>}, f0: {ModelRoles.mrw_choice_fits(c0) == True{} : Bool}, f1: {ModelRoles.mrw_choice_fits(c1) == True{} : Bool}, f2: {ModelRoles.mrw_choice_fits(c2) == True{} : Bool}, f3: {ModelRoles.mrw_choice_fits(c3) == True{} : Bool}) -> {ModelRoles.mrw_owns_fits(o) == True{} : Bool}:
  match d:
    case Wr.Got{+c4, +s1}:
      f4 = mf.choice(s, c4, s1, ed)
      mf.owns_5(FMr.get_choice(s1), s1, c0, c1, c2, c3, c4, o, rest, {==}, h, f0, f1, f2, f3, f4)
    case Wr.Bad{}:
      LX.mx.bad_got(Mr.Owns, {ModelRoles.mrw_owns_fits(o) == True{} : Bool}, o, rest, h)

def mf.owns_3(d: Wr.Dec<Mr.Choice>, +s: String, +c0: Mr.Choice, +c1: Mr.Choice, +c2: Mr.Choice, +o: Mr.Owns, +rest: String, ed: {FMr.get_choice(s) == d : Wr.Dec<Mr.Choice>}, +h: {FMr.get_owns.image(c0, c1, c2, d) == Wr.Got{o, rest} : Wr.Dec<Mr.Owns>}, f0: {ModelRoles.mrw_choice_fits(c0) == True{} : Bool}, f1: {ModelRoles.mrw_choice_fits(c1) == True{} : Bool}, f2: {ModelRoles.mrw_choice_fits(c2) == True{} : Bool}) -> {ModelRoles.mrw_owns_fits(o) == True{} : Bool}:
  match d:
    case Wr.Got{+c3, +s1}:
      f3 = mf.choice(s, c3, s1, ed)
      mf.owns_4(FMr.get_choice(s1), s1, c0, c1, c2, c3, o, rest, {==}, h, f0, f1, f2, f3)
    case Wr.Bad{}:
      LX.mx.bad_got(Mr.Owns, {ModelRoles.mrw_owns_fits(o) == True{} : Bool}, o, rest, h)

def mf.owns_2(d: Wr.Dec<Mr.Choice>, +s: String, +c0: Mr.Choice, +c1: Mr.Choice, +o: Mr.Owns, +rest: String, ed: {FMr.get_choice(s) == d : Wr.Dec<Mr.Choice>}, +h: {FMr.get_owns.auxiliary(c0, c1, d) == Wr.Got{o, rest} : Wr.Dec<Mr.Owns>}, f0: {ModelRoles.mrw_choice_fits(c0) == True{} : Bool}, f1: {ModelRoles.mrw_choice_fits(c1) == True{} : Bool}) -> {ModelRoles.mrw_owns_fits(o) == True{} : Bool}:
  match d:
    case Wr.Got{+c2, +s1}:
      f2 = mf.choice(s, c2, s1, ed)
      mf.owns_3(FMr.get_choice(s1), s1, c0, c1, c2, o, rest, {==}, h, f0, f1, f2)
    case Wr.Bad{}:
      LX.mx.bad_got(Mr.Owns, {ModelRoles.mrw_owns_fits(o) == True{} : Bool}, o, rest, h)

def mf.owns_1(d: Wr.Dec<Mr.Choice>, +s: String, +c0: Mr.Choice, +o: Mr.Owns, +rest: String, ed: {FMr.get_choice(s) == d : Wr.Dec<Mr.Choice>}, +h: {FMr.get_owns.memory(c0, d) == Wr.Got{o, rest} : Wr.Dec<Mr.Owns>}, f0: {ModelRoles.mrw_choice_fits(c0) == True{} : Bool}) -> {ModelRoles.mrw_owns_fits(o) == True{} : Bool}:
  match d:
    case Wr.Got{+c1, +s1}:
      f1 = mf.choice(s, c1, s1, ed)
      mf.owns_2(FMr.get_choice(s1), s1, c0, c1, o, rest, {==}, h, f0, f1)
    case Wr.Bad{}:
      LX.mx.bad_got(Mr.Owns, {ModelRoles.mrw_owns_fits(o) == True{} : Bool}, o, rest, h)

def mf.owns_0(d: Wr.Dec<Mr.Choice>, +s: String, +o: Mr.Owns, +rest: String, ed: {FMr.get_choice(s) == d : Wr.Dec<Mr.Choice>}, +h: {FMr.get_owns.chat(d) == Wr.Got{o, rest} : Wr.Dec<Mr.Owns>}) -> {ModelRoles.mrw_owns_fits(o) == True{} : Bool}:
  match d:
    case Wr.Got{+c0, +s1}:
      f0 = mf.choice(s, c0, s1, ed)
      mf.owns_1(FMr.get_choice(s1), s1, c0, o, rest, {==}, h, f0)
    case Wr.Bad{}:
      LX.mx.bad_got(Mr.Owns, {ModelRoles.mrw_owns_fits(o) == True{} : Bool}, o, rest, h)

# decoded own settings fit the wire
def mf.owns(+s: String, +o: Mr.Owns, +rest: String, h: {FMr.get_owns(s) == Wr.Got{o, rest} : Wr.Dec<Mr.Owns>}) -> {ModelRoles.mrw_owns_fits(o) == True{} : Bool}:
  mf.owns_0(FMr.get_choice(s), s, o, rest, {==}, h)

# The request
# -----------

def mf.in_all(d: Wr.Dec<Mr.Choice>, +s1: String, +ow: Mr.Owns, +x: Mr.In, +rest: String, ed: {FMr.get_choice(s1) == d : Wr.Dec<Mr.Choice>}, +h: {FMr.get_in.all(ow, d) == Wr.Got{x, rest} : Wr.Dec<Mr.In>}, fo: {ModelRoles.mrw_owns_fits(ow) == True{} : Bool}) -> {ModelRoles.mrw_in_fits(x) == True{} : Bool}:
  match d:
    case Wr.Got{+al, +s2}:
      fa = mf.choice(s1, al, s2, ed)
      %LX.mx.got_v(Mr.In, Mr.In{ow, al}, x, s2, rest, h) : {ModelRoles.mrw_in_fits(_) == True{} : Bool}
      mf.and_t(ModelRoles.mrw_owns_fits(ow), ModelRoles.mrw_choice_fits(al), fo, fa)
    case Wr.Bad{}:
      LX.mx.bad_got(Mr.In, {ModelRoles.mrw_in_fits(x) == True{} : Bool}, x, rest, h)

def mf.in_go(d: Wr.Dec<Mr.Owns>, +s: String, +x: Mr.In, +rest: String, ed: {FMr.get_owns(s) == d : Wr.Dec<Mr.Owns>}, +h: {FMr.get_in.go(d) == Wr.Got{x, rest} : Wr.Dec<Mr.In>}) -> {ModelRoles.mrw_in_fits(x) == True{} : Bool}:
  match d:
    case Wr.Got{+ow, +s1}:
      mf.in_all(FMr.get_choice(s1), s1, ow, x, rest, {==}, h, mf.owns(s, ow, s1, ed))
    case Wr.Bad{}:
      LX.mx.bad_got(Mr.In, {ModelRoles.mrw_in_fits(x) == True{} : Bool}, x, rest, h)

# a decoded request fits the wire
def mf.in(+s: String, +x: Mr.In, +rest: String, h: {FMr.get_in(s) == Wr.Got{x, rest} : Wr.Dec<Mr.In>}) -> {ModelRoles.mrw_in_fits(x) == True{} : Bool}:
  mf.in_go(FMr.get_owns(s), s, x, rest, {==}, h)
