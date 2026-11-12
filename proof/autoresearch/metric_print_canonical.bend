# eukhe: the proof of LAW metric_print_canonical: per printer case (zero,
# no point, the point among the digits, `0.` and zeros first), the value
# parts the text spells, that they are canonical, and that they are worth
# the decimal

import Base
import ../../bend/autoresearch/dec.bend as ArD
import ../../bend/autoresearch/line.bend as ArL
import ../../spec/autoresearch/decimal.bend as SD
import ../../spec/autoresearch/metric_line.bend as SL
import ../../laws/autoresearch/model.bend as Autoresearch
import ./base/dec.bend as AdDec
import ./base/line.bend as AL
import ./metric_print_round_trip/print.bend as AdPrint

# the text s spells canonical value parts worth d
def mpc.H(s: String, +d: ArD.Dec) -> Type:
  &p: ArL.Parts -> {s == Autoresearch.ar_value_text(p) : String} & {Autoresearch.ar_canon_parts(p) == True{} : Bool} & {SD.same(d, SL.raw(p)) == True{} : Bool}

# Lists
# -----

def mpc.app_cat(xs: List<&2, Nat>, -ys: List<&2, Nat>) -> {List.append(&2, Nat, xs, ys) == ArD.cat(xs, ys) : List<&2, Nat>}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +t:
      Equal.cong(List<&2, Nat>, List<&2, Nat>, l => x <> l, List.append(&2, Nat, t, ys), ArD.cat(t, ys), mpc.app_cat(t, ys))

def mpc.ne_any(xs: List<&2, Nat>, h: {ArL.any_d(xs) == True{} : Bool}) -> {SL.nonempty_ds(xs) == True{} : Bool}:
  match xs:
    case Nil{}:
      AdDec.ad.absurd({SL.nonempty_ds(Nil{}) == True{} : Bool}, h)
    case x <> t:
      {==}

# zeros, then a digit that is not 0: some digit is not 0
def mpc.nz_zeros(z: Nat, +j: Nat, +t: List<&2, Nat>) -> {Autoresearch.ar_some_nz(ArD.cat(ArD.zeros(z), (1n+j) <> t)) == True{} : Bool}:
  match z:
    case 0n:
      {==}
    case 1n+w:
      mpc.nz_zeros(w, j, t)

# leading zeros are worth nothing
def mpc.num_zeros(z: Nat, -ds: List<&2, Nat>) -> {SD.num.go(ArD.cat(ArD.zeros(z), ds), 0n) == SD.num.go(ds, 0n) : Nat}:
  match z:
    case 0n:
      {==}
    case 1n+w:
      mpc.num_zeros(w, ds)

# Worth
# -----

# the same digits' worth at one scale and sign: the same value
def mpc.same_by(neg: Bool, +a: List<&2, Nat>, +b: List<&2, Nat>, +s: Nat, en: {SD.num(a) == SD.num(b) : Nat}) -> {SD.same(ArD.Dec{neg, a, s}, ArD.Dec{neg, b, s}) == True{} : Bool}:
  match neg:
    case True{}:
      +x = SD.shift(s, SD.num(a))
      %en : {Cmp.is_eq(Nat.cmp(SD.shift(s, _), x)) == True{} : Bool}
      %Equal.sym(Cmp, Nat.cmp(x, x), EQ{}, AdDec.ad.nat_cmp_refl(x)) : {Cmp.is_eq(_) == True{} : Bool}
      {==}
    case False{}:
      +x = SD.shift(s, SD.num(a))
      %en : {Cmp.is_eq(Nat.cmp(x, SD.shift(s, _))) == True{} : Bool}
      %Equal.sym(Cmp, Nat.cmp(x, x), EQ{}, AdDec.ad.nat_cmp_refl(x)) : {Cmp.is_eq(_) == True{} : Bool}
      {==}

def mpc.same_num(neg: Bool, +a: List<&2, Nat>, +b: List<&2, Nat>, +s: Nat, -s2: Nat, en: {SD.num(a) == SD.num(b) : Nat}, es: {s2 == s : Nat}) -> {SD.same(ArD.Dec{neg, a, s}, ArD.Dec{neg, b, s2}) == True{} : Bool}:
  %Equal.sym(Nat, s2, s, es) : {SD.same(ArD.Dec{neg, a, s}, ArD.Dec{neg, b, _}) == True{} : Bool}
  mpc.same_by(neg, a, b, s, en)

# Text
# ----

def mpc.sign(neg: Bool, -s: String) -> {ArD.show.sign(neg, s) == SL.spell_sign(neg, s) : String}:
  match neg:
    case True{}:
      {==}
    case False{}:
      {==}

def mpc.sp(+neg: Bool, +ds: List<&2, Nat>, +r: String) -> {ArD.show.sign(neg, ArD.put_ds(ds, r)) == SL.spell_sign(neg, SL.spell_ds(ds, r)) : String}:
  %AL.al.put_spell(ds, r) : {ArD.show.sign(neg, ArD.put_ds(ds, r)) == SL.spell_sign(neg, _) : String}
  mpc.sign(neg, ArD.put_ds(ds, r))

# the point among the digits
def mpc.e_more(+neg: Bool, +j: Nat, +t: List<&2, Nat>, +q: Nat, +hm: {Nat.is_lt(q, ArD.len(t)) == True{} : Bool}) -> {ArD.show.sign(neg, ArD.show.mag(True{}, (1n+j) <> t, 1n+ArD.len(t), 1n+q)) == SL.spell_sign(neg, SL.spell_ds((1n+j) <> AdPrint.ad.take(Nat.sub(ArD.len(t), 1n+q), t), SCon{'.', SL.spell_ds(AdPrint.ad.skip(Nat.sub(ArD.len(t), 1n+q), t), "")})) : String}:
  +h = {1n+j : Nat}
  +k = Nat.sub(ArD.len(t), 1n+q)
  +i = {h <> AdPrint.ad.take(k, t) : List<&2, Nat>}
  +f = AdPrint.ad.skip(k, t)
  %Equal.sym(Nat, Nat.sub(ArD.len(t), q), 1n+k, AdPrint.ad.lt_sub(q, ArD.len(t), hm)) : {ArD.show.sign(neg, ArD.show.parts(ArD.split(_, h <> t))) == SL.spell_sign(neg, SL.spell_ds(i, SCon{'.', SL.spell_ds(f, "")})) : String}
  %AdPrint.ad.split_eq(k, t) : {ArD.show.sign(neg, ArD.show.parts(ArD.split.on(h, _))) == SL.spell_sign(neg, SL.spell_ds(i, SCon{'.', SL.spell_ds(f, "")})) : String}
  %AL.al.put_spell(f, "") : {ArD.show.sign(neg, ArD.put_ds(i, SCon{'.', ArD.put_ds(f, "")})) == SL.spell_sign(neg, SL.spell_ds(i, SCon{'.', _})) : String}
  mpc.sp(neg, i, SCon{'.', ArD.put_ds(f, "")})

# `0.`, zeros, then the digits
def mpc.e_less(+neg: Bool, +z: Nat, +ds: List<&2, Nat>) -> {ArD.show.sign(neg, SCon{'0', SCon{'.', ArD.put_ds(ArD.zeros(z), ArD.put_ds(ds, ""))}}) == SL.spell_sign(neg, SL.spell_ds([0n], SCon{'.', SL.spell_ds(ArD.cat(ArD.zeros(z), ds), "")})) : String}:
  %AdPrint.ad.put_cat(ArD.zeros(z), ds, "") : {ArD.show.sign(neg, SCon{'0', SCon{'.', _}}) == SL.spell_sign(neg, SL.spell_ds([0n], SCon{'.', SL.spell_ds(ArD.cat(ArD.zeros(z), ds), "")})) : String}
  %AL.al.put_spell(ArD.cat(ArD.zeros(z), ds), "") : {ArD.show.sign(neg, SCon{'0', SCon{'.', ArD.put_ds(ArD.cat(ArD.zeros(z), ds), "")}}) == SL.spell_sign(neg, SL.spell_ds([0n], SCon{'.', _})) : String}
  mpc.sign(neg, SCon{'0', SCon{'.', ArD.put_ds(ArD.cat(ArD.zeros(z), ds), "")}})

# Canonical parts
# ---------------

def mpc.canon.at(+D: Bool, +frac: Maybe<&2, List<&2, Nat>>, di: {D == True{} : Bool}, fo: {SL.frac_ok(frac) == True{} : Bool}, fc: {Autoresearch.ar_frac_canon(frac) == True{} : Bool}) -> {Bool.and(D, Bool.and(SL.frac_ok(frac), Bool.and(Autoresearch.ar_frac_canon(frac), True{}))) == True{} : Bool}:
  AdDec.ad.and_intro(D, Bool.and(SL.frac_ok(frac), Bool.and(Autoresearch.ar_frac_canon(frac), True{})), di, AdDec.ad.and_intro(SL.frac_ok(frac), Bool.and(Autoresearch.ar_frac_canon(frac), True{}), fo, AdDec.ad.and_intro(Autoresearch.ar_frac_canon(frac), True{}, fc, {==})))

# an integer part led by a digit that is not 0
def mpc.canon(neg: Bool, +j: Nat, +it: List<&2, Nat>, +frac: Maybe<&2, List<&2, Nat>>, di: {SD.digits_ok((1n+j) <> it) == True{} : Bool}, fo: {SL.frac_ok(frac) == True{} : Bool}, fc: {Autoresearch.ar_frac_canon(frac) == True{} : Bool}) -> {Autoresearch.ar_canon_parts(ArL.Parts{" ", "m", neg, (1n+j) <> it, frac, ""}) == True{} : Bool}:
  match neg:
    case True{}:
      mpc.canon.at(SD.digits_ok((1n+j) <> it), frac, di, fo, fc)
    case False{}:
      mpc.canon.at(SD.digits_ok((1n+j) <> it), frac, di, fo, fc)

# the integer part 0, then a fraction f
def mpc.canon0(neg: Bool, +f: List<&2, Nat>, ne: {SL.nonempty_ds(f) == True{} : Bool}, dk: {SD.digits_ok(f) == True{} : Bool}, ln: {SD.last_nz(f) == True{} : Bool}, nz: {Autoresearch.ar_some_nz(f) == True{} : Bool}) -> {Autoresearch.ar_canon_parts(ArL.Parts{" ", "m", neg, [0n], Some{f}, ""}) == True{} : Bool}:
  match neg:
    case True{}:
      AdDec.ad.and_intro(Bool.and(SL.nonempty_ds(f), SD.digits_ok(f)), Bool.and(SD.last_nz(f), Autoresearch.ar_some_nz(f)), AdDec.ad.and_intro(SL.nonempty_ds(f), SD.digits_ok(f), ne, dk), AdDec.ad.and_intro(SD.last_nz(f), Autoresearch.ar_some_nz(f), ln, nz))
    case False{}:
      AdDec.ad.and_intro(Bool.and(SL.nonempty_ds(f), SD.digits_ok(f)), Bool.and(SD.last_nz(f), True{}), AdDec.ad.and_intro(SL.nonempty_ds(f), SD.digits_ok(f), ne, dk), AdDec.ad.and_intro(SD.last_nz(f), True{}, ln, {==}))

# The cases
# ---------

# no point: the digits are the integer part
def mpc.int(+neg: Bool, h: Nat, +t: List<&2, Nat>, hz: {Nat.is_ne(h, 0n) == True{} : Bool}, +dok: {SD.digits_ok(h <> t) == True{} : Bool}) -> mpc.H(ArD.show(ArD.Dec{neg, h <> t, 0n}), ArD.Dec{neg, h <> t, 0n}):
  match h:
    case 0n:
      AdDec.ad.absurd(mpc.H(ArD.show(ArD.Dec{neg, 0n <> t, 0n}), ArD.Dec{neg, 0n <> t, 0n}), hz)
    case 1n++j:
      +ds = {(1n+j) <> t : List<&2, Nat>}
      +ea = Equal.trans(List<&2, Nat>, List.append(&2, Nat, ds, Nil{}), ArD.cat(ds, Nil{}), ds, mpc.app_cat(ds, Nil{}), AdPrint.ad.cat_nil(ds))
      (ArL.Parts{" ", "m", neg, ds, None{}, ""}, mpc.sp(neg, ds, ""), mpc.canon(neg, j, t, None{}, dok, {==}, {==}), mpc.same_num(neg, ds, List.append(&2, Nat, ds, Nil{}), 0n, 0n, Equal.cong(List<&2, Nat>, Nat, l => SD.num(l), ds, List.append(&2, Nat, ds, Nil{}), Equal.sym(List<&2, Nat>, List.append(&2, Nat, ds, Nil{}), ds, ea)), {==}))

# more digits than the scale: the point among them
def mpc.more(+neg: Bool, +j: Nat, +t: List<&2, Nat>, +q: Nat, +hm: {Nat.is_lt(q, ArD.len(t)) == True{} : Bool}, +dok: {SD.digits_ok((1n+j) <> t) == True{} : Bool}, lt: {SD.last_nz((1n+j) <> t) == True{} : Bool}) -> mpc.H(ArD.show.sign(neg, ArD.show.mag(True{}, (1n+j) <> t, 1n+ArD.len(t), 1n+q)), ArD.Dec{neg, (1n+j) <> t, 1n+q}):
  +h = {1n+j : Nat}
  +k = Nat.sub(ArD.len(t), 1n+q)
  +i = {h <> AdPrint.ad.take(k, t) : List<&2, Nat>}
  +f = AdPrint.ad.skip(k, t)
  +hh = AdDec.ad.and_l(Nat.is_lt(h, 10n), SD.digits_ok(t), dok)
  +dt = AdDec.ad.and_r(Nat.is_lt(h, 10n), SD.digits_ok(t), dok)
  +el = Equal.trans(Nat, ArD.len(f), Nat.sub(ArD.len(t), k), 1n+q, AdPrint.ad.len_skip(k, t), AdPrint.ad.sub_sub(ArD.len(t), 1n+q, AdPrint.ad.lt_succ_le(q, ArD.len(t), hm)))
  +af = Equal.trans(Bool, ArL.any_d(f), Nat.is_lt(0n, ArD.len(f)), True{}, AdPrint.ad.any_len(f), Equal.cong(Nat, Bool, n => Nat.is_lt(0n, n), ArD.len(f), 1n+q, el))
  +ect = AdPrint.ad.cat_take_skip(k, t)
  +lf = Equal.trans(Bool, SD.last_nz(f), SD.last_nz(h <> ArD.cat(AdPrint.ad.take(k, t), f)), True{},
    Equal.sym(Bool, SD.last_nz(ArD.cat(i, f)), SD.last_nz(f), AdPrint.ad.last_cat(i, f, af)),
    Equal.trans(Bool, SD.last_nz(h <> ArD.cat(AdPrint.ad.take(k, t), f)), SD.last_nz(h <> t), True{},
      Equal.cong(List<&2, Nat>, Bool, l => SD.last_nz(h <> l), ArD.cat(AdPrint.ad.take(k, t), f), t, ect),
      lt))
  +di = AdDec.ad.and_intro(Nat.is_lt(h, 10n), SD.digits_ok(AdPrint.ad.take(k, t)), hh, AdPrint.ad.digits_take(k, t, dt))
  +fo = AdDec.ad.and_intro(SL.nonempty_ds(f), SD.digits_ok(f), mpc.ne_any(f, af), AdPrint.ad.digits_skip(k, t, dt))
  +ea = Equal.trans(List<&2, Nat>, List.append(&2, Nat, i, f), ArD.cat(i, f), h <> t, mpc.app_cat(i, f), Equal.cong(List<&2, Nat>, List<&2, Nat>, l => h <> l, ArD.cat(AdPrint.ad.take(k, t), f), t, ect))
  +eL = Equal.trans(Nat, SL.dlen(f), ArD.len(f), 1n+q, AdPrint.ad.dlen_len(f), el)
  +en = Equal.cong(List<&2, Nat>, Nat, l => SD.num(l), h <> t, List.append(&2, Nat, i, f), Equal.sym(List<&2, Nat>, List.append(&2, Nat, i, f), h <> t, ea))
  (ArL.Parts{" ", "m", neg, i, Some{f}, ""}, mpc.e_more(neg, j, t, q, hm), mpc.canon(neg, j, AdPrint.ad.take(k, t), Some{f}, di, fo, lf), mpc.same_num(neg, h <> t, List.append(&2, Nat, i, f), 1n+q, SL.dlen(f), en, eL))

# no more digits than the scale: `0.`, zeros, then the digits
def mpc.less(+neg: Bool, +j: Nat, +t: List<&2, Nat>, +q: Nat, hm: {Nat.is_lt(q, ArD.len(t)) == False{} : Bool}, +dok: {SD.digits_ok((1n+j) <> t) == True{} : Bool}, lt: {SD.last_nz((1n+j) <> t) == True{} : Bool}) -> mpc.H(ArD.show.sign(neg, ArD.show.mag(False{}, (1n+j) <> t, 1n+ArD.len(t), 1n+q)), ArD.Dec{neg, (1n+j) <> t, 1n+q}):
  +h = {1n+j : Nat}
  +z = Nat.sub(q, ArD.len(t))
  +f = ArD.cat(ArD.zeros(z), h <> t)
  +af = AdPrint.ad.any_cat(ArD.zeros(z), h <> t, {==})
  +lf = Equal.trans(Bool, SD.last_nz(f), SD.last_nz(h <> t), True{}, AdPrint.ad.last_cat(ArD.zeros(z), h <> t, {==}), lt)
  +df = AdDec.ad.digits_cat(ArD.zeros(z), h <> t, AdDec.ad.digits_zeros(z), dok)
  +eL = Equal.trans(Nat, SL.dlen(f), ArD.len(f), 1n+q, AdPrint.ad.dlen_len(f),
    Equal.trans(Nat, ArD.len(f), Nat.add(z, ArD.len(h <> t)), 1n+q,
      AdDec.ad.len_pad(z, h <> t),
      AdPrint.ad.le_split(1n+q, 1n+ArD.len(t), AdPrint.ad.not_lt_le(q, ArD.len(t), hm))))
  +en = Equal.sym(Nat, SD.num.go(f, 0n), SD.num.go(h <> t, 0n), mpc.num_zeros(z, h <> t))
  (ArL.Parts{" ", "m", neg, [0n], Some{f}, ""}, mpc.e_less(neg, z, h <> t), mpc.canon0(neg, f, mpc.ne_any(f, af), df, lf, mpc.nz_zeros(z, j, t)), mpc.same_num(neg, h <> t, List.append(&2, Nat, [0n], f), 1n+q, SL.dlen(f), en, eL))

def mpc.mag(+neg: Bool, h: Nat, +t: List<&2, Nat>, +q: Nat, more: Bool, hm: {Nat.is_lt(q, ArD.len(t)) == more : Bool}, hz: {Nat.is_ne(h, 0n) == True{} : Bool}, dok: {SD.digits_ok(h <> t) == True{} : Bool}, lt: {SD.last_nz(h <> t) == True{} : Bool}) -> mpc.H(ArD.show.sign(neg, ArD.show.mag(more, h <> t, 1n+ArD.len(t), 1n+q)), ArD.Dec{neg, h <> t, 1n+q}):
  match h:
    case 0n:
      AdDec.ad.absurd(mpc.H(ArD.show.sign(neg, ArD.show.mag(more, 0n <> t, 1n+ArD.len(t), 1n+q)), ArD.Dec{neg, 0n <> t, 1n+q}), hz)
    case 1n++j:
      match more:
        case True{}:
          mpc.more(neg, j, t, q, hm, dok, lt)
        case False{}:
          mpc.less(neg, j, t, q, hm, dok, lt)

def mpc.value(ds: List<&2, Nat>, neg: Bool, +scale: Nat, +c: {SD.canon.ds(neg, ds, scale) == True{} : Bool}) -> mpc.H(ArD.show(ArD.Dec{neg, ds, scale}), ArD.Dec{neg, ds, scale}):
  match ds:
    case Nil{}:
      match neg:
        case True{}:
          AdDec.ad.absurd(mpc.H("0", ArD.Dec{True{}, Nil{}, scale}), c)
        case False{}:
          match scale:
            case 0n:
              (ArL.Parts{" ", "m", False{}, [0n], None{}, ""}, {==}, {==}, {==})
            case 1n+q:
              AdDec.ad.absurd(mpc.H("0", ArD.Dec{False{}, Nil{}, 1n+q}), c)
    case +h <> +t:
      match scale:
        case 0n:
          +rest = AdDec.ad.and_r(Nat.is_ne(h, 0n), Bool.and(SD.digits_ok(h <> t), True{}), c)
          mpc.int(neg, h, t, AdDec.ad.and_l(Nat.is_ne(h, 0n), Bool.and(SD.digits_ok(h <> t), True{}), c), AdDec.ad.and_l(SD.digits_ok(h <> t), True{}, rest))
        case 1n+q:
          +rest = AdDec.ad.and_r(Nat.is_ne(h, 0n), Bool.and(SD.digits_ok(h <> t), SD.last_nz(h <> t)), c)
          mpc.mag(neg, h, t, q, Nat.is_lt(q, ArD.len(t)), {==}, AdDec.ad.and_l(Nat.is_ne(h, 0n), Bool.and(SD.digits_ok(h <> t), SD.last_nz(h <> t)), c), AdDec.ad.and_l(SD.digits_ok(h <> t), SD.last_nz(h <> t), rest), AdDec.ad.and_r(SD.digits_ok(h <> t), SD.last_nz(h <> t), rest))

def Autoresearch.metric_print_canonical(d, c):
  match d:
    case ArD.Dec{+neg, +ds, +scale}:
      mpc.value(ds, neg, scale, c)
