# eukhe: lemmas of LAW metric_print_round_trip: the parser on a printed
# metric line

import Base
import ../../../bend/autoresearch/dec.bend as ArD
import ../../../bend/autoresearch/line.bend as ArL
import ../../../spec/autoresearch/decimal.bend as SD
import ../../../spec/autoresearch/metric_line.bend as SL
import ../base/dec.bend as AdDec
import ../base/line.bend as AL
import ./print.bend as AdPrint

# Spans
# -----

# the printed digits read back, up to a char that is no digit
def ad.span_put(+ds: List<&2, Nat>, +rest: String, ok: {SD.digits_ok(ds) == True{} : Bool}, stop: {ArL.span_d(rest) == (Nil{}, rest) : List<&2, Nat> & String}) -> {ArL.span_d(ArD.put_ds(ds, rest)) == (ds, rest) : List<&2, Nat> & String}:
  %Equal.sym(String, ArD.put_ds(ds, rest), SL.spell_ds(ds, rest), AL.al.put_spell(ds, rest)) : {ArL.span_d(_) == (ds, rest) : List<&2, Nat> & String}
  AL.al.span_d_app(ds, rest, ok, stop)

def ad.some_ne(s: String, ne: {SL.nonempty(s) == True{} : Bool}) -> {ArL.some(s) == True{} : Bool}:
  match s:
    case SNil{}:
      ne
    case SCon{c, t}:
      {==}

# `METRIC `, a name and `=`: what follows is read as the value
def ad.head(+name: String, +v: String, +okn: {Bool.and(SL.nonempty(name), SL.all_name(name)) == True{} : Bool}) -> {ArL.parse(String.append("METRIC ", String.append(name, SCon{'=', v}))) == ArL.pl.sign(" ", name, v) : Maybe<&2, ArL.Parts>}:
  +x = String.append(name, SCon{'=', v})
  +ne = AdDec.ad.and_l(SL.nonempty(name), SL.all_name(name), okn)
  +ok = AdDec.ad.and_r(SL.nonempty(name), SL.all_name(name), okn)
  %Equal.sym(String & String, ArL.span_b(x), (SNil{}, x), AL.al.stop_b_name(name, SCon{'=', v}, ne, ok)) : {ArL.pl.sp(ArL.span.at(True{}, ' ', x, _)) == ArL.pl.sign(" ", name, v) : Maybe<&2, ArL.Parts>}
  %Equal.sym(String & String, ArL.span_n(x), (name, SCon{'=', v}), AL.al.span_n_app(name, SCon{'=', v}, ok, {==})) : {ArL.pl.name(" ", _) == ArL.pl.sign(" ", name, v) : Maybe<&2, ArL.Parts>}
  %Equal.sym(Bool, ArL.some(name), True{}, ad.some_ne(name, ne)) : {ArL.pl.name.ok(_, " ", name, SCon{'=', v}) == ArL.pl.sign(" ", name, v) : Maybe<&2, ArL.Parts>}
  {==}

# The value
# ---------

# after `=`: the sign, then the first digit
def ad.sign_lem(-sp: String, -name: String, neg: Bool, +h: Nat, -t: List<&2, Nat>, -r: String, hh: {Nat.is_lt(h, 10n) == True{} : Bool}) -> {ArL.pl.sign(sp, name, ArD.show.sign(neg, ArD.put_ds(h <> t, r))) == ArL.pl.int(sp, name, neg, ArL.span_d(ArD.put_ds(h <> t, r))) : Maybe<&2, ArL.Parts>}:
  match neg:
    case True{}:
      {==}
    case False{}:
      %Equal.sym(Bool, ArL.same_char(ArD.dchar(h), '-'), False{}, AdPrint.ad.dchar_minus(h, hh)) : {ArL.pl.sign.at(_, sp, name, ArD.dchar(h), ArD.put_ds(t, r)) == ArL.pl.int(sp, name, False{}, ArL.span_d(ArD.put_ds(h <> t, r))) : Maybe<&2, ArL.Parts>}
      {==}

# integer digits, then the end
def ad.int_only(-sp: String, -name: String, -neg: Bool, +h: Nat, +t: List<&2, Nat>, ok: {SD.digits_ok(h <> t) == True{} : Bool}) -> {ArL.pl.int(sp, name, neg, ArL.span_d(ArD.put_ds(h <> t, ""))) == Some{ArL.Parts{sp, name, neg, h <> t, None{}, ""}} : Maybe<&2, ArL.Parts>}:
  %Equal.sym(List<&2, Nat> & String, ArL.span_d(ArD.put_ds(h <> t, "")), (h <> t, ""), ad.span_put(h <> t, "", ok, {==})) : {ArL.pl.int(sp, name, neg, _) == Some{ArL.Parts{sp, name, neg, h <> t, None{}, ""}} : Maybe<&2, ArL.Parts>}
  {==}

# integer digits, a point, fraction digits, then the end
def ad.int_frac(-sp: String, -name: String, -neg: Bool, +i: List<&2, Nat>, +f: List<&2, Nat>, oi: {SD.digits_ok(i) == True{} : Bool}, of: {SD.digits_ok(f) == True{} : Bool}, ai: {ArL.any_d(i) == True{} : Bool}, af: {ArL.any_d(f) == True{} : Bool}) -> {ArL.pl.int(sp, name, neg, ArL.span_d(ArD.put_ds(i, SCon{'.', ArD.put_ds(f, "")}))) == Some{ArL.Parts{sp, name, neg, i, Some{f}, ""}} : Maybe<&2, ArL.Parts>}:
  %Equal.sym(List<&2, Nat> & String, ArL.span_d(ArD.put_ds(i, SCon{'.', ArD.put_ds(f, "")})), (i, SCon{'.', ArD.put_ds(f, "")}), ad.span_put(i, SCon{'.', ArD.put_ds(f, "")}, oi, {==})) : {ArL.pl.int(sp, name, neg, _) == Some{ArL.Parts{sp, name, neg, i, Some{f}, ""}} : Maybe<&2, ArL.Parts>}
  %Equal.sym(Bool, ArL.any_d(i), True{}, ai) : {ArL.pl.int.ok(_, sp, name, neg, i, SCon{'.', ArD.put_ds(f, "")}) == Some{ArL.Parts{sp, name, neg, i, Some{f}, ""}} : Maybe<&2, ArL.Parts>}
  %Equal.sym(List<&2, Nat> & String, ArL.span_d(ArD.put_ds(f, "")), (f, ""), ad.span_put(f, "", of, {==})) : {ArL.pl.frac.got(sp, name, neg, i, _) == Some{ArL.Parts{sp, name, neg, i, Some{f}, ""}} : Maybe<&2, ArL.Parts>}
  %Equal.sym(Bool, ArL.any_d(f), True{}, af) : {ArL.pl.frac.ok(_, sp, name, neg, i, f, "") == Some{ArL.Parts{sp, name, neg, i, Some{f}, ""}} : Maybe<&2, ArL.Parts>}
  {==}

def ad.fit_len(xs: List<&2, Nat>, fit: {Nat.is_le(SL.dlen(xs), 15n) == True{} : Bool}) -> {Nat.is_le(ArD.len(xs), 15n) == True{} : Bool}:
  %AdPrint.ad.dlen_len(xs) : {Nat.is_le(_, 15n) == True{} : Bool}
  fit

# no point: the digits are the integer
def ad.v_int(+name: String, +neg: Bool, +h: Nat, +t: List<&2, Nat>, hz: {Nat.is_eq(h, 0n) == False{} : Bool}, +dok: {SD.digits_ok(h <> t) == True{} : Bool}, fit: {Nat.is_le(SL.dlen(h <> t), 15n) == True{} : Bool}) -> {ArL.metric.of(ArL.pl.sign(" ", name, ArD.show(ArD.Dec{neg, h <> t, 0n}))) == Some{ArL.Kv{name, ArD.Dec{neg, h <> t, 0n}}} : Maybe<&2, ArL.Kv>}:
  %Equal.sym(Maybe<&2, ArL.Parts>, ArL.pl.sign(" ", name, ArD.show.sign(neg, ArD.put_ds(h <> t, ""))), ArL.pl.int(" ", name, neg, ArL.span_d(ArD.put_ds(h <> t, ""))), ad.sign_lem(" ", name, neg, h, t, "", AdDec.ad.and_l(Nat.is_lt(h, 10n), SD.digits_ok(t), dok))) : {ArL.metric.of(_) == Some{ArL.Kv{name, ArD.Dec{neg, h <> t, 0n}}} : Maybe<&2, ArL.Kv>}
  %Equal.sym(Maybe<&2, ArL.Parts>, ArL.pl.int(" ", name, neg, ArL.span_d(ArD.put_ds(h <> t, ""))), Some{ArL.Parts{" ", name, neg, h <> t, None{}, ""}}, ad.int_only(" ", name, neg, h, t, dok)) : {ArL.metric.of(_) == Some{ArL.Kv{name, ArD.Dec{neg, h <> t, 0n}}} : Maybe<&2, ArL.Kv>}
  AdPrint.ad.canon_go(name, neg, h <> t, Nil{}, h, t, 0n,
    Equal.trans(List<&2, Nat>, ArL.drop(ArD.cat(h <> t, Nil{})), ArL.drop(h <> t), h <> t,
      Equal.cong(List<&2, Nat>, List<&2, Nat>, l => ArL.drop(l), ArD.cat(h <> t, Nil{}), h <> t, AdPrint.ad.cat_nil(h <> t)),
      AdPrint.ad.drop_nz(h, t, hz)),
    {==},
    ad.fit_len(h <> t, fit))

# more digits than the scale: the point among them
def ad.v_more(+name: String, +neg: Bool, +h: Nat, +t: List<&2, Nat>, +p: Nat, +hm: {Nat.is_lt(p, ArD.len(t)) == True{} : Bool}, hz: {Nat.is_eq(h, 0n) == False{} : Bool}, +dok: {SD.digits_ok(h <> t) == True{} : Bool}, lt: {SD.last_nz(h <> t) == True{} : Bool}, fit: {Nat.is_le(SL.dlen(h <> t), 15n) == True{} : Bool}) -> {ArL.metric.of(ArL.pl.sign(" ", name, ArD.show.sign(neg, ArD.show.mag(True{}, h <> t, 1n+ArD.len(t), 1n+p)))) == Some{ArL.Kv{name, ArD.Dec{neg, h <> t, 1n+p}}} : Maybe<&2, ArL.Kv>}:
  +k = Nat.sub(ArD.len(t), 1n+p)
  +i = {h <> AdPrint.ad.take(k, t) : List<&2, Nat>}
  +f = AdPrint.ad.skip(k, t)
  +hh = AdDec.ad.and_l(Nat.is_lt(h, 10n), SD.digits_ok(t), dok)
  +dt = AdDec.ad.and_r(Nat.is_lt(h, 10n), SD.digits_ok(t), dok)
  +el = Equal.trans(Nat, ArD.len(f), Nat.sub(ArD.len(t), k), 1n+p, AdPrint.ad.len_skip(k, t), AdPrint.ad.sub_sub(ArD.len(t), 1n+p, AdPrint.ad.lt_succ_le(p, ArD.len(t), hm)))
  +af = Equal.trans(Bool, ArL.any_d(f), Nat.is_lt(0n, ArD.len(f)), True{}, AdPrint.ad.any_len(f), Equal.cong(Nat, Bool, n => Nat.is_lt(0n, n), ArD.len(f), 1n+p, el))
  +ect = AdPrint.ad.cat_take_skip(k, t)
  +lf = Equal.trans(Bool, SD.last_nz(f), SD.last_nz(h <> ArD.cat(AdPrint.ad.take(k, t), f)), True{},
    Equal.sym(Bool, SD.last_nz(ArD.cat(i, f)), SD.last_nz(f), AdPrint.ad.last_cat(i, f, af)),
    Equal.trans(Bool, SD.last_nz(h <> ArD.cat(AdPrint.ad.take(k, t), f)), SD.last_nz(h <> t), True{},
      Equal.cong(List<&2, Nat>, Bool, l => SD.last_nz(h <> l), ArD.cat(AdPrint.ad.take(k, t), f), t, ect),
      lt))
  %Equal.sym(Nat, Nat.sub(ArD.len(t), p), 1n+k, AdPrint.ad.lt_sub(p, ArD.len(t), hm)) : {ArL.metric.of(ArL.pl.sign(" ", name, ArD.show.sign(neg, ArD.show.parts(ArD.split(_, h <> t))))) == Some{ArL.Kv{name, ArD.Dec{neg, h <> t, 1n+p}}} : Maybe<&2, ArL.Kv>}
  %AdPrint.ad.split_eq(k, t) : {ArL.metric.of(ArL.pl.sign(" ", name, ArD.show.sign(neg, ArD.show.parts(ArD.split.on(h, _))))) == Some{ArL.Kv{name, ArD.Dec{neg, h <> t, 1n+p}}} : Maybe<&2, ArL.Kv>}
  %Equal.sym(Maybe<&2, ArL.Parts>, ArL.pl.sign(" ", name, ArD.show.sign(neg, ArD.put_ds(i, SCon{'.', ArD.put_ds(f, "")}))), ArL.pl.int(" ", name, neg, ArL.span_d(ArD.put_ds(i, SCon{'.', ArD.put_ds(f, "")}))), ad.sign_lem(" ", name, neg, h, AdPrint.ad.take(k, t), SCon{'.', ArD.put_ds(f, "")}, hh)) : {ArL.metric.of(_) == Some{ArL.Kv{name, ArD.Dec{neg, h <> t, 1n+p}}} : Maybe<&2, ArL.Kv>}
  %Equal.sym(Maybe<&2, ArL.Parts>, ArL.pl.int(" ", name, neg, ArL.span_d(ArD.put_ds(i, SCon{'.', ArD.put_ds(f, "")}))), Some{ArL.Parts{" ", name, neg, i, Some{f}, ""}}, ad.int_frac(" ", name, neg, i, f, AdDec.ad.and_intro(Nat.is_lt(h, 10n), SD.digits_ok(AdPrint.ad.take(k, t)), hh, AdPrint.ad.digits_take(k, t, dt)), AdPrint.ad.digits_skip(k, t, dt), {==}, af)) : {ArL.metric.of(_) == Some{ArL.Kv{name, ArD.Dec{neg, h <> t, 1n+p}}} : Maybe<&2, ArL.Kv>}
  %Equal.sym(List<&2, Nat>, ArL.strip(f), f, AdPrint.ad.strip_id(f, lf)) : {ArL.canon.go(name, neg, i, _) == Some{ArL.Kv{name, ArD.Dec{neg, h <> t, 1n+p}}} : Maybe<&2, ArL.Kv>}
  AdPrint.ad.canon_go(name, neg, i, f, h, t, 1n+p,
    Equal.trans(List<&2, Nat>, ArL.drop(h <> ArD.cat(AdPrint.ad.take(k, t), f)), ArL.drop(h <> t), h <> t,
      Equal.cong(List<&2, Nat>, List<&2, Nat>, l => ArL.drop(h <> l), ArD.cat(AdPrint.ad.take(k, t), f), t, ect),
      AdPrint.ad.drop_nz(h, t, hz)),
    el,
    ad.fit_len(h <> t, fit))

# no more digits than the scale: `0.`, zeros, then the digits
def ad.v_less(+name: String, +neg: Bool, +h: Nat, +t: List<&2, Nat>, +p: Nat, hm: {Nat.is_lt(p, ArD.len(t)) == False{} : Bool}, hz: {Nat.is_eq(h, 0n) == False{} : Bool}, +dok: {SD.digits_ok(h <> t) == True{} : Bool}, lt: {SD.last_nz(h <> t) == True{} : Bool}, fit: {Nat.is_le(SL.dlen(h <> t), 15n) == True{} : Bool}) -> {ArL.metric.of(ArL.pl.sign(" ", name, ArD.show.sign(neg, ArD.show.mag(False{}, h <> t, 1n+ArD.len(t), 1n+p)))) == Some{ArL.Kv{name, ArD.Dec{neg, h <> t, 1n+p}}} : Maybe<&2, ArL.Kv>}:
  +z = Nat.sub(p, ArD.len(t))
  +f = ArD.cat(ArD.zeros(z), h <> t)
  +af = AdPrint.ad.any_cat(ArD.zeros(z), h <> t, {==})
  %AdPrint.ad.put_cat(ArD.zeros(z), h <> t, "") : {ArL.metric.of(ArL.pl.sign(" ", name, ArD.show.sign(neg, SCon{'0', SCon{'.', _}}))) == Some{ArL.Kv{name, ArD.Dec{neg, h <> t, 1n+p}}} : Maybe<&2, ArL.Kv>}
  %Equal.sym(Maybe<&2, ArL.Parts>, ArL.pl.sign(" ", name, ArD.show.sign(neg, ArD.put_ds([0n], SCon{'.', ArD.put_ds(f, "")}))), ArL.pl.int(" ", name, neg, ArL.span_d(ArD.put_ds([0n], SCon{'.', ArD.put_ds(f, "")}))), ad.sign_lem(" ", name, neg, 0n, Nil{}, SCon{'.', ArD.put_ds(f, "")}, {==})) : {ArL.metric.of(_) == Some{ArL.Kv{name, ArD.Dec{neg, h <> t, 1n+p}}} : Maybe<&2, ArL.Kv>}
  %Equal.sym(Maybe<&2, ArL.Parts>, ArL.pl.int(" ", name, neg, ArL.span_d(ArD.put_ds([0n], SCon{'.', ArD.put_ds(f, "")}))), Some{ArL.Parts{" ", name, neg, [0n], Some{f}, ""}}, ad.int_frac(" ", name, neg, [0n], f, {==}, AdDec.ad.digits_cat(ArD.zeros(z), h <> t, AdDec.ad.digits_zeros(z), dok), {==}, af)) : {ArL.metric.of(_) == Some{ArL.Kv{name, ArD.Dec{neg, h <> t, 1n+p}}} : Maybe<&2, ArL.Kv>}
  %Equal.sym(List<&2, Nat>, ArL.strip(f), f, AdPrint.ad.strip_id(f, Equal.trans(Bool, SD.last_nz(f), SD.last_nz(h <> t), True{}, AdPrint.ad.last_cat(ArD.zeros(z), h <> t, {==}), lt))) : {ArL.canon.go(name, neg, [0n], _) == Some{ArL.Kv{name, ArD.Dec{neg, h <> t, 1n+p}}} : Maybe<&2, ArL.Kv>}
  AdPrint.ad.canon_go(name, neg, [0n], f, h, t, 1n+p,
    Equal.trans(List<&2, Nat>, ArL.drop(ArD.cat([0n], f)), ArL.drop(h <> t), h <> t,
      AdPrint.ad.drop_zeros(z, h <> t),
      AdPrint.ad.drop_nz(h, t, hz)),
    Equal.trans(Nat, ArD.len(f), Nat.add(z, ArD.len(h <> t)), 1n+p,
      AdDec.ad.len_pad(z, h <> t),
      AdPrint.ad.le_split(1n+p, 1n+ArD.len(t), AdPrint.ad.not_lt_le(p, ArD.len(t), hm))),
    ad.fit_len(h <> t, fit))

def ad.v_mag(+name: String, +neg: Bool, +h: Nat, +t: List<&2, Nat>, +p: Nat, more: Bool, hm: {Nat.is_lt(p, ArD.len(t)) == more : Bool}, hz: {Nat.is_eq(h, 0n) == False{} : Bool}, dok: {SD.digits_ok(h <> t) == True{} : Bool}, lt: {SD.last_nz(h <> t) == True{} : Bool}, fit: {Nat.is_le(SL.dlen(h <> t), 15n) == True{} : Bool}) -> {ArL.metric.of(ArL.pl.sign(" ", name, ArD.show.sign(neg, ArD.show.mag(more, h <> t, 1n+ArD.len(t), 1n+p)))) == Some{ArL.Kv{name, ArD.Dec{neg, h <> t, 1n+p}}} : Maybe<&2, ArL.Kv>}:
  match more:
    case True{}:
      ad.v_more(name, neg, h, t, p, hm, hz, dok, lt, fit)
    case False{}:
      ad.v_less(name, neg, h, t, p, hm, hz, dok, lt, fit)

# a canonical decimal, printed, reads back as itself
def ad.value(+name: String, ds: List<&2, Nat>, neg: Bool, +scale: Nat, +c: {SD.canon.ds(neg, ds, scale) == True{} : Bool}, fit: {Nat.is_le(SL.dlen(ds), 15n) == True{} : Bool}) -> {ArL.metric.of(ArL.pl.sign(" ", name, ArD.show(ArD.Dec{neg, ds, scale}))) == Some{ArL.Kv{name, ArD.Dec{neg, ds, scale}}} : Maybe<&2, ArL.Kv>}:
  match ds:
    case Nil{}:
      match neg:
        case True{}:
          AdDec.ad.absurd({ArL.metric.of(ArL.pl.sign(" ", name, "0")) == Some{ArL.Kv{name, ArD.Dec{True{}, Nil{}, scale}}} : Maybe<&2, ArL.Kv>}, c)
        case False{}:
          match scale:
            case 0n:
              {==}
            case 1n+q:
              AdDec.ad.absurd({ArL.metric.of(ArL.pl.sign(" ", name, "0")) == Some{ArL.Kv{name, ArD.Dec{False{}, Nil{}, 1n+q}}} : Maybe<&2, ArL.Kv>}, c)
    case +h <> +t:
      match scale:
        case 0n:
          +rest = AdDec.ad.and_r(Nat.is_ne(h, 0n), Bool.and(SD.digits_ok(h <> t), True{}), c)
          ad.v_int(name, neg, h, t, AdPrint.ad.not_true(Nat.is_eq(h, 0n), AdDec.ad.and_l(Nat.is_ne(h, 0n), Bool.and(SD.digits_ok(h <> t), True{}), c)), AdDec.ad.and_l(SD.digits_ok(h <> t), True{}, rest), fit)
        case 1n+p:
          +rest = AdDec.ad.and_r(Nat.is_ne(h, 0n), Bool.and(SD.digits_ok(h <> t), SD.last_nz(h <> t)), c)
          ad.v_mag(name, neg, h, t, p, Nat.is_lt(p, ArD.len(t)), {==}, AdPrint.ad.not_true(Nat.is_eq(h, 0n), AdDec.ad.and_l(Nat.is_ne(h, 0n), Bool.and(SD.digits_ok(h <> t), SD.last_nz(h <> t)), c)), AdDec.ad.and_l(SD.digits_ok(h <> t), SD.last_nz(h <> t), rest), AdDec.ad.and_r(SD.digits_ok(h <> t), SD.last_nz(h <> t), rest), fit)
