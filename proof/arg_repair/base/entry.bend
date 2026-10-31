# eukhe: lemmas of the entry proofs of area arg_repair: a spelled request
# reads back (ae.*_rt, from the wire round trips), the reply encoders are
# the spec spellers (ae.verdict), and no answer opens with 'E'
# (ae.answer_ok)

import Base
import ../../../bend/arg_repair.bend as Ar
import ../../../bend/ffi_arg_repair.bend as FAr
import ../../../bend/wire.bend as Wr
import ../../../laws/base.bend as LawsBase
import ../../../laws/wire.bend as Wire
import ../../../laws/arg_repair.bend as ArgRepair
import ../base.bend as AB
import ../arg_repair_spec.bend as PSpec
import ../../base/wire.bend as LWire
import ../../wire/wire_bool_round_trip.bend as PWireBoolRoundTrip
import ../../wire/wire_nat_not_err.bend as PWireNatNotErr
import ../../wire/wire_strs_spells.bend as PWireStrsSpells

# Fits
# ----

def ae.l(+a: Bool, -b: Bool, e: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  AB.ab.and_l(a, b, e)

def ae.r(+a: Bool, +b: Bool, e: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  AB.ab.and_r(a, b, e)

# Items
# -----

def ae.ms_rt(m: Maybe<&2, String>, +rest: String, h: {ArgRepair.ar_fit_ms(m) == True{} : Bool}) -> {FAr.get_ms(ArgRepair.ar_w_ms(m, rest)) == Wr.Got{m, rest} : Wr.Dec<Maybe<&2, String>>}:
  match m:
    case None{}:
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(0n, rest)), Wr.Got{0n, rest}, Wire.wire_nat_round_trip(0n, rest, {==})) : {FAr.get_ms.start(_) == Wr.Got{None{}, rest} : Wr.Dec<Maybe<&2, String>>}
      {==}
    case Some{+x}:
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(1n, Wr.put_str(x, rest))), Wr.Got{1n, Wr.put_str(x, rest)}, Wire.wire_nat_round_trip(1n, Wr.put_str(x, rest), {==})) : {FAr.get_ms.start(_) == Wr.Got{Some{x}, rest} : Wr.Dec<Maybe<&2, String>>}
      %Equal.sym(Wr.Dec<String>, Wr.get_str(Wr.put_str(x, rest)), Wr.Got{x, rest}, Wire.wire_str_round_trip(x, rest, h)) : {FAr.get_ms.some(_) == Wr.Got{Some{x}, rest} : Wr.Dec<Maybe<&2, String>>}
      {==}

def ae.prop_rt(p: Ar.Prop, +rest: String, h: {ArgRepair.ar_fit_prop(p) == True{} : Bool}) -> {FAr.get_prop(ArgRepair.ar_w_prop(p, rest)) == Wr.Got{p, rest} : Wr.Dec<Ar.Prop>}:
  match p:
    case Ar.Prop{+n, +k, +i}:
      +hh = h
      +r1 = ArgRepair.ar_w_ms(k, ArgRepair.ar_w_ms(i, rest))
      %Equal.sym(Wr.Dec<String>, Wr.get_str(Wr.put_str(n, r1)), Wr.Got{n, r1}, Wire.wire_str_round_trip(n, r1, ae.l(LawsBase.wire_fits(String.length(n)), Bool.and(ArgRepair.ar_fit_ms(k), ArgRepair.ar_fit_ms(i)), hh))) : {FAr.get_prop.name(_) == Wr.Got{Ar.Prop{n, k, i}, rest} : Wr.Dec<Ar.Prop>}
      +h2 = ae.r(LawsBase.wire_fits(String.length(n)), Bool.and(ArgRepair.ar_fit_ms(k), ArgRepair.ar_fit_ms(i)), hh)
      %Equal.sym(Wr.Dec<Maybe<&2, String>>, FAr.get_ms(r1), Wr.Got{k, ArgRepair.ar_w_ms(i, rest)}, ae.ms_rt(k, ArgRepair.ar_w_ms(i, rest), ae.l(ArgRepair.ar_fit_ms(k), ArgRepair.ar_fit_ms(i), h2))) : {FAr.get_prop.kind(n, _) == Wr.Got{Ar.Prop{n, k, i}, rest} : Wr.Dec<Ar.Prop>}
      %Equal.sym(Wr.Dec<Maybe<&2, String>>, FAr.get_ms(ArgRepair.ar_w_ms(i, rest)), Wr.Got{i, rest}, ae.ms_rt(i, rest, ae.r(ArgRepair.ar_fit_ms(k), ArgRepair.ar_fit_ms(i), h2))) : {FAr.get_prop.items(n, k, _) == Wr.Got{Ar.Prop{n, k, i}, rest} : Wr.Dec<Ar.Prop>}
      {==}

def ae.kv_rt(e: Ar.KV, +rest: String, h: {ArgRepair.ar_fit_kv(e) == True{} : Bool}) -> {FAr.get_kv(ArgRepair.ar_w_kv(e, rest)) == Wr.Got{e, rest} : Wr.Dec<Ar.KV>}:
  match e:
    case Ar.KV{+k, +x}:
      +hh = h
      %Equal.sym(Wr.Dec<String>, Wr.get_str(Wr.put_str(k, Wr.put_str(x, rest))), Wr.Got{k, Wr.put_str(x, rest)}, Wire.wire_str_round_trip(k, Wr.put_str(x, rest), ae.l(LawsBase.wire_fits(String.length(k)), LawsBase.wire_fits(String.length(x)), hh))) : {FAr.get_kv.key(_) == Wr.Got{Ar.KV{k, x}, rest} : Wr.Dec<Ar.KV>}
      %Equal.sym(Wr.Dec<String>, Wr.get_str(Wr.put_str(x, rest)), Wr.Got{x, rest}, Wire.wire_str_round_trip(x, rest, ae.r(LawsBase.wire_fits(String.length(k)), LawsBase.wire_fits(String.length(x)), hh))) : {FAr.get_kv.text(k, _) == Wr.Got{Ar.KV{k, x}, rest} : Wr.Dec<Ar.KV>}
      {==}

def ae.shape_rt(sh: Ar.Shape, +rest: String) -> {FAr.get_shape(Wr.get_nat(ArgRepair.ar_w_shape(sh, rest))) == Wr.Got{sh, rest} : Wr.Dec<Ar.Shape>}:
  match sh:
    case Ar.SPlain{}:
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(0n, rest)), Wr.Got{0n, rest}, Wire.wire_nat_round_trip(0n, rest, {==})) : {FAr.get_shape(_) == Wr.Got{Ar.SPlain{}, rest} : Wr.Dec<Ar.Shape>}
      {==}
    case Ar.SBrace{+b}:
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(1n, Wr.put_bool(b, rest))), Wr.Got{1n, Wr.put_bool(b, rest)}, Wire.wire_nat_round_trip(1n, Wr.put_bool(b, rest), {==})) : {FAr.get_shape(_) == Wr.Got{Ar.SBrace{b}, rest} : Wr.Dec<Ar.Shape>}
      %Equal.sym(Wr.Dec<Bool>, Wr.get_bool(Wr.put_bool(b, rest)), Wr.Got{b, rest}, Wire.wire_bool_round_trip(b, rest)) : {FAr.get_shape.brace(_) == Wr.Got{Ar.SBrace{b}, rest} : Wr.Dec<Ar.Shape>}
      {==}
    case Ar.SBracket{+b}:
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(2n, Wr.put_bool(b, rest))), Wr.Got{2n, Wr.put_bool(b, rest)}, Wire.wire_nat_round_trip(2n, Wr.put_bool(b, rest), {==})) : {FAr.get_shape(_) == Wr.Got{Ar.SBracket{b}, rest} : Wr.Dec<Ar.Shape>}
      %Equal.sym(Wr.Dec<Bool>, Wr.get_bool(Wr.put_bool(b, rest)), Wr.Got{b, rest}, Wire.wire_bool_round_trip(b, rest)) : {FAr.get_shape.bracket(_) == Wr.Got{Ar.SBracket{b}, rest} : Wr.Dec<Ar.Shape>}
      {==}

def ae.val_rt(v: Ar.Val, +rest: String, h: {ArgRepair.ar_fit_val(v) == True{} : Bool}) -> {FAr.get_val(Wr.get_nat(ArgRepair.ar_w_val(v, rest))) == Wr.Got{v, rest} : Wr.Dec<Ar.Val>}:
  match v:
    case Ar.VNull{}:
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(0n, rest)), Wr.Got{0n, rest}, Wire.wire_nat_round_trip(0n, rest, {==})) : {FAr.get_val(_) == Wr.Got{Ar.VNull{}, rest} : Wr.Dec<Ar.Val>}
      {==}
    case Ar.VBool{+b}:
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(1n, Wr.put_bool(b, rest))), Wr.Got{1n, Wr.put_bool(b, rest)}, Wire.wire_nat_round_trip(1n, Wr.put_bool(b, rest), {==})) : {FAr.get_val(_) == Wr.Got{Ar.VBool{b}, rest} : Wr.Dec<Ar.Val>}
      %Equal.sym(Wr.Dec<Bool>, Wr.get_bool(Wr.put_bool(b, rest)), Wr.Got{b, rest}, Wire.wire_bool_round_trip(b, rest)) : {FAr.get_bool.val(_) == Wr.Got{Ar.VBool{b}, rest} : Wr.Dec<Ar.Val>}
      {==}
    case Ar.VNum{+x}:
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(2n, Wr.put_str(x, rest))), Wr.Got{2n, Wr.put_str(x, rest)}, Wire.wire_nat_round_trip(2n, Wr.put_str(x, rest), {==})) : {FAr.get_val(_) == Wr.Got{Ar.VNum{x}, rest} : Wr.Dec<Ar.Val>}
      %Equal.sym(Wr.Dec<String>, Wr.get_str(Wr.put_str(x, rest)), Wr.Got{x, rest}, Wire.wire_str_round_trip(x, rest, h)) : {FAr.get_num.val(_) == Wr.Got{Ar.VNum{x}, rest} : Wr.Dec<Ar.Val>}
      {==}
    case Ar.VStr{+t, +n, +sh}:
      +hh = h
      +r1 = ArgRepair.ar_w_ms(t, ArgRepair.ar_w_ms(n, ArgRepair.ar_w_shape(sh, rest)))
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(3n, r1)), Wr.Got{3n, r1}, Wire.wire_nat_round_trip(3n, r1, {==})) : {FAr.get_val(_) == Wr.Got{Ar.VStr{t, n, sh}, rest} : Wr.Dec<Ar.Val>}
      %Equal.sym(Wr.Dec<Maybe<&2, String>>, FAr.get_ms(r1), Wr.Got{t, ArgRepair.ar_w_ms(n, ArgRepair.ar_w_shape(sh, rest))}, ae.ms_rt(t, ArgRepair.ar_w_ms(n, ArgRepair.ar_w_shape(sh, rest)), ae.l(ArgRepair.ar_fit_ms(t), ArgRepair.ar_fit_ms(n), hh))) : {FAr.get_str.text(_) == Wr.Got{Ar.VStr{t, n, sh}, rest} : Wr.Dec<Ar.Val>}
      %Equal.sym(Wr.Dec<Maybe<&2, String>>, FAr.get_ms(ArgRepair.ar_w_ms(n, ArgRepair.ar_w_shape(sh, rest))), Wr.Got{n, ArgRepair.ar_w_shape(sh, rest)}, ae.ms_rt(n, ArgRepair.ar_w_shape(sh, rest), ae.r(ArgRepair.ar_fit_ms(t), ArgRepair.ar_fit_ms(n), hh))) : {FAr.get_str.num(t, _) == Wr.Got{Ar.VStr{t, n, sh}, rest} : Wr.Dec<Ar.Val>}
      %Equal.sym(Wr.Dec<Ar.Shape>, FAr.get_shape(Wr.get_nat(ArgRepair.ar_w_shape(sh, rest))), Wr.Got{sh, rest}, ae.shape_rt(sh, rest)) : {FAr.get_str.shape(t, n, _) == Wr.Got{Ar.VStr{t, n, sh}, rest} : Wr.Dec<Ar.Val>}
      {==}
    case Ar.VArr{}:
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(4n, rest)), Wr.Got{4n, rest}, Wire.wire_nat_round_trip(4n, rest, {==})) : {FAr.get_val(_) == Wr.Got{Ar.VArr{}, rest} : Wr.Dec<Ar.Val>}
      {==}
    case Ar.VObj{}:
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(5n, rest)), Wr.Got{5n, rest}, Wire.wire_nat_round_trip(5n, rest, {==})) : {FAr.get_val(_) == Wr.Got{Ar.VObj{}, rest} : Wr.Dec<Ar.Val>}
      {==}

def ae.arg_rt(a: Ar.Arg, +rest: String, h: {ArgRepair.ar_fit_arg(a) == True{} : Bool}) -> {FAr.get_arg(ArgRepair.ar_w_arg(a, rest)) == Wr.Got{a, rest} : Wr.Dec<Ar.Arg>}:
  match a:
    case Ar.Arg{+k, +p, +v}:
      +hh = h
      +r1 = ArgRepair.ar_w_ms(p, ArgRepair.ar_w_val(v, rest))
      %Equal.sym(Wr.Dec<String>, Wr.get_str(Wr.put_str(k, r1)), Wr.Got{k, r1}, Wire.wire_str_round_trip(k, r1, ae.l(LawsBase.wire_fits(String.length(k)), Bool.and(ArgRepair.ar_fit_ms(p), ArgRepair.ar_fit_val(v)), hh))) : {FAr.get_arg.key(_) == Wr.Got{Ar.Arg{k, p, v}, rest} : Wr.Dec<Ar.Arg>}
      +h2 = ae.r(LawsBase.wire_fits(String.length(k)), Bool.and(ArgRepair.ar_fit_ms(p), ArgRepair.ar_fit_val(v)), hh)
      %Equal.sym(Wr.Dec<Maybe<&2, String>>, FAr.get_ms(r1), Wr.Got{p, ArgRepair.ar_w_val(v, rest)}, ae.ms_rt(p, ArgRepair.ar_w_val(v, rest), ae.l(ArgRepair.ar_fit_ms(p), ArgRepair.ar_fit_val(v), h2))) : {FAr.get_arg.plain(k, _) == Wr.Got{Ar.Arg{k, p, v}, rest} : Wr.Dec<Ar.Arg>}
      %Equal.sym(Wr.Dec<Ar.Val>, FAr.get_val(Wr.get_nat(ArgRepair.ar_w_val(v, rest))), Wr.Got{v, rest}, ae.val_rt(v, rest, ae.r(ArgRepair.ar_fit_ms(p), ArgRepair.ar_fit_val(v), h2))) : {FAr.get_arg.val(k, p, _) == Wr.Got{Ar.Arg{k, p, v}, rest} : Wr.Dec<Ar.Arg>}
      {==}

# Lists
# -----


def ae.props.go_rt(+t: List<&2, Ar.Prop>, +x: Ar.Prop, +rest: String, h: {ArgRepair.ar_fit_props(x <> t) == True{} : Bool}) ->
  {Wr.get_list.go(~Ar.Prop, ~FAr.get_prop, List.length(&2, Ar.Prop, t), FAr.get_prop(ArgRepair.ar_w_prop(x, ArgRepair.ar_w_props.items(t, rest)))) == Wr.Got{x <> t, rest} : Wr.Dec<List<&2, Ar.Prop>>}:
  match t:
    case Nil{}:
      %Equal.sym(Wr.Dec<Ar.Prop>, FAr.get_prop(ArgRepair.ar_w_prop(x, rest)), Wr.Got{x, rest}, ae.prop_rt(x, rest, ae.l(ArgRepair.ar_fit_prop(x), ArgRepair.ar_fit_props(Nil{}), h))) : {Wr.get_list.go(~Ar.Prop, ~FAr.get_prop, 0n, _) == Wr.Got{[x], rest} : Wr.Dec<List<&2, Ar.Prop>>}
      {==}
    case +y <> +u:
      +hh = h
      +r2 = ArgRepair.ar_w_prop(y, ArgRepair.ar_w_props.items(u, rest))
      %Equal.sym(Wr.Dec<Ar.Prop>, FAr.get_prop(ArgRepair.ar_w_prop(x, r2)), Wr.Got{x, r2}, ae.prop_rt(x, r2, ae.l(ArgRepair.ar_fit_prop(x), ArgRepair.ar_fit_props(y <> u), hh))) : {Wr.get_list.go(~Ar.Prop, ~FAr.get_prop, 1n+List.length(&2, Ar.Prop, u), _) == Wr.Got{x <> y <> u, rest} : Wr.Dec<List<&2, Ar.Prop>>}
      %Equal.sym(Wr.Dec<List<&2, Ar.Prop>>, Wr.get_list.go(~Ar.Prop, ~FAr.get_prop, List.length(&2, Ar.Prop, u), FAr.get_prop(r2)), Wr.Got{y <> u, rest}, ae.props.go_rt(u, y, rest, ae.r(ArgRepair.ar_fit_prop(x), ArgRepair.ar_fit_props(y <> u), hh))) : {Wr.get_list.cons(Ar.Prop, x, _) == Wr.Got{x <> y <> u, rest} : Wr.Dec<List<&2, Ar.Prop>>}
      {==}

# a spelled list whose count and items fit reads back, the rest untouched
def ae.props.rt(xs: List<&2, Ar.Prop>, +rest: String, hn: {LawsBase.wire_fits(List.length(&2, Ar.Prop, xs)) == True{} : Bool}, hf: {ArgRepair.ar_fit_props(xs) == True{} : Bool}) ->
  {Wr.get_list(~Ar.Prop, ~FAr.get_prop, Wr.put_nat(List.length(&2, Ar.Prop, xs), ArgRepair.ar_w_props.items(xs, rest))) == Wr.Got{xs, rest} : Wr.Dec<List<&2, Ar.Prop>>}:
  match xs:
    case Nil{}:
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(0n, rest)), Wr.Got{0n, rest}, Wire.wire_nat_round_trip(0n, rest, hn)) : {Wr.get_list.start(~Ar.Prop, ~FAr.get_prop, _) == Wr.Got{Nil{}, rest} : Wr.Dec<List<&2, Ar.Prop>>}
      {==}
    case +x <> +t:
      +its = ArgRepair.ar_w_props.items(x <> t, rest)
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(List.length(&2, Ar.Prop, x <> t), its)), Wr.Got{List.length(&2, Ar.Prop, x <> t), its}, Wire.wire_nat_round_trip(List.length(&2, Ar.Prop, x <> t), its, hn)) : {Wr.get_list.start(~Ar.Prop, ~FAr.get_prop, _) == Wr.Got{x <> t, rest} : Wr.Dec<List<&2, Ar.Prop>>}
      ae.props.go_rt(t, x, rest, hf)


def ae.kvs.go_rt(+t: List<&2, Ar.KV>, +x: Ar.KV, +rest: String, h: {ArgRepair.ar_fit_kvs(x <> t) == True{} : Bool}) ->
  {Wr.get_list.go(~Ar.KV, ~FAr.get_kv, List.length(&2, Ar.KV, t), FAr.get_kv(ArgRepair.ar_w_kv(x, ArgRepair.ar_w_kvs.items(t, rest)))) == Wr.Got{x <> t, rest} : Wr.Dec<List<&2, Ar.KV>>}:
  match t:
    case Nil{}:
      %Equal.sym(Wr.Dec<Ar.KV>, FAr.get_kv(ArgRepair.ar_w_kv(x, rest)), Wr.Got{x, rest}, ae.kv_rt(x, rest, ae.l(ArgRepair.ar_fit_kv(x), ArgRepair.ar_fit_kvs(Nil{}), h))) : {Wr.get_list.go(~Ar.KV, ~FAr.get_kv, 0n, _) == Wr.Got{[x], rest} : Wr.Dec<List<&2, Ar.KV>>}
      {==}
    case +y <> +u:
      +hh = h
      +r2 = ArgRepair.ar_w_kv(y, ArgRepair.ar_w_kvs.items(u, rest))
      %Equal.sym(Wr.Dec<Ar.KV>, FAr.get_kv(ArgRepair.ar_w_kv(x, r2)), Wr.Got{x, r2}, ae.kv_rt(x, r2, ae.l(ArgRepair.ar_fit_kv(x), ArgRepair.ar_fit_kvs(y <> u), hh))) : {Wr.get_list.go(~Ar.KV, ~FAr.get_kv, 1n+List.length(&2, Ar.KV, u), _) == Wr.Got{x <> y <> u, rest} : Wr.Dec<List<&2, Ar.KV>>}
      %Equal.sym(Wr.Dec<List<&2, Ar.KV>>, Wr.get_list.go(~Ar.KV, ~FAr.get_kv, List.length(&2, Ar.KV, u), FAr.get_kv(r2)), Wr.Got{y <> u, rest}, ae.kvs.go_rt(u, y, rest, ae.r(ArgRepair.ar_fit_kv(x), ArgRepair.ar_fit_kvs(y <> u), hh))) : {Wr.get_list.cons(Ar.KV, x, _) == Wr.Got{x <> y <> u, rest} : Wr.Dec<List<&2, Ar.KV>>}
      {==}

# a spelled list whose count and items fit reads back, the rest untouched
def ae.kvs.rt(xs: List<&2, Ar.KV>, +rest: String, hn: {LawsBase.wire_fits(List.length(&2, Ar.KV, xs)) == True{} : Bool}, hf: {ArgRepair.ar_fit_kvs(xs) == True{} : Bool}) ->
  {Wr.get_list(~Ar.KV, ~FAr.get_kv, Wr.put_nat(List.length(&2, Ar.KV, xs), ArgRepair.ar_w_kvs.items(xs, rest))) == Wr.Got{xs, rest} : Wr.Dec<List<&2, Ar.KV>>}:
  match xs:
    case Nil{}:
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(0n, rest)), Wr.Got{0n, rest}, Wire.wire_nat_round_trip(0n, rest, hn)) : {Wr.get_list.start(~Ar.KV, ~FAr.get_kv, _) == Wr.Got{Nil{}, rest} : Wr.Dec<List<&2, Ar.KV>>}
      {==}
    case +x <> +t:
      +its = ArgRepair.ar_w_kvs.items(x <> t, rest)
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(List.length(&2, Ar.KV, x <> t), its)), Wr.Got{List.length(&2, Ar.KV, x <> t), its}, Wire.wire_nat_round_trip(List.length(&2, Ar.KV, x <> t), its, hn)) : {Wr.get_list.start(~Ar.KV, ~FAr.get_kv, _) == Wr.Got{x <> t, rest} : Wr.Dec<List<&2, Ar.KV>>}
      ae.kvs.go_rt(t, x, rest, hf)


def ae.args.go_rt(+t: List<&2, Ar.Arg>, +x: Ar.Arg, +rest: String, h: {ArgRepair.ar_fit_args(x <> t) == True{} : Bool}) ->
  {Wr.get_list.go(~Ar.Arg, ~FAr.get_arg, List.length(&2, Ar.Arg, t), FAr.get_arg(ArgRepair.ar_w_arg(x, ArgRepair.ar_w_args.items(t, rest)))) == Wr.Got{x <> t, rest} : Wr.Dec<List<&2, Ar.Arg>>}:
  match t:
    case Nil{}:
      %Equal.sym(Wr.Dec<Ar.Arg>, FAr.get_arg(ArgRepair.ar_w_arg(x, rest)), Wr.Got{x, rest}, ae.arg_rt(x, rest, ae.l(ArgRepair.ar_fit_arg(x), ArgRepair.ar_fit_args(Nil{}), h))) : {Wr.get_list.go(~Ar.Arg, ~FAr.get_arg, 0n, _) == Wr.Got{[x], rest} : Wr.Dec<List<&2, Ar.Arg>>}
      {==}
    case +y <> +u:
      +hh = h
      +r2 = ArgRepair.ar_w_arg(y, ArgRepair.ar_w_args.items(u, rest))
      %Equal.sym(Wr.Dec<Ar.Arg>, FAr.get_arg(ArgRepair.ar_w_arg(x, r2)), Wr.Got{x, r2}, ae.arg_rt(x, r2, ae.l(ArgRepair.ar_fit_arg(x), ArgRepair.ar_fit_args(y <> u), hh))) : {Wr.get_list.go(~Ar.Arg, ~FAr.get_arg, 1n+List.length(&2, Ar.Arg, u), _) == Wr.Got{x <> y <> u, rest} : Wr.Dec<List<&2, Ar.Arg>>}
      %Equal.sym(Wr.Dec<List<&2, Ar.Arg>>, Wr.get_list.go(~Ar.Arg, ~FAr.get_arg, List.length(&2, Ar.Arg, u), FAr.get_arg(r2)), Wr.Got{y <> u, rest}, ae.args.go_rt(u, y, rest, ae.r(ArgRepair.ar_fit_arg(x), ArgRepair.ar_fit_args(y <> u), hh))) : {Wr.get_list.cons(Ar.Arg, x, _) == Wr.Got{x <> y <> u, rest} : Wr.Dec<List<&2, Ar.Arg>>}
      {==}

# a spelled list whose count and items fit reads back, the rest untouched
def ae.args.rt(xs: List<&2, Ar.Arg>, +rest: String, hn: {LawsBase.wire_fits(List.length(&2, Ar.Arg, xs)) == True{} : Bool}, hf: {ArgRepair.ar_fit_args(xs) == True{} : Bool}) ->
  {Wr.get_list(~Ar.Arg, ~FAr.get_arg, Wr.put_nat(List.length(&2, Ar.Arg, xs), ArgRepair.ar_w_args.items(xs, rest))) == Wr.Got{xs, rest} : Wr.Dec<List<&2, Ar.Arg>>}:
  match xs:
    case Nil{}:
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(0n, rest)), Wr.Got{0n, rest}, Wire.wire_nat_round_trip(0n, rest, hn)) : {Wr.get_list.start(~Ar.Arg, ~FAr.get_arg, _) == Wr.Got{Nil{}, rest} : Wr.Dec<List<&2, Ar.Arg>>}
      {==}
    case +x <> +t:
      +its = ArgRepair.ar_w_args.items(x <> t, rest)
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(List.length(&2, Ar.Arg, x <> t), its)), Wr.Got{List.length(&2, Ar.Arg, x <> t), its}, Wire.wire_nat_round_trip(List.length(&2, Ar.Arg, x <> t), its, hn)) : {Wr.get_list.start(~Ar.Arg, ~FAr.get_arg, _) == Wr.Got{x <> t, rest} : Wr.Dec<List<&2, Ar.Arg>>}
      ae.args.go_rt(t, x, rest, hf)

# The request
# -----------
def ae.req_rt.at(+ps: List<&2, Ar.Prop>, +cl: Bool, +als: List<&2, Ar.KV>, +rs: List<&2, Ar.KV>, +xs: List<&2, Ar.Arg>, +rest: String, h: {ArgRepair.ar_fit_req(FAr.Req{Ar.Schema{ps, cl}, Ar.Dialect{als, rs}, xs}) == True{} : Bool}) -> {FAr.get_req(ArgRepair.ar_w_req(FAr.Req{Ar.Schema{ps, cl}, Ar.Dialect{als, rs}, xs}, rest)) == Wr.Got{FAr.Req{Ar.Schema{ps, cl}, Ar.Dialect{als, rs}, xs}, rest} : Wr.Dec<FAr.Req>}:
  +g0 = h
  +f0 = ae.l(LawsBase.wire_fits(List.length(&2, Ar.Prop, ps)), Bool.and(ArgRepair.ar_fit_props(ps), Bool.and(LawsBase.wire_fits(List.length(&2, Ar.KV, als)), Bool.and(ArgRepair.ar_fit_kvs(als), Bool.and(LawsBase.wire_fits(List.length(&2, Ar.KV, rs)), Bool.and(ArgRepair.ar_fit_kvs(rs), Bool.and(LawsBase.wire_fits(List.length(&2, Ar.Arg, xs)), ArgRepair.ar_fit_args(xs))))))), g0)
  +g1 = ae.r(LawsBase.wire_fits(List.length(&2, Ar.Prop, ps)), Bool.and(ArgRepair.ar_fit_props(ps), Bool.and(LawsBase.wire_fits(List.length(&2, Ar.KV, als)), Bool.and(ArgRepair.ar_fit_kvs(als), Bool.and(LawsBase.wire_fits(List.length(&2, Ar.KV, rs)), Bool.and(ArgRepair.ar_fit_kvs(rs), Bool.and(LawsBase.wire_fits(List.length(&2, Ar.Arg, xs)), ArgRepair.ar_fit_args(xs))))))), g0)
  +f1 = ae.l(ArgRepair.ar_fit_props(ps), Bool.and(LawsBase.wire_fits(List.length(&2, Ar.KV, als)), Bool.and(ArgRepair.ar_fit_kvs(als), Bool.and(LawsBase.wire_fits(List.length(&2, Ar.KV, rs)), Bool.and(ArgRepair.ar_fit_kvs(rs), Bool.and(LawsBase.wire_fits(List.length(&2, Ar.Arg, xs)), ArgRepair.ar_fit_args(xs)))))), g1)
  +g2 = ae.r(ArgRepair.ar_fit_props(ps), Bool.and(LawsBase.wire_fits(List.length(&2, Ar.KV, als)), Bool.and(ArgRepair.ar_fit_kvs(als), Bool.and(LawsBase.wire_fits(List.length(&2, Ar.KV, rs)), Bool.and(ArgRepair.ar_fit_kvs(rs), Bool.and(LawsBase.wire_fits(List.length(&2, Ar.Arg, xs)), ArgRepair.ar_fit_args(xs)))))), g1)
  +f2 = ae.l(LawsBase.wire_fits(List.length(&2, Ar.KV, als)), Bool.and(ArgRepair.ar_fit_kvs(als), Bool.and(LawsBase.wire_fits(List.length(&2, Ar.KV, rs)), Bool.and(ArgRepair.ar_fit_kvs(rs), Bool.and(LawsBase.wire_fits(List.length(&2, Ar.Arg, xs)), ArgRepair.ar_fit_args(xs))))), g2)
  +g3 = ae.r(LawsBase.wire_fits(List.length(&2, Ar.KV, als)), Bool.and(ArgRepair.ar_fit_kvs(als), Bool.and(LawsBase.wire_fits(List.length(&2, Ar.KV, rs)), Bool.and(ArgRepair.ar_fit_kvs(rs), Bool.and(LawsBase.wire_fits(List.length(&2, Ar.Arg, xs)), ArgRepair.ar_fit_args(xs))))), g2)
  +f3 = ae.l(ArgRepair.ar_fit_kvs(als), Bool.and(LawsBase.wire_fits(List.length(&2, Ar.KV, rs)), Bool.and(ArgRepair.ar_fit_kvs(rs), Bool.and(LawsBase.wire_fits(List.length(&2, Ar.Arg, xs)), ArgRepair.ar_fit_args(xs)))), g3)
  +g4 = ae.r(ArgRepair.ar_fit_kvs(als), Bool.and(LawsBase.wire_fits(List.length(&2, Ar.KV, rs)), Bool.and(ArgRepair.ar_fit_kvs(rs), Bool.and(LawsBase.wire_fits(List.length(&2, Ar.Arg, xs)), ArgRepair.ar_fit_args(xs)))), g3)
  +f4 = ae.l(LawsBase.wire_fits(List.length(&2, Ar.KV, rs)), Bool.and(ArgRepair.ar_fit_kvs(rs), Bool.and(LawsBase.wire_fits(List.length(&2, Ar.Arg, xs)), ArgRepair.ar_fit_args(xs))), g4)
  +g5 = ae.r(LawsBase.wire_fits(List.length(&2, Ar.KV, rs)), Bool.and(ArgRepair.ar_fit_kvs(rs), Bool.and(LawsBase.wire_fits(List.length(&2, Ar.Arg, xs)), ArgRepair.ar_fit_args(xs))), g4)
  +f5 = ae.l(ArgRepair.ar_fit_kvs(rs), Bool.and(LawsBase.wire_fits(List.length(&2, Ar.Arg, xs)), ArgRepair.ar_fit_args(xs)), g5)
  +g6 = ae.r(ArgRepair.ar_fit_kvs(rs), Bool.and(LawsBase.wire_fits(List.length(&2, Ar.Arg, xs)), ArgRepair.ar_fit_args(xs)), g5)
  +f6 = ae.l(LawsBase.wire_fits(List.length(&2, Ar.Arg, xs)), ArgRepair.ar_fit_args(xs), g6)
  +g7 = ae.r(LawsBase.wire_fits(List.length(&2, Ar.Arg, xs)), ArgRepair.ar_fit_args(xs), g6)
  %Equal.sym(Wr.Dec<List<&2, Ar.Prop>>, Wr.get_list(~Ar.Prop, ~FAr.get_prop, Wr.put_nat(List.length(&2, Ar.Prop, ps), ArgRepair.ar_w_props.items(ps, Wr.put_bool(cl, Wr.put_nat(List.length(&2, Ar.KV, als), ArgRepair.ar_w_kvs.items(als, Wr.put_nat(List.length(&2, Ar.KV, rs), ArgRepair.ar_w_kvs.items(rs, Wr.put_nat(List.length(&2, Ar.Arg, xs), ArgRepair.ar_w_args.items(xs, rest)))))))))), Wr.Got{ps, Wr.put_bool(cl, Wr.put_nat(List.length(&2, Ar.KV, als), ArgRepair.ar_w_kvs.items(als, Wr.put_nat(List.length(&2, Ar.KV, rs), ArgRepair.ar_w_kvs.items(rs, Wr.put_nat(List.length(&2, Ar.Arg, xs), ArgRepair.ar_w_args.items(xs, rest)))))))}, ae.props.rt(ps, Wr.put_bool(cl, Wr.put_nat(List.length(&2, Ar.KV, als), ArgRepair.ar_w_kvs.items(als, Wr.put_nat(List.length(&2, Ar.KV, rs), ArgRepair.ar_w_kvs.items(rs, Wr.put_nat(List.length(&2, Ar.Arg, xs), ArgRepair.ar_w_args.items(xs, rest))))))), f0, f1)) : {FAr.get_req.props(_) == Wr.Got{FAr.Req{Ar.Schema{ps, cl}, Ar.Dialect{als, rs}, xs}, rest} : Wr.Dec<FAr.Req>}
  %Equal.sym(Wr.Dec<Bool>, Wr.get_bool(Wr.put_bool(cl, Wr.put_nat(List.length(&2, Ar.KV, als), ArgRepair.ar_w_kvs.items(als, Wr.put_nat(List.length(&2, Ar.KV, rs), ArgRepair.ar_w_kvs.items(rs, Wr.put_nat(List.length(&2, Ar.Arg, xs), ArgRepair.ar_w_args.items(xs, rest)))))))), Wr.Got{cl, Wr.put_nat(List.length(&2, Ar.KV, als), ArgRepair.ar_w_kvs.items(als, Wr.put_nat(List.length(&2, Ar.KV, rs), ArgRepair.ar_w_kvs.items(rs, Wr.put_nat(List.length(&2, Ar.Arg, xs), ArgRepair.ar_w_args.items(xs, rest))))))}, Wire.wire_bool_round_trip(cl, Wr.put_nat(List.length(&2, Ar.KV, als), ArgRepair.ar_w_kvs.items(als, Wr.put_nat(List.length(&2, Ar.KV, rs), ArgRepair.ar_w_kvs.items(rs, Wr.put_nat(List.length(&2, Ar.Arg, xs), ArgRepair.ar_w_args.items(xs, rest)))))))) : {FAr.get_req.closed(ps, _) == Wr.Got{FAr.Req{Ar.Schema{ps, cl}, Ar.Dialect{als, rs}, xs}, rest} : Wr.Dec<FAr.Req>}
  %Equal.sym(Wr.Dec<List<&2, Ar.KV>>, Wr.get_list(~Ar.KV, ~FAr.get_kv, Wr.put_nat(List.length(&2, Ar.KV, als), ArgRepair.ar_w_kvs.items(als, Wr.put_nat(List.length(&2, Ar.KV, rs), ArgRepair.ar_w_kvs.items(rs, Wr.put_nat(List.length(&2, Ar.Arg, xs), ArgRepair.ar_w_args.items(xs, rest))))))), Wr.Got{als, Wr.put_nat(List.length(&2, Ar.KV, rs), ArgRepair.ar_w_kvs.items(rs, Wr.put_nat(List.length(&2, Ar.Arg, xs), ArgRepair.ar_w_args.items(xs, rest))))}, ae.kvs.rt(als, Wr.put_nat(List.length(&2, Ar.KV, rs), ArgRepair.ar_w_kvs.items(rs, Wr.put_nat(List.length(&2, Ar.Arg, xs), ArgRepair.ar_w_args.items(xs, rest)))), f2, f3)) : {FAr.get_req.aliases(Ar.Schema{ps, cl}, _) == Wr.Got{FAr.Req{Ar.Schema{ps, cl}, Ar.Dialect{als, rs}, xs}, rest} : Wr.Dec<FAr.Req>}
  %Equal.sym(Wr.Dec<List<&2, Ar.KV>>, Wr.get_list(~Ar.KV, ~FAr.get_kv, Wr.put_nat(List.length(&2, Ar.KV, rs), ArgRepair.ar_w_kvs.items(rs, Wr.put_nat(List.length(&2, Ar.Arg, xs), ArgRepair.ar_w_args.items(xs, rest))))), Wr.Got{rs, Wr.put_nat(List.length(&2, Ar.Arg, xs), ArgRepair.ar_w_args.items(xs, rest))}, ae.kvs.rt(rs, Wr.put_nat(List.length(&2, Ar.Arg, xs), ArgRepair.ar_w_args.items(xs, rest)), f4, f5)) : {FAr.get_req.refused(Ar.Schema{ps, cl}, als, _) == Wr.Got{FAr.Req{Ar.Schema{ps, cl}, Ar.Dialect{als, rs}, xs}, rest} : Wr.Dec<FAr.Req>}
  %Equal.sym(Wr.Dec<List<&2, Ar.Arg>>, Wr.get_list(~Ar.Arg, ~FAr.get_arg, Wr.put_nat(List.length(&2, Ar.Arg, xs), ArgRepair.ar_w_args.items(xs, rest))), Wr.Got{xs, rest}, ae.args.rt(xs, rest, f6, g7)) : {FAr.get_req.args(Ar.Schema{ps, cl}, Ar.Dialect{als, rs}, _) == Wr.Got{FAr.Req{Ar.Schema{ps, cl}, Ar.Dialect{als, rs}, xs}, rest} : Wr.Dec<FAr.Req>}
  {==}

def ae.req_rt(q: FAr.Req, +rest: String, h: {ArgRepair.ar_fit_req(q) == True{} : Bool}) -> {FAr.get_req(ArgRepair.ar_w_req(q, rest)) == Wr.Got{q, rest} : Wr.Dec<FAr.Req>}:
  match q:
    case FAr.Req{sc, d, +xs}:
      match sc:
        case Ar.Schema{+ps, +cl}:
          match d:
            case Ar.Dialect{+als, +rs}:
              ae.req_rt.at(ps, cl, als, rs, xs, rest, h)


# The reply
# ---------

def ae.to(t: Ar.To, -rest: String) -> {FAr.put_to(t, rest) == ArgRepair.ar_w_to(t, rest) : String}:
  match t:
    case Ar.TBool{b}:
      {==}
    case Ar.TNum{x}:
      {==}
    case Ar.TStr{x}:
      {==}
    case Ar.TOne{}:
      {==}
    case Ar.TObj{}:
      {==}
    case Ar.TArr{}:
      {==}

def ae.out(o: Ar.Out, +rest: String) -> {FAr.put_out(o, rest) == ArgRepair.ar_w_out(o, rest) : String}:
  match o:
    case Ar.Out{+k, m}:
      match m:
        case None{}:
          {==}
        case Some{+t}:
          %ae.to(t, rest) : {FAr.put_out(Ar.Out{k, Some{t}}, rest) == Wr.put_str(k, Wr.put_nat(1n, _)) : String}
          {==}

def ae.rec(r: Ar.Record, -rest: String) -> {FAr.put_record(r, rest) == ArgRepair.ar_w_rec(r, rest) : String}:
  match r:
    case Ar.RAlias{f, x}:
      {==}
    case Ar.RCoerce{k, f, x}:
      {==}

def ae.outs.put_go(xs: List<&2, Ar.Out>, +rest: String) ->
  {Wr.put_list.go(~Ar.Out, ~FAr.put_out, xs, rest) == (List.length(&2, Ar.Out, xs), ArgRepair.ar_w_outs.items(xs, rest)) : Nat & String}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +t:
      %Equal.sym(Nat & String, Wr.put_list.go(~Ar.Out, ~FAr.put_out, t, rest), (List.length(&2, Ar.Out, t), ArgRepair.ar_w_outs.items(t, rest)), ae.outs.put_go(t, rest)) : {Wr.put_list.step(~Ar.Out, ~FAr.put_out, x, _) == (1n+List.length(&2, Ar.Out, t), ArgRepair.ar_w_out(x, ArgRepair.ar_w_outs.items(t, rest))) : Nat & String}
      %ae.out(x, ArgRepair.ar_w_outs.items(t, rest)) : {(1n+List.length(&2, Ar.Out, t), FAr.put_out(x, ArgRepair.ar_w_outs.items(t, rest))) == (1n+List.length(&2, Ar.Out, t), _) : Nat & String}
      {==}

# a list is its count, then its items
def ae.outs.put(+xs: List<&2, Ar.Out>, +rest: String) ->
  {Wr.put_list(~Ar.Out, ~FAr.put_out, xs, rest) == Wr.put_nat(List.length(&2, Ar.Out, xs), ArgRepair.ar_w_outs.items(xs, rest)) : String}:
  %Equal.sym(Nat & String, Wr.put_list.go(~Ar.Out, ~FAr.put_out, xs, rest), (List.length(&2, Ar.Out, xs), ArgRepair.ar_w_outs.items(xs, rest)), ae.outs.put_go(xs, rest)) : {Wr.put_list.fin(_) == Wr.put_nat(List.length(&2, Ar.Out, xs), ArgRepair.ar_w_outs.items(xs, rest)) : String}
  {==}

def ae.recs.put_go(xs: List<&2, Ar.Record>, +rest: String) ->
  {Wr.put_list.go(~Ar.Record, ~FAr.put_record, xs, rest) == (List.length(&2, Ar.Record, xs), ArgRepair.ar_w_recs.items(xs, rest)) : Nat & String}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +t:
      %Equal.sym(Nat & String, Wr.put_list.go(~Ar.Record, ~FAr.put_record, t, rest), (List.length(&2, Ar.Record, t), ArgRepair.ar_w_recs.items(t, rest)), ae.recs.put_go(t, rest)) : {Wr.put_list.step(~Ar.Record, ~FAr.put_record, x, _) == (1n+List.length(&2, Ar.Record, t), ArgRepair.ar_w_rec(x, ArgRepair.ar_w_recs.items(t, rest))) : Nat & String}
      %ae.rec(x, ArgRepair.ar_w_recs.items(t, rest)) : {(1n+List.length(&2, Ar.Record, t), FAr.put_record(x, ArgRepair.ar_w_recs.items(t, rest))) == (1n+List.length(&2, Ar.Record, t), _) : Nat & String}
      {==}

# a list is its count, then its items
def ae.recs.put(+xs: List<&2, Ar.Record>, +rest: String) ->
  {Wr.put_list(~Ar.Record, ~FAr.put_record, xs, rest) == Wr.put_nat(List.length(&2, Ar.Record, xs), ArgRepair.ar_w_recs.items(xs, rest)) : String}:
  %Equal.sym(Nat & String, Wr.put_list.go(~Ar.Record, ~FAr.put_record, xs, rest), (List.length(&2, Ar.Record, xs), ArgRepair.ar_w_recs.items(xs, rest)), ae.recs.put_go(xs, rest)) : {Wr.put_list.fin(_) == Wr.put_nat(List.length(&2, Ar.Record, xs), ArgRepair.ar_w_recs.items(xs, rest)) : String}
  {==}

# the reply encoder is the spec speller
def ae.verdict(v: Ar.Verdict) -> {FAr.put_verdict(v) == ArgRepair.ar_w_verdict(v) : String}:
  match v:
    case Ar.Repaired{+os, +rs}:
      %ae.recs.put(rs, "") : {FAr.put_verdict(Ar.Repaired{os, rs}) == Wr.put_nat(0n, Wr.put_nat(List.length(&2, Ar.Out, os), ArgRepair.ar_w_outs.items(os, _))) : String}
      %ae.outs.put(os, Wr.put_list(~Ar.Record, ~FAr.put_record, rs, "")) : {FAr.put_verdict(Ar.Repaired{os, rs}) == Wr.put_nat(0n, _) : String}
      {==}
    case Ar.Rejected{x}:
      match x:
        case Ar.Refused{k, h}:
          {==}
        case Ar.Unknown{+k, +ns}:
          %Wire.wire_strs_spells(ns, "") : {FAr.put_verdict(Ar.Rejected{Ar.Unknown{k, ns}}) == Wr.put_nat(1n, Wr.put_nat(1n, Wr.put_str(k, _))) : String}
          {==}
        case Ar.Ambiguous{c, f, k}:
          {==}

# the entry answers the spec's verdict, spelled
def ae.reply(q: FAr.Req) -> {FAr.answer(q) == ArgRepair.ar_w_reply(q) : String}:
  match q:
    case FAr.Req{+sc, +d, +xs}:
      %ArgRepair.arg_repair_spec(sc, d, xs) : {FAr.put_verdict(Ar.repair(sc, d, xs)) == ArgRepair.ar_w_verdict(_) : String}
      ae.verdict(Ar.repair(sc, d, xs))

def ae.verdict_ok(v: Ar.Verdict) -> {LawsBase.wire_opens_err(FAr.put_verdict(v)) == False{} : Bool}:
  match v:
    case Ar.Repaired{os, rs}:
      Wire.wire_nat_not_err(0n, Wr.put_list(~Ar.Out, ~FAr.put_out, os, Wr.put_list(~Ar.Record, ~FAr.put_record, rs, "")))
    case Ar.Rejected{x}:
      Wire.wire_nat_not_err(1n, FAr.put_refusal(x, ""))

# every answer opens with a Nat: never 'E'
def ae.answer_ok(q: FAr.Req) -> {LawsBase.wire_opens_err(FAr.answer(q)) == False{} : Bool}:
  match q:
    case FAr.Req{sc, d, xs}:
      ae.verdict_ok(Ar.repair(sc, d, xs))
