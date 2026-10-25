# eukhe: lemmas of the entry proofs of area codemode_source: spelled
# requests read back
#
# Each decoder of bend/ffi_codemode_source.bend reads the spec's spelling
# of a value whose numbers fit back and leaves the rest untouched (Nats,
# Bools: proof/context_order/base/read.bend; strings: wire_str_round_trip;
# the options lines: wire_list_round_trip).

import Base
import ../../../bend/codemode_source.bend as Src
import ../../../bend/ffi_codemode_source.bend as FSrc
import ../../../bend/wire.bend as Wr
import ../../../laws/base.bend as LawsBase
import ../../../laws/wire.bend as Wire
import ../../../laws/codemode_source.bend as CodemodeSource
import ../../context_order/base.bend as LACo
import ../../context_order/base/read.bend as LACoRead

def csq.num(v: Src.Num, +rest: String, h: {CodemodeSource.num_fits(v) == True{} : Bool}) -> {FSrc.get_num(CodemodeSource.spell_num(v, rest)) == Wr.Got{v, rest} : Wr.Dec<Src.Num>}:
  match v:
    case Src.NoInt{}:
      %LACoRead.cot.nat(0n, rest, {==}) : {FSrc.get_num.tag(_) == Wr.Got{Src.NoInt{}, rest} : Wr.Dec<Src.Num>}
      {==}
    case Src.Int{+n}:
      %LACoRead.cot.nat(1n, Wr.put_nat(n, rest), {==}) : {FSrc.get_num.tag(_) == Wr.Got{Src.Int{n}, rest} : Wr.Dec<Src.Num>}
      %LACoRead.cot.nat(n, rest, h) : {FSrc.get_num.n(_) == Wr.Got{Src.Int{n}, rest} : Wr.Dec<Src.Num>}
      {==}

def csq.field(f: Src.Field, +rest: String, +h: {CodemodeSource.field_fits(f) == True{} : Bool}) -> {FSrc.get_field(CodemodeSource.spell_field(f, rest)) == Wr.Got{f, rest} : Wr.Dec<Src.Field>}:
  match f:
    case Src.Field{+k, +v}:
      +r1 = CodemodeSource.spell_num(v, rest)
      %Equal.sym(Wr.Dec<String>, Wr.get_str(Wr.put_str(k, r1)), Wr.Got{k, r1}, Wire.wire_str_round_trip(k, r1, LACo.co.and_l(LawsBase.wire_fits(String.length(k)), CodemodeSource.num_fits(v), h))) : {FSrc.get_field.key(_) == Wr.Got{Src.Field{k, v}, rest} : Wr.Dec<Src.Field>}
      %Equal.sym(Wr.Dec<Src.Num>, FSrc.get_num(r1), Wr.Got{v, rest}, csq.num(v, rest, LACo.co.and_r(LawsBase.wire_fits(String.length(k)), CodemodeSource.num_fits(v), h))) : {FSrc.get_field.num(k, _) == Wr.Got{Src.Field{k, v}, rest} : Wr.Dec<Src.Field>}
      {==}

# a spelled list of fields whose count and items fit reads back
def csq.fl.go_rt(+t: List<&2, Src.Field>, +x: Src.Field, +rest: String, +h: {CodemodeSource.fields_all(x <> t) == True{} : Bool}) -> {Wr.get_list.go(~Src.Field, ~FSrc.get_field, List.length(&2, Src.Field, t), FSrc.get_field(CodemodeSource.spell_field(x, CodemodeSource.spell_fields.items(t, rest)))) == Wr.Got{x <> t, rest} : Wr.Dec<List<&2, Src.Field>>}:
  match t:
    case Nil{}:
      %Equal.sym(Wr.Dec<Src.Field>, FSrc.get_field(CodemodeSource.spell_field(x, rest)), Wr.Got{x, rest}, csq.field(x, rest, LACo.co.and_l(CodemodeSource.field_fits(x), CodemodeSource.fields_all([]), h))) : {Wr.get_list.go(~Src.Field, ~FSrc.get_field, 0n, _) == Wr.Got{[x], rest} : Wr.Dec<List<&2, Src.Field>>}
      {==}
    case Con{+y, +u}:
      +r2 = CodemodeSource.spell_field(y, CodemodeSource.spell_fields.items(u, rest))
      %Equal.sym(Wr.Dec<Src.Field>, FSrc.get_field(CodemodeSource.spell_field(x, r2)), Wr.Got{x, r2}, csq.field(x, r2, LACo.co.and_l(CodemodeSource.field_fits(x), CodemodeSource.fields_all(y <> u), h))) : {Wr.get_list.go(~Src.Field, ~FSrc.get_field, 1n+List.length(&2, Src.Field, u), _) == Wr.Got{x <> y <> u, rest} : Wr.Dec<List<&2, Src.Field>>}
      %Equal.sym(Wr.Dec<List<&2, Src.Field>>, Wr.get_list.go(~Src.Field, ~FSrc.get_field, List.length(&2, Src.Field, u), FSrc.get_field(r2)), Wr.Got{y <> u, rest}, csq.fl.go_rt(u, y, rest, LACo.co.and_r(CodemodeSource.field_fits(x), CodemodeSource.fields_all(y <> u), h))) : {Wr.get_list.cons(Src.Field, x, _) == Wr.Got{x <> y <> u, rest} : Wr.Dec<List<&2, Src.Field>>}
      {==}

def csq.fl.rt(+xs: List<&2, Src.Field>, +r: String, +h: {Bool.and(LawsBase.wire_fits(List.length(&2, Src.Field, xs)), CodemodeSource.fields_all(xs)) == True{} : Bool}) -> {Wr.get_list(~Src.Field, ~FSrc.get_field, Wr.put_nat(List.length(&2, Src.Field, xs), CodemodeSource.spell_fields.items(xs, r))) == Wr.Got{xs, r} : Wr.Dec<List<&2, Src.Field>>}:
  match xs:
    case Nil{}:
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(0n, r)), Wr.Got{0n, r}, Wire.wire_nat_round_trip(0n, r, {==})) : {Wr.get_list.start(~Src.Field, ~FSrc.get_field, _) == Wr.Got{Nil{}, r} : Wr.Dec<List<&2, Src.Field>>}
      {==}
    case Con{+x, +t}:
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(List.length(&2, Src.Field, x <> t), CodemodeSource.spell_fields.items(x <> t, r))), Wr.Got{List.length(&2, Src.Field, x <> t), CodemodeSource.spell_fields.items(x <> t, r)}, Wire.wire_nat_round_trip(List.length(&2, Src.Field, x <> t), CodemodeSource.spell_fields.items(x <> t, r), LACo.co.and_l(LawsBase.wire_fits(List.length(&2, Src.Field, x <> t)), CodemodeSource.fields_all(x <> t), h))) : {Wr.get_list.start(~Src.Field, ~FSrc.get_field, _) == Wr.Got{x <> t, r} : Wr.Dec<List<&2, Src.Field>>}
      csq.fl.go_rt(t, x, r, LACo.co.and_r(LawsBase.wire_fits(List.length(&2, Src.Field, x <> t)), CodemodeSource.fields_all(x <> t), h))

def csq.json(j: Src.Json, +rest: String, +h: {CodemodeSource.json_fits(j) == True{} : Bool}) -> {FSrc.get_json(CodemodeSource.spell_json(j, rest)) == Wr.Got{j, rest} : Wr.Dec<Src.Json>}:
  match j:
    case Src.JsonErr{+t}:
      %LACoRead.cot.nat(0n, Wr.put_str(t, rest), {==}) : {FSrc.get_json.tag(_) == Wr.Got{Src.JsonErr{t}, rest} : Wr.Dec<Src.Json>}
      %Equal.sym(Wr.Dec<String>, Wr.get_str(Wr.put_str(t, rest)), Wr.Got{t, rest}, Wire.wire_str_round_trip(t, rest, h)) : {FSrc.get_json.text(_) == Wr.Got{Src.JsonErr{t}, rest} : Wr.Dec<Src.Json>}
      {==}
    case Src.NotObj{}:
      %LACoRead.cot.nat(1n, rest, {==}) : {FSrc.get_json.tag(_) == Wr.Got{Src.NotObj{}, rest} : Wr.Dec<Src.Json>}
      {==}
    case Src.Obj{+fs}:
      +r1 = Wr.put_nat(List.length(&2, Src.Field, fs), CodemodeSource.spell_fields.items(fs, rest))
      %LACoRead.cot.nat(2n, r1, {==}) : {FSrc.get_json.tag(_) == Wr.Got{Src.Obj{fs}, rest} : Wr.Dec<Src.Json>}
      %Equal.sym(Wr.Dec<List<&2, Src.Field>>, Wr.get_list(~Src.Field, ~FSrc.get_field, r1), Wr.Got{fs, rest}, csq.fl.rt(fs, rest, h)) : {FSrc.get_json.fields(_) == Wr.Got{Src.Obj{fs}, rest} : Wr.Dec<Src.Json>}
      {==}

def csq.dir(d: Src.Dir, +rest: String, +h: {CodemodeSource.dir_fits(d) == True{} : Bool}) -> {FSrc.get_dir(CodemodeSource.spell_dir(d, rest)) == Wr.Got{d, rest} : Wr.Dec<Src.Dir>}:
  match d:
    case Src.Dir{+e, +j}:
      %LACoRead.cot.bool(e, CodemodeSource.spell_json(j, rest)) : {FSrc.get_dir.empty(_) == Wr.Got{Src.Dir{e, j}, rest} : Wr.Dec<Src.Dir>}
      %Equal.sym(Wr.Dec<Src.Json>, FSrc.get_json(CodemodeSource.spell_json(j, rest)), Wr.Got{j, rest}, csq.json(j, rest, h)) : {FSrc.get_dir.json(e, _) == Wr.Got{Src.Dir{e, j}, rest} : Wr.Dec<Src.Dir>}
      {==}

def csq.mdir(m: Maybe<&2, Src.Dir>, +rest: String, +h: {CodemodeSource.mdir_fits(m) == True{} : Bool}) -> {FSrc.get_mdir(CodemodeSource.spell_mdir(m, rest)) == Wr.Got{m, rest} : Wr.Dec<Maybe<&2, Src.Dir>>}:
  match m:
    case None{}:
      %LACoRead.cot.nat(0n, rest, {==}) : {FSrc.get_mdir.tag(_) == Wr.Got{None{}, rest} : Wr.Dec<Maybe<&2, Src.Dir>>}
      {==}
    case Some{+d}:
      %LACoRead.cot.nat(1n, CodemodeSource.spell_dir(d, rest), {==}) : {FSrc.get_mdir.tag(_) == Wr.Got{Some{d}, rest} : Wr.Dec<Maybe<&2, Src.Dir>>}
      %Equal.sym(Wr.Dec<Src.Dir>, FSrc.get_dir(CodemodeSource.spell_dir(d, rest)), Wr.Got{d, rest}, csq.dir(d, rest, h)) : {FSrc.get_mdir.dir(_) == Wr.Got{Some{d}, rest} : Wr.Dec<Maybe<&2, Src.Dir>>}
      {==}

# a spelled request whose numbers fit reads back
def csq.req(f: Src.Facts, +rest: String, +h: {CodemodeSource.req_fits(f) == True{} : Bool}) -> {FSrc.get_req(CodemodeSource.spell_req(f, rest)) == Wr.Got{f, rest} : Wr.Dec<Src.Facts>}:
  match f:
    case Src.Facts{+b, +ms, +rb, +m}:
      +r2 = Wr.put_bool(rb, CodemodeSource.spell_mdir(m, rest))
      +x = Bool.and(LawsBase.wire_fits(List.length(&2, Nat, ms)), LawsBase.wire_nats_fit(ms))
      %LACoRead.cot.bool(b, LawsBase.wire_spell_nats(ms, r2)) : {FSrc.get_req.blank(_) == Wr.Got{Src.Facts{b, ms, rb, m}, rest} : Wr.Dec<Src.Facts>}
      %Wire.wire_nats_spells(ms, r2) : {FSrc.get_req.marks(b, Wr.get_list(~Nat, ~Wr.get_nat, _)) == Wr.Got{Src.Facts{b, ms, rb, m}, rest} : Wr.Dec<Src.Facts>}
      %Equal.sym(Wr.Dec<List<&2, Nat>>, Wr.get_list(~Nat, ~Wr.get_nat, Wr.put_list(~Nat, ~Wr.put_nat, ms, r2)), Wr.Got{ms, r2}, Wire.wire_list_round_trip(ms, r2, LACo.co.and_l(x, CodemodeSource.mdir_fits(m), h))) : {FSrc.get_req.marks(b, _) == Wr.Got{Src.Facts{b, ms, rb, m}, rest} : Wr.Dec<Src.Facts>}
      %LACoRead.cot.bool(rb, CodemodeSource.spell_mdir(m, rest)) : {FSrc.get_req.rest(b, ms, _) == Wr.Got{Src.Facts{b, ms, rb, m}, rest} : Wr.Dec<Src.Facts>}
      %Equal.sym(Wr.Dec<Maybe<&2, Src.Dir>>, FSrc.get_mdir(CodemodeSource.spell_mdir(m, rest)), Wr.Got{m, rest}, csq.mdir(m, rest, LACo.co.and_r(x, CodemodeSource.mdir_fits(m), h))) : {FSrc.get_req.dir(b, ms, rb, _) == Wr.Got{Src.Facts{b, ms, rb, m}, rest} : Wr.Dec<Src.Facts>}
      {==}
