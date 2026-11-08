# eukhe: the proof of LAW mrw_rows_round_trip

import Base
import ../../bend/model_roles.bend as Mr
import ../../bend/ffi_model_roles.bend as FMr
import ../../bend/wire.bend as Wr
import ../../laws/model_roles.bend as ModelRoles
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../base/logic/bool.bend as LLogicBool
import ../base/wire.bend as LWire
import ./mrw_row_round_trip.bend as PMrwRowRoundTrip

# a row reads back (turned around for rewriting)
def pmr.row(+t: Mr.Row, +rest: String, h: {ModelRoles.mrw_row_fits(t) == True{} : Bool}) -> {Wr.Got{t, rest} == FMr.get_row(FMr.put_row(t, rest)) : Wr.Dec<Mr.Row>}:
  Equal.sym(Wr.Dec<Mr.Row>, FMr.get_row(FMr.put_row(t, rest)), Wr.Got{t, rest}, ModelRoles.mrw_row_round_trip(t, rest, h))

# the items of xs, then rest (Mr.Row; a copy of PROOF.bend wire's wr_items)
def pmr.row_items(xs: List<&2, Mr.Row>, rest: String) -> String:
  match xs:
    case Nil{}:
      rest
    case Con{x, t}:
      FMr.put_row(x, pmr.row_items(t, rest))

def pmr.row_put_go(xs: List<&2, Mr.Row>, -rest: String) ->
  {Wr.put_list.go(~Mr.Row, ~FMr.put_row, xs, rest) == (List.length(&2, Mr.Row, xs), pmr.row_items(xs, rest)) : Nat & String}:
  match xs:
    case Nil{}:
      {==}
    case Con{x, +t}:
      %Equal.sym(Nat & String, Wr.put_list.go(~Mr.Row, ~FMr.put_row, t, rest), (List.length(&2, Mr.Row, t), pmr.row_items(t, rest)), pmr.row_put_go(t, rest)) : {Wr.put_list.step(~Mr.Row, ~FMr.put_row, x, _) == (1n+List.length(&2, Mr.Row, t), FMr.put_row(x, pmr.row_items(t, rest))) : Nat & String}
      {==}

# a list is its count, then its items
def pmr.row_put(+xs: List<&2, Mr.Row>, -rest: String) ->
  {Wr.put_list(~Mr.Row, ~FMr.put_row, xs, rest) == Wr.put_nat(List.length(&2, Mr.Row, xs), pmr.row_items(xs, rest)) : String}:
  %Equal.sym(Nat & String, Wr.put_list.go(~Mr.Row, ~FMr.put_row, xs, rest), (List.length(&2, Mr.Row, xs), pmr.row_items(xs, rest)), pmr.row_put_go(xs, rest)) : {Wr.put_list.fin(_) == Wr.put_nat(List.length(&2, Mr.Row, xs), pmr.row_items(xs, rest)) : String}
  {==}

# the item loop reads back x then t (wr_list_go_rt for Mr.Row)
def pmr.row_go_rt(+t: List<&2, Mr.Row>, +x: Mr.Row, +rest: String,
  +hf: {ModelRoles.mrw_rows_fit(x <> t) == True{} : Bool}) ->
  {Wr.get_list.go(~Mr.Row, ~FMr.get_row, List.length(&2, Mr.Row, t), FMr.get_row(FMr.put_row(x, pmr.row_items(t, rest)))) == Wr.Got{x <> t, rest} : Wr.Dec<List<&2, Mr.Row>>}:
  match t:
    case Nil{}:
      %pmr.row(x, rest, LLogicBool.wr_and_l(ModelRoles.mrw_row_fits(x), True{}, hf)) : {Wr.get_list.go(~Mr.Row, ~FMr.get_row, 0n, _) == Wr.Got{[x], rest} : Wr.Dec<List<&2, Mr.Row>>}
      {==}
    case Con{+y, +u}:
      %pmr.row(x, FMr.put_row(y, pmr.row_items(u, rest)), LLogicBool.wr_and_l(ModelRoles.mrw_row_fits(x), ModelRoles.mrw_rows_fit(y <> u), hf)) : {Wr.get_list.go(~Mr.Row, ~FMr.get_row, 1n+List.length(&2, Mr.Row, u), _) == Wr.Got{x <> y <> u, rest} : Wr.Dec<List<&2, Mr.Row>>}
      %Equal.sym(Wr.Dec<List<&2, Mr.Row>>, Wr.get_list.go(~Mr.Row, ~FMr.get_row, List.length(&2, Mr.Row, u), FMr.get_row(FMr.put_row(y, pmr.row_items(u, rest)))), Wr.Got{y <> u, rest}, pmr.row_go_rt(u, y, rest, LLogicBool.wr_and_r(ModelRoles.mrw_row_fits(x), ModelRoles.mrw_rows_fit(y <> u), hf))) : {Wr.get_list.cons(Mr.Row, x, _) == Wr.Got{x <> y <> u, rest} : Wr.Dec<List<&2, Mr.Row>>}
      {==}

def ModelRoles.mrw_rows_round_trip(xs, rest, h):
  match xs:
    case Nil{}:
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(0n, rest)), Wr.Got{0n, rest}, Wire.wire_nat_round_trip(0n, rest, LLogicBool.wr_and_l(LawsBase.wire_fits(0n), True{}, h))) : {Wr.get_list.start(~Mr.Row, ~FMr.get_row, _) == Wr.Got{Nil{}, rest} : Wr.Dec<List<&2, Mr.Row>>}
      {==}
    case Con{+x, +t}:
      +r = rest
      +hh = h
      %Equal.sym(String, Wr.put_list(~Mr.Row, ~FMr.put_row, x <> t, r), Wr.put_nat(List.length(&2, Mr.Row, x <> t), pmr.row_items(x <> t, r)), pmr.row_put(x <> t, r)) : {Wr.get_list(~Mr.Row, ~FMr.get_row, _) == Wr.Got{x <> t, r} : Wr.Dec<List<&2, Mr.Row>>}
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(List.length(&2, Mr.Row, x <> t), pmr.row_items(x <> t, r))), Wr.Got{List.length(&2, Mr.Row, x <> t), pmr.row_items(x <> t, r)}, Wire.wire_nat_round_trip(List.length(&2, Mr.Row, x <> t), pmr.row_items(x <> t, r), LLogicBool.wr_and_l(LawsBase.wire_fits(List.length(&2, Mr.Row, x <> t)), ModelRoles.mrw_rows_fit(x <> t), hh))) : {Wr.get_list.start(~Mr.Row, ~FMr.get_row, _) == Wr.Got{x <> t, r} : Wr.Dec<List<&2, Mr.Row>>}
      pmr.row_go_rt(t, x, r, LLogicBool.wr_and_r(LawsBase.wire_fits(List.length(&2, Mr.Row, x <> t)), ModelRoles.mrw_rows_fit(x <> t), hh))
