# eukhe: the proof of LAW cvar_ffi_open

import Base
import ../../bend/cvar.bend as Cv
import ../../bend/ffi_cvar.bend as FCv
import ../../bend/wire.bend as Wr
import ../../laws/cvar.bend as Cvar
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../base.bend as L
import ./base.bend as LA

def pvf.bind_rt(+a: Cv.KeyBind, +rest: String, +h: {Cvar.cvar_bind_fits(a) == True{} : Bool}) -> {FCv.get_bind(FCv.put_bind(a, rest)) == Wr.Got{a, rest} : Wr.Dec<Cv.KeyBind>}:
  match a:
    case Cv.KeyBind{+n, +b}:
      Equal.trans(Wr.Dec<Cv.KeyBind>, FCv.get_bind.key(Wr.get_nat(Wr.put_nat(n, FCv.put_cmds(b, rest)))), FCv.get_bind.key(Wr.Got{n, FCv.put_cmds(b, rest)}), Wr.Got{Cv.KeyBind{n, b}, rest}, Equal.cong(Wr.Dec<Nat>, Wr.Dec<Cv.KeyBind>, d => FCv.get_bind.key(d), Wr.get_nat(Wr.put_nat(n, FCv.put_cmds(b, rest))), Wr.Got{n, FCv.put_cmds(b, rest)}, Wire.wire_nat_round_trip(n, FCv.put_cmds(b, rest), L.wr_and_l(LawsBase.wire_fits(n), Cvar.cvar_cmds_fit(b), h))), Equal.cong(Wr.Dec<List<&2, Cv.Cmd>>, Wr.Dec<Cv.KeyBind>, d => FCv.get_bind.cmds(n, d), Wr.get_list(~Cv.Cmd, ~FCv.get_cmd, Wr.put_list(~Cv.Cmd, ~FCv.put_cmd, b, rest)), Wr.Got{b, rest}, LA.pvf.cs.rt(b, rest, L.wr_and_r(LawsBase.wire_fits(n), Cvar.cvar_cmds_fit(b), h))))

# the items of a list of Cv.KeyBind, then rest
def pvf.bs.items(xs: List<&2, Cv.KeyBind>, rest: String) -> String:
  match xs:
    case Nil{}:
      rest
    case Con{x, t}:
      FCv.put_bind(x, pvf.bs.items(t, rest))

def pvf.bs.put_go(xs: List<&2, Cv.KeyBind>, -rest: String) -> {Wr.put_list.go(~Cv.KeyBind, ~FCv.put_bind, xs, rest) == (List.length(&2, Cv.KeyBind, xs), pvf.bs.items(xs, rest)) : Nat & String}:
  match xs:
    case Nil{}:
      {==}
    case Con{x, +t}:
      %Equal.sym(Nat & String, Wr.put_list.go(~Cv.KeyBind, ~FCv.put_bind, t, rest), (List.length(&2, Cv.KeyBind, t), pvf.bs.items(t, rest)), pvf.bs.put_go(t, rest)) : {Wr.put_list.step(~Cv.KeyBind, ~FCv.put_bind, x, _) == (1n+List.length(&2, Cv.KeyBind, t), FCv.put_bind(x, pvf.bs.items(t, rest))) : Nat & String}
      {==}

# a list of Cv.KeyBind is its count, then its items
def pvf.bs.put(+xs: List<&2, Cv.KeyBind>, -rest: String) -> {Wr.put_list(~Cv.KeyBind, ~FCv.put_bind, xs, rest) == Wr.put_nat(List.length(&2, Cv.KeyBind, xs), pvf.bs.items(xs, rest)) : String}:
  %Equal.sym(Nat & String, Wr.put_list.go(~Cv.KeyBind, ~FCv.put_bind, xs, rest), (List.length(&2, Cv.KeyBind, xs), pvf.bs.items(xs, rest)), pvf.bs.put_go(xs, rest)) : {Wr.put_list.fin(_) == Wr.put_nat(List.length(&2, Cv.KeyBind, xs), pvf.bs.items(xs, rest)) : String}
  {==}

# the item loop reads back x then t
def pvf.bs.go_rt(+t: List<&2, Cv.KeyBind>, +x: Cv.KeyBind, +rest: String, +hf: {Cvar.cvar_binds_all(x <> t) == True{} : Bool}) -> {Wr.get_list.go(~Cv.KeyBind, ~FCv.get_bind, List.length(&2, Cv.KeyBind, t), FCv.get_bind(FCv.put_bind(x, pvf.bs.items(t, rest)))) == Wr.Got{x <> t, rest} : Wr.Dec<List<&2, Cv.KeyBind>>}:
  match t:
    case Nil{}:
      %Equal.sym(Wr.Dec<Cv.KeyBind>, FCv.get_bind(FCv.put_bind(x, rest)), Wr.Got{x, rest}, pvf.bind_rt(x, rest, L.wr_and_l(Cvar.cvar_bind_fits(x), True{}, hf))) : {Wr.get_list.go(~Cv.KeyBind, ~FCv.get_bind, 0n, _) == Wr.Got{[x], rest} : Wr.Dec<List<&2, Cv.KeyBind>>}
      {==}
    case Con{+y, +u}:
      %Equal.sym(Wr.Dec<Cv.KeyBind>, FCv.get_bind(FCv.put_bind(x, FCv.put_bind(y, pvf.bs.items(u, rest)))), Wr.Got{x, FCv.put_bind(y, pvf.bs.items(u, rest))}, pvf.bind_rt(x, FCv.put_bind(y, pvf.bs.items(u, rest)), L.wr_and_l(Cvar.cvar_bind_fits(x), Cvar.cvar_binds_all(y <> u), hf))) : {Wr.get_list.go(~Cv.KeyBind, ~FCv.get_bind, 1n+List.length(&2, Cv.KeyBind, u), _) == Wr.Got{x <> y <> u, rest} : Wr.Dec<List<&2, Cv.KeyBind>>}
      %Equal.sym(Wr.Dec<List<&2, Cv.KeyBind>>, Wr.get_list.go(~Cv.KeyBind, ~FCv.get_bind, List.length(&2, Cv.KeyBind, u), FCv.get_bind(FCv.put_bind(y, pvf.bs.items(u, rest)))), Wr.Got{y <> u, rest}, pvf.bs.go_rt(u, y, rest, L.wr_and_r(Cvar.cvar_bind_fits(x), Cvar.cvar_binds_all(y <> u), hf))) : {Wr.get_list.cons(Cv.KeyBind, x, _) == Wr.Got{x <> y <> u, rest} : Wr.Dec<List<&2, Cv.KeyBind>>}
      {==}

# a list of Cv.KeyBind that fits reads back
def pvf.bs.rt(+xs: List<&2, Cv.KeyBind>, +rest: String, h: {Bool.and(LawsBase.wire_fits(List.length(&2, Cv.KeyBind, xs)), Cvar.cvar_binds_all(xs)) == True{} : Bool}) -> {Wr.get_list(~Cv.KeyBind, ~FCv.get_bind, Wr.put_list(~Cv.KeyBind, ~FCv.put_bind, xs, rest)) == Wr.Got{xs, rest} : Wr.Dec<List<&2, Cv.KeyBind>>}:
  match xs:
    case Nil{}:
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(0n, rest)), Wr.Got{0n, rest}, Wire.wire_nat_round_trip(0n, rest, L.wr_and_l(LawsBase.wire_fits(0n), True{}, h))) : {Wr.get_list.start(~Cv.KeyBind, ~FCv.get_bind, _) == Wr.Got{Nil{}, rest} : Wr.Dec<List<&2, Cv.KeyBind>>}
      {==}
    case Con{+x, +t}:
      +r = rest
      +hh = h
      %Equal.sym(String, Wr.put_list(~Cv.KeyBind, ~FCv.put_bind, x <> t, r), Wr.put_nat(List.length(&2, Cv.KeyBind, x <> t), pvf.bs.items(x <> t, r)), pvf.bs.put(x <> t, r)) : {Wr.get_list(~Cv.KeyBind, ~FCv.get_bind, _) == Wr.Got{x <> t, r} : Wr.Dec<List<&2, Cv.KeyBind>>}
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(List.length(&2, Cv.KeyBind, x <> t), pvf.bs.items(x <> t, r))), Wr.Got{List.length(&2, Cv.KeyBind, x <> t), pvf.bs.items(x <> t, r)}, Wire.wire_nat_round_trip(List.length(&2, Cv.KeyBind, x <> t), pvf.bs.items(x <> t, r), L.wr_and_l(LawsBase.wire_fits(List.length(&2, Cv.KeyBind, x <> t)), Cvar.cvar_binds_all(x <> t), hh))) : {Wr.get_list.start(~Cv.KeyBind, ~FCv.get_bind, _) == Wr.Got{x <> t, r} : Wr.Dec<List<&2, Cv.KeyBind>>}
      pvf.bs.go_rt(t, x, r, L.wr_and_r(LawsBase.wire_fits(List.length(&2, Cv.KeyBind, x <> t)), Cvar.cvar_binds_all(x <> t), hh))

def pvf.table_rt(+bs: List<&2, Cv.KeyBind>, +as: List<&2, Cv.Alias>, +rest: String, +h: {Bool.and(Cvar.cvar_binds_fit(bs), Cvar.cvar_aliases_fit(as)) == True{} : Bool}) -> {FCv.get_table(FCv.put_table(bs, as, rest)) == Wr.Got{FCv.Table{bs, as}, rest} : Wr.Dec<FCv.St>}:
  Equal.trans(Wr.Dec<FCv.St>, FCv.get_table.binds(Wr.get_list(~Cv.KeyBind, ~FCv.get_bind, Wr.put_list(~Cv.KeyBind, ~FCv.put_bind, bs, Wr.put_list(~Cv.Alias, ~FCv.put_alias, as, rest)))), FCv.get_table.binds(Wr.Got{bs, Wr.put_list(~Cv.Alias, ~FCv.put_alias, as, rest)}), Wr.Got{FCv.Table{bs, as}, rest}, Equal.cong(Wr.Dec<List<&2, Cv.KeyBind>>, Wr.Dec<FCv.St>, d => FCv.get_table.binds(d), Wr.get_list(~Cv.KeyBind, ~FCv.get_bind, Wr.put_list(~Cv.KeyBind, ~FCv.put_bind, bs, Wr.put_list(~Cv.Alias, ~FCv.put_alias, as, rest))), Wr.Got{bs, Wr.put_list(~Cv.Alias, ~FCv.put_alias, as, rest)}, pvf.bs.rt(bs, Wr.put_list(~Cv.Alias, ~FCv.put_alias, as, rest), L.wr_and_l(Cvar.cvar_binds_fit(bs), Cvar.cvar_aliases_fit(as), h))), Equal.cong(Wr.Dec<List<&2, Cv.Alias>>, Wr.Dec<FCv.St>, d => FCv.get_table.aliases(bs, d), Wr.get_list(~Cv.Alias, ~FCv.get_alias, Wr.put_list(~Cv.Alias, ~FCv.put_alias, as, rest)), Wr.Got{as, rest}, LA.pvf.as.rt(as, rest, L.wr_and_r(Cvar.cvar_binds_fit(bs), Cvar.cvar_aliases_fit(as), h))))

def Cvar.cvar_ffi_open(bs, as, h):
  Equal.cong(Wr.Dec<FCv.St>, FCv.St & String, d => FCv.open.go(d), FCv.get_table(FCv.put_table(bs, as, "")), Wr.Got{FCv.Table{bs, as}, ""}, pvf.table_rt(bs, as, "", h))
