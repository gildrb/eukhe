# PROOF of LAW command_ffi_round_trip: a request is its table (a list of
# entries, each two lists of strings and three Bools), then its query (a
# tag, a string, and for a key a row and a press). Each piece is a wire
# value that fits, so each reads back by the wire laws (Nat, Bool, String)
# and the list loop (the pvf.cs pattern of PROOF.bend: count, then items),
# leaving exactly the encoding of the next piece; the last leaves rest.
# Shared codec lemmas for the other command_ffi_* proofs: cfr_strs_rt
# (a list of strings), cfr_req_rt (the request).

import Base
import ../LAWS.bend as Laws
import ../bend/command.bend as Cmd
import ../bend/ffi_command.bend as FCmd
import ../bend/wire.bend as Wr
import ./wire.bend as PWire

# ---- lists of strings ----

# the items of a list of strings, then rest
def cfr_ss_items(xs: List<&2, String>, rest: String) -> String:
  match xs:
    case Nil{}:
      rest
    case Con{x, t}:
      Wr.put_str(x, cfr_ss_items(t, rest))

def cfr_ss_put_go(xs: List<&2, String>, -rest: String) -> {Wr.put_list.go(~String, ~Wr.put_str, xs, rest) == (List.length(&2, String, xs), cfr_ss_items(xs, rest)) : Nat & String}:
  match xs:
    case Nil{}:
      {==}
    case Con{x, +t}:
      %Equal.sym(Nat & String, Wr.put_list.go(~String, ~Wr.put_str, t, rest), (List.length(&2, String, t), cfr_ss_items(t, rest)), cfr_ss_put_go(t, rest)) : {Wr.put_list.step(~String, ~Wr.put_str, x, _) == (1n+List.length(&2, String, t), Wr.put_str(x, cfr_ss_items(t, rest))) : Nat & String}
      {==}

# a list of strings is its count, then its items
def cfr_ss_put(+xs: List<&2, String>, -rest: String) -> {Wr.put_list(~String, ~Wr.put_str, xs, rest) == Wr.put_nat(List.length(&2, String, xs), cfr_ss_items(xs, rest)) : String}:
  %Equal.sym(Nat & String, Wr.put_list.go(~String, ~Wr.put_str, xs, rest), (List.length(&2, String, xs), cfr_ss_items(xs, rest)), cfr_ss_put_go(xs, rest)) : {Wr.put_list.fin(_) == Wr.put_nat(List.length(&2, String, xs), cfr_ss_items(xs, rest)) : String}
  {==}

# the item loop reads back x then t
def cfr_ss_go_rt(+t: List<&2, String>, +x: String, +rest: String, +hf: {Laws.cmd_strs_all(x <> t) == True{} : Bool}) -> {Wr.get_list.go(~String, ~Wr.get_str, List.length(&2, String, t), Wr.get_str(Wr.put_str(x, cfr_ss_items(t, rest)))) == Wr.Got{x <> t, rest} : Wr.Dec<List<&2, String>>}:
  match t:
    case Nil{}:
      %Equal.sym(Wr.Dec<String>, Wr.get_str(Wr.put_str(x, rest)), Wr.Got{x, rest}, Laws.wire_str_round_trip(x, rest, PWire.wr_and_l(Laws.wire_fits(String.length(x)), True{}, hf))) : {Wr.get_list.go(~String, ~Wr.get_str, 0n, _) == Wr.Got{[x], rest} : Wr.Dec<List<&2, String>>}
      {==}
    case Con{+y, +u}:
      %Equal.sym(Wr.Dec<String>, Wr.get_str(Wr.put_str(x, Wr.put_str(y, cfr_ss_items(u, rest)))), Wr.Got{x, Wr.put_str(y, cfr_ss_items(u, rest))}, Laws.wire_str_round_trip(x, Wr.put_str(y, cfr_ss_items(u, rest)), PWire.wr_and_l(Laws.wire_fits(String.length(x)), Laws.cmd_strs_all(y <> u), hf))) : {Wr.get_list.go(~String, ~Wr.get_str, 1n+List.length(&2, String, u), _) == Wr.Got{x <> y <> u, rest} : Wr.Dec<List<&2, String>>}
      %Equal.sym(Wr.Dec<List<&2, String>>, Wr.get_list.go(~String, ~Wr.get_str, List.length(&2, String, u), Wr.get_str(Wr.put_str(y, cfr_ss_items(u, rest)))), Wr.Got{y <> u, rest}, cfr_ss_go_rt(u, y, rest, PWire.wr_and_r(Laws.wire_fits(String.length(x)), Laws.cmd_strs_all(y <> u), hf))) : {Wr.get_list.cons(String, x, _) == Wr.Got{x <> y <> u, rest} : Wr.Dec<List<&2, String>>}
      {==}

# a list of strings that fits reads back
def cfr_strs_rt(+xs: List<&2, String>, +rest: String, h: {Laws.cmd_strs_fit(xs) == True{} : Bool}) -> {FCmd.get_strs(FCmd.put_strs(xs, rest)) == Wr.Got{xs, rest} : Wr.Dec<List<&2, String>>}:
  match xs:
    case Nil{}:
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(0n, rest)), Wr.Got{0n, rest}, Laws.wire_nat_round_trip(0n, rest, {==})) : {Wr.get_list.start(~String, ~Wr.get_str, _) == Wr.Got{Nil{}, rest} : Wr.Dec<List<&2, String>>}
      {==}
    case Con{+x, +t}:
      +r = rest
      +hh = h
      %Equal.sym(String, Wr.put_list(~String, ~Wr.put_str, x <> t, r), Wr.put_nat(List.length(&2, String, x <> t), cfr_ss_items(x <> t, r)), cfr_ss_put(x <> t, r)) : {Wr.get_list(~String, ~Wr.get_str, _) == Wr.Got{x <> t, r} : Wr.Dec<List<&2, String>>}
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(List.length(&2, String, x <> t), cfr_ss_items(x <> t, r))), Wr.Got{List.length(&2, String, x <> t), cfr_ss_items(x <> t, r)}, Laws.wire_nat_round_trip(List.length(&2, String, x <> t), cfr_ss_items(x <> t, r), PWire.wr_and_l(Laws.wire_fits(List.length(&2, String, x <> t)), Laws.cmd_strs_all(x <> t), hh))) : {Wr.get_list.start(~String, ~Wr.get_str, _) == Wr.Got{x <> t, r} : Wr.Dec<List<&2, String>>}
      cfr_ss_go_rt(t, x, r, PWire.wr_and_r(Laws.wire_fits(List.length(&2, String, x <> t)), Laws.cmd_strs_all(x <> t), hh))

# ---- entries ----

# an entry that fits reads back: its path, its aliases, then three Bools
def cfr_ent_rt(+e: FCmd.EntW, +rest: String, +h: {Laws.cmd_ent_fits(e) == True{} : Bool}) -> {FCmd.get_ent(FCmd.put_ent(e, rest)) == Wr.Got{e, rest} : Wr.Dec<FCmd.EntW>}:
  match e:
    case FCmd.EntW{+p, +a, +r, +f, +g}:
      %Equal.sym(Wr.Dec<List<&2, String>>, FCmd.get_strs(FCmd.put_strs(p, FCmd.put_strs(a, Wr.put_bool(r, Wr.put_bool(f, Wr.put_bool(g, rest)))))), Wr.Got{p, FCmd.put_strs(a, Wr.put_bool(r, Wr.put_bool(f, Wr.put_bool(g, rest))))}, cfr_strs_rt(p, FCmd.put_strs(a, Wr.put_bool(r, Wr.put_bool(f, Wr.put_bool(g, rest)))), PWire.wr_and_l(Laws.cmd_strs_fit(p), Laws.cmd_strs_fit(a), h))) : {FCmd.get_ent.path(_) == Wr.Got{FCmd.EntW{p, a, r, f, g}, rest} : Wr.Dec<FCmd.EntW>}
      %Equal.sym(Wr.Dec<List<&2, String>>, FCmd.get_strs(FCmd.put_strs(a, Wr.put_bool(r, Wr.put_bool(f, Wr.put_bool(g, rest))))), Wr.Got{a, Wr.put_bool(r, Wr.put_bool(f, Wr.put_bool(g, rest)))}, cfr_strs_rt(a, Wr.put_bool(r, Wr.put_bool(f, Wr.put_bool(g, rest))), PWire.wr_and_r(Laws.cmd_strs_fit(p), Laws.cmd_strs_fit(a), h))) : {FCmd.get_ent.alias(p, _) == Wr.Got{FCmd.EntW{p, a, r, f, g}, rest} : Wr.Dec<FCmd.EntW>}
      %Equal.sym(Wr.Dec<Bool>, Wr.get_bool(Wr.put_bool(r, Wr.put_bool(f, Wr.put_bool(g, rest)))), Wr.Got{r, Wr.put_bool(f, Wr.put_bool(g, rest))}, Laws.wire_bool_round_trip(r, Wr.put_bool(f, Wr.put_bool(g, rest)))) : {FCmd.get_ent.run(p, a, _) == Wr.Got{FCmd.EntW{p, a, r, f, g}, rest} : Wr.Dec<FCmd.EntW>}
      %Equal.sym(Wr.Dec<Bool>, Wr.get_bool(Wr.put_bool(f, Wr.put_bool(g, rest))), Wr.Got{f, Wr.put_bool(g, rest)}, Laws.wire_bool_round_trip(f, Wr.put_bool(g, rest))) : {FCmd.get_ent.free(p, a, r, _) == Wr.Got{FCmd.EntW{p, a, r, f, g}, rest} : Wr.Dec<FCmd.EntW>}
      %Equal.sym(Wr.Dec<Bool>, Wr.get_bool(Wr.put_bool(g, rest)), Wr.Got{g, rest}, Laws.wire_bool_round_trip(g, rest)) : {FCmd.get_ent.arg(p, a, r, f, _) == Wr.Got{FCmd.EntW{p, a, r, f, g}, rest} : Wr.Dec<FCmd.EntW>}
      {==}

# the items of a table, then rest
def cfr_es_items(xs: List<&2, FCmd.EntW>, rest: String) -> String:
  match xs:
    case Nil{}:
      rest
    case Con{x, t}:
      FCmd.put_ent(x, cfr_es_items(t, rest))

def cfr_es_put_go(xs: List<&2, FCmd.EntW>, -rest: String) -> {Wr.put_list.go(~FCmd.EntW, ~FCmd.put_ent, xs, rest) == (List.length(&2, FCmd.EntW, xs), cfr_es_items(xs, rest)) : Nat & String}:
  match xs:
    case Nil{}:
      {==}
    case Con{x, +t}:
      %Equal.sym(Nat & String, Wr.put_list.go(~FCmd.EntW, ~FCmd.put_ent, t, rest), (List.length(&2, FCmd.EntW, t), cfr_es_items(t, rest)), cfr_es_put_go(t, rest)) : {Wr.put_list.step(~FCmd.EntW, ~FCmd.put_ent, x, _) == (1n+List.length(&2, FCmd.EntW, t), FCmd.put_ent(x, cfr_es_items(t, rest))) : Nat & String}
      {==}

# a table is its count, then its entries
def cfr_es_put(+xs: List<&2, FCmd.EntW>, -rest: String) -> {Wr.put_list(~FCmd.EntW, ~FCmd.put_ent, xs, rest) == Wr.put_nat(List.length(&2, FCmd.EntW, xs), cfr_es_items(xs, rest)) : String}:
  %Equal.sym(Nat & String, Wr.put_list.go(~FCmd.EntW, ~FCmd.put_ent, xs, rest), (List.length(&2, FCmd.EntW, xs), cfr_es_items(xs, rest)), cfr_es_put_go(xs, rest)) : {Wr.put_list.fin(_) == Wr.put_nat(List.length(&2, FCmd.EntW, xs), cfr_es_items(xs, rest)) : String}
  {==}

# the item loop reads back x then t
def cfr_es_go_rt(+t: List<&2, FCmd.EntW>, +x: FCmd.EntW, +rest: String, +hf: {Laws.cmd_ents_all(x <> t) == True{} : Bool}) -> {Wr.get_list.go(~FCmd.EntW, ~FCmd.get_ent, List.length(&2, FCmd.EntW, t), FCmd.get_ent(FCmd.put_ent(x, cfr_es_items(t, rest)))) == Wr.Got{x <> t, rest} : Wr.Dec<List<&2, FCmd.EntW>>}:
  match t:
    case Nil{}:
      %Equal.sym(Wr.Dec<FCmd.EntW>, FCmd.get_ent(FCmd.put_ent(x, rest)), Wr.Got{x, rest}, cfr_ent_rt(x, rest, PWire.wr_and_l(Laws.cmd_ent_fits(x), True{}, hf))) : {Wr.get_list.go(~FCmd.EntW, ~FCmd.get_ent, 0n, _) == Wr.Got{[x], rest} : Wr.Dec<List<&2, FCmd.EntW>>}
      {==}
    case Con{+y, +u}:
      %Equal.sym(Wr.Dec<FCmd.EntW>, FCmd.get_ent(FCmd.put_ent(x, FCmd.put_ent(y, cfr_es_items(u, rest)))), Wr.Got{x, FCmd.put_ent(y, cfr_es_items(u, rest))}, cfr_ent_rt(x, FCmd.put_ent(y, cfr_es_items(u, rest)), PWire.wr_and_l(Laws.cmd_ent_fits(x), Laws.cmd_ents_all(y <> u), hf))) : {Wr.get_list.go(~FCmd.EntW, ~FCmd.get_ent, 1n+List.length(&2, FCmd.EntW, u), _) == Wr.Got{x <> y <> u, rest} : Wr.Dec<List<&2, FCmd.EntW>>}
      %Equal.sym(Wr.Dec<List<&2, FCmd.EntW>>, Wr.get_list.go(~FCmd.EntW, ~FCmd.get_ent, List.length(&2, FCmd.EntW, u), FCmd.get_ent(FCmd.put_ent(y, cfr_es_items(u, rest)))), Wr.Got{y <> u, rest}, cfr_es_go_rt(u, y, rest, PWire.wr_and_r(Laws.cmd_ent_fits(x), Laws.cmd_ents_all(y <> u), hf))) : {Wr.get_list.cons(FCmd.EntW, x, _) == Wr.Got{x <> y <> u, rest} : Wr.Dec<List<&2, FCmd.EntW>>}
      {==}

# a table that fits reads back
def cfr_table_rt(+xs: List<&2, FCmd.EntW>, +rest: String, h: {Bool.and(Laws.wire_fits(List.length(&2, FCmd.EntW, xs)), Laws.cmd_ents_all(xs)) == True{} : Bool}) -> {FCmd.get_table(FCmd.put_table(xs, rest)) == Wr.Got{xs, rest} : Wr.Dec<List<&2, FCmd.EntW>>}:
  match xs:
    case Nil{}:
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(0n, rest)), Wr.Got{0n, rest}, Laws.wire_nat_round_trip(0n, rest, {==})) : {Wr.get_list.start(~FCmd.EntW, ~FCmd.get_ent, _) == Wr.Got{Nil{}, rest} : Wr.Dec<List<&2, FCmd.EntW>>}
      {==}
    case Con{+x, +t}:
      +r = rest
      +hh = h
      %Equal.sym(String, Wr.put_list(~FCmd.EntW, ~FCmd.put_ent, x <> t, r), Wr.put_nat(List.length(&2, FCmd.EntW, x <> t), cfr_es_items(x <> t, r)), cfr_es_put(x <> t, r)) : {Wr.get_list(~FCmd.EntW, ~FCmd.get_ent, _) == Wr.Got{x <> t, r} : Wr.Dec<List<&2, FCmd.EntW>>}
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(List.length(&2, FCmd.EntW, x <> t), cfr_es_items(x <> t, r))), Wr.Got{List.length(&2, FCmd.EntW, x <> t), cfr_es_items(x <> t, r)}, Laws.wire_nat_round_trip(List.length(&2, FCmd.EntW, x <> t), cfr_es_items(x <> t, r), PWire.wr_and_l(Laws.wire_fits(List.length(&2, FCmd.EntW, x <> t)), Laws.cmd_ents_all(x <> t), hh))) : {Wr.get_list.start(~FCmd.EntW, ~FCmd.get_ent, _) == Wr.Got{x <> t, r} : Wr.Dec<List<&2, FCmd.EntW>>}
      cfr_es_go_rt(t, x, r, PWire.wr_and_r(Laws.wire_fits(List.length(&2, FCmd.EntW, x <> t)), Laws.cmd_ents_all(x <> t), hh))

# ---- queries ----

# a row that fits reads back
def cfr_sel_rt(+x: Cmd.Sel, +rest: String, +h: {Laws.cmd_sel_fits(x) == True{} : Bool}) -> {FCmd.get_sel(FCmd.put_sel(x, rest)) == Wr.Got{x, rest} : Wr.Dec<Cmd.Sel>}:
  match x:
    case Cmd.NoRow{}:
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(0n, rest)), Wr.Got{0n, rest}, Laws.wire_nat_round_trip(0n, rest, {==})) : {FCmd.get_sel.go(_) == Wr.Got{Cmd.NoRow{}, rest} : Wr.Dec<Cmd.Sel>}
      {==}
    case Cmd.Row{+i}:
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(1n, Wr.put_nat(i, rest))), Wr.Got{1n, Wr.put_nat(i, rest)}, Laws.wire_nat_round_trip(1n, Wr.put_nat(i, rest), {==})) : {FCmd.get_sel.go(_) == Wr.Got{Cmd.Row{i}, rest} : Wr.Dec<Cmd.Sel>}
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(i, rest)), Wr.Got{i, rest}, Laws.wire_nat_round_trip(i, rest, h)) : {FCmd.get_sel.row(_) == Wr.Got{Cmd.Row{i}, rest} : Wr.Dec<Cmd.Sel>}
      {==}

# a press reads back
def cfr_press_rt(+k: Cmd.Press, +rest: String) -> {FCmd.get_press(FCmd.put_press(k, rest)) == Wr.Got{k, rest} : Wr.Dec<Cmd.Press>}:
  match k:
    case Cmd.Tab{}:
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(0n, rest)), Wr.Got{0n, rest}, Laws.wire_nat_round_trip(0n, rest, {==})) : {FCmd.get_press.go(_) == Wr.Got{Cmd.Tab{}, rest} : Wr.Dec<Cmd.Press>}
      {==}
    case Cmd.Enter{}:
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(1n, rest)), Wr.Got{1n, rest}, Laws.wire_nat_round_trip(1n, rest, {==})) : {FCmd.get_press.go(_) == Wr.Got{Cmd.Enter{}, rest} : Wr.Dec<Cmd.Press>}
      {==}

# a query that fits reads back: its tag, its line, and for a key its row
# and press
def cfr_query_rt(+q: FCmd.Query, +rest: String, +h: {Laws.cmd_query_fits(q) == True{} : Bool}) -> {FCmd.get_query(FCmd.put_query(q, rest)) == Wr.Got{q, rest} : Wr.Dec<FCmd.Query>}:
  match q:
    case FCmd.QResolve{+l}:
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(0n, Wr.put_str(l, rest))), Wr.Got{0n, Wr.put_str(l, rest)}, Laws.wire_nat_round_trip(0n, Wr.put_str(l, rest), {==})) : {FCmd.get_query.go(_) == Wr.Got{FCmd.QResolve{l}, rest} : Wr.Dec<FCmd.Query>}
      %Equal.sym(Wr.Dec<String>, Wr.get_str(Wr.put_str(l, rest)), Wr.Got{l, rest}, Laws.wire_str_round_trip(l, rest, h)) : {FCmd.get_query.resolve(_) == Wr.Got{FCmd.QResolve{l}, rest} : Wr.Dec<FCmd.Query>}
      {==}
    case FCmd.QMenu{+l}:
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(1n, Wr.put_str(l, rest))), Wr.Got{1n, Wr.put_str(l, rest)}, Laws.wire_nat_round_trip(1n, Wr.put_str(l, rest), {==})) : {FCmd.get_query.go(_) == Wr.Got{FCmd.QMenu{l}, rest} : Wr.Dec<FCmd.Query>}
      %Equal.sym(Wr.Dec<String>, Wr.get_str(Wr.put_str(l, rest)), Wr.Got{l, rest}, Laws.wire_str_round_trip(l, rest, h)) : {FCmd.get_query.menu(_) == Wr.Got{FCmd.QMenu{l}, rest} : Wr.Dec<FCmd.Query>}
      {==}
    case FCmd.QKey{+l, +x, +k}:
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(2n, Wr.put_str(l, FCmd.put_sel(x, FCmd.put_press(k, rest))))), Wr.Got{2n, Wr.put_str(l, FCmd.put_sel(x, FCmd.put_press(k, rest)))}, Laws.wire_nat_round_trip(2n, Wr.put_str(l, FCmd.put_sel(x, FCmd.put_press(k, rest))), {==})) : {FCmd.get_query.go(_) == Wr.Got{FCmd.QKey{l, x, k}, rest} : Wr.Dec<FCmd.Query>}
      %Equal.sym(Wr.Dec<String>, Wr.get_str(Wr.put_str(l, FCmd.put_sel(x, FCmd.put_press(k, rest)))), Wr.Got{l, FCmd.put_sel(x, FCmd.put_press(k, rest))}, Laws.wire_str_round_trip(l, FCmd.put_sel(x, FCmd.put_press(k, rest)), PWire.wr_and_l(Laws.wire_fits(String.length(l)), Laws.cmd_sel_fits(x), h))) : {FCmd.get_query.key(_) == Wr.Got{FCmd.QKey{l, x, k}, rest} : Wr.Dec<FCmd.Query>}
      %Equal.sym(Wr.Dec<Cmd.Sel>, FCmd.get_sel(FCmd.put_sel(x, FCmd.put_press(k, rest))), Wr.Got{x, FCmd.put_press(k, rest)}, cfr_sel_rt(x, FCmd.put_press(k, rest), PWire.wr_and_r(Laws.wire_fits(String.length(l)), Laws.cmd_sel_fits(x), h))) : {FCmd.get_query.sel(l, _) == Wr.Got{FCmd.QKey{l, x, k}, rest} : Wr.Dec<FCmd.Query>}
      %Equal.sym(Wr.Dec<Cmd.Press>, FCmd.get_press(FCmd.put_press(k, rest)), Wr.Got{k, rest}, cfr_press_rt(k, rest)) : {FCmd.get_query.press(l, x, _) == Wr.Got{FCmd.QKey{l, x, k}, rest} : Wr.Dec<FCmd.Query>}
      {==}

# ---- the request ----

# a request that fits reads back: its table, then its query
def cfr_req_rt(+r: FCmd.Req, +rest: String, +h: {Laws.cmd_req_fits(r) == True{} : Bool}) -> {FCmd.get_req(FCmd.put_req(r, rest)) == Wr.Got{r, rest} : Wr.Dec<FCmd.Req>}:
  match r:
    case FCmd.Req{+t, +q}:
      %Equal.sym(Wr.Dec<List<&2, FCmd.EntW>>, FCmd.get_table(FCmd.put_table(t, FCmd.put_query(q, rest))), Wr.Got{t, FCmd.put_query(q, rest)}, cfr_table_rt(t, FCmd.put_query(q, rest), PWire.wr_and_l(Bool.and(Laws.wire_fits(List.length(&2, FCmd.EntW, t)), Laws.cmd_ents_all(t)), Laws.cmd_query_fits(q), h))) : {FCmd.get_req.table(_) == Wr.Got{FCmd.Req{t, q}, rest} : Wr.Dec<FCmd.Req>}
      %Equal.sym(Wr.Dec<FCmd.Query>, FCmd.get_query(FCmd.put_query(q, rest)), Wr.Got{q, rest}, cfr_query_rt(q, rest, PWire.wr_and_r(Bool.and(Laws.wire_fits(List.length(&2, FCmd.EntW, t)), Laws.cmd_ents_all(t)), Laws.cmd_query_fits(q), h))) : {FCmd.get_req.query(t, _) == Wr.Got{FCmd.Req{t, q}, rest} : Wr.Dec<FCmd.Req>}
      {==}

def Laws.command_ffi_round_trip(r, rest, h):
  cfr_req_rt(r, rest, h)
