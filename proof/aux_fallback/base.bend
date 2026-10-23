# eukhe: lemmas the proofs of area aux_fallback share

import Base
import ../../bend/aux_fallback.bend as Af
import ../../bend/ffi_aux_fallback.bend as FAf
import ../../bend/wire.bend as Wr
import ../../LAWS.bend as Laws
import ../base.bend as L
import ../wire/wire_bool_round_trip.bend as PWireBoolRoundTrip

# ---- aux_fallback_wire ----

# Place after PROOF.bend section wire: the proofs use its Laws.wire_*
# fills and wr_and_l / wr_and_r.

# a Nat that fits reads back (Laws.wire_nat_round_trip, turned around)
def pfw.nat(+n: Nat, +rest: String, h: {Laws.wire_fits(n) == True{} : Bool}) -> {Wr.Got{n, rest} == Wr.get_nat(Wr.put_nat(n, rest)) : Wr.Dec<Nat>}:
  Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(n, rest)), Wr.Got{n, rest}, Laws.wire_nat_round_trip(n, rest, h))

# a Bool reads back (Laws.wire_bool_round_trip, turned around)
def pfw.bool(+b: Bool, +rest: String) -> {Wr.Got{b, rest} == Wr.get_bool(Wr.put_bool(b, rest)) : Wr.Dec<Bool>}:
  Equal.sym(Wr.Dec<Bool>, Wr.get_bool(Wr.put_bool(b, rest)), Wr.Got{b, rest}, Laws.wire_bool_round_trip(b, rest))

def Laws.afw_key_round_trip(k, rest, h):
  match k:
    case Af.K{+p, +s, +r}:
      +z = rest
      +hh = h
      +h1 = L.wr_and_r(Laws.wire_fits(p), Bool.and(Laws.wire_fits(s), Laws.wire_fits(r)), hh)
      %pfw.nat(p, Wr.put_nat(s, Wr.put_nat(r, z)), L.wr_and_l(Laws.wire_fits(p), Bool.and(Laws.wire_fits(s), Laws.wire_fits(r)), hh)) : {FAf.get_key.go(_) == Wr.Got{Af.K{p, s, r}, z} : Wr.Dec<Af.Key>}
      %pfw.nat(s, Wr.put_nat(r, z), L.wr_and_l(Laws.wire_fits(s), Laws.wire_fits(r), h1)) : {FAf.get_key.s(p, _) == Wr.Got{Af.K{p, s, r}, z} : Wr.Dec<Af.Key>}
      %pfw.nat(r, z, L.wr_and_r(Laws.wire_fits(s), Laws.wire_fits(r), h1)) : {FAf.get_key.r(p, s, _) == Wr.Got{Af.K{p, s, r}, z} : Wr.Dec<Af.Key>}
      {==}

# a key reads back (turned around for rewriting)
def pfw.key(+k: Af.Key, +rest: String, h: {Laws.afw_key_fits(k) == True{} : Bool}) -> {Wr.Got{k, rest} == FAf.get_key(FAf.put_key(k, rest)) : Wr.Dec<Af.Key>}:
  Equal.sym(Wr.Dec<Af.Key>, FAf.get_key(FAf.put_key(k, rest)), Wr.Got{k, rest}, Laws.afw_key_round_trip(k, rest, h))

# the items of xs, then rest (Af.Key; a copy of PROOF.bend wire's wr_items)
def pfw.key_items(xs: List<&2, Af.Key>, rest: String) -> String:
  match xs:
    case Nil{}:
      rest
    case Con{x, t}:
      FAf.put_key(x, pfw.key_items(t, rest))

def pfw.key_put_go(xs: List<&2, Af.Key>, -rest: String) ->
  {Wr.put_list.go(~Af.Key, ~FAf.put_key, xs, rest) == (List.length(&2, Af.Key, xs), pfw.key_items(xs, rest)) : Nat & String}:
  match xs:
    case Nil{}:
      {==}
    case Con{x, +t}:
      %Equal.sym(Nat & String, Wr.put_list.go(~Af.Key, ~FAf.put_key, t, rest), (List.length(&2, Af.Key, t), pfw.key_items(t, rest)), pfw.key_put_go(t, rest)) : {Wr.put_list.step(~Af.Key, ~FAf.put_key, x, _) == (1n+List.length(&2, Af.Key, t), FAf.put_key(x, pfw.key_items(t, rest))) : Nat & String}
      {==}

# a list is its count, then its items
def pfw.key_put(+xs: List<&2, Af.Key>, -rest: String) ->
  {Wr.put_list(~Af.Key, ~FAf.put_key, xs, rest) == Wr.put_nat(List.length(&2, Af.Key, xs), pfw.key_items(xs, rest)) : String}:
  %Equal.sym(Nat & String, Wr.put_list.go(~Af.Key, ~FAf.put_key, xs, rest), (List.length(&2, Af.Key, xs), pfw.key_items(xs, rest)), pfw.key_put_go(xs, rest)) : {Wr.put_list.fin(_) == Wr.put_nat(List.length(&2, Af.Key, xs), pfw.key_items(xs, rest)) : String}
  {==}

# the item loop reads back x then t (wr_list_go_rt for Af.Key)
def pfw.key_go_rt(+t: List<&2, Af.Key>, +x: Af.Key, +rest: String,
  +hf: {Laws.afw_keys_fit(x <> t) == True{} : Bool}) ->
  {Wr.get_list.go(~Af.Key, ~FAf.get_key, List.length(&2, Af.Key, t), FAf.get_key(FAf.put_key(x, pfw.key_items(t, rest)))) == Wr.Got{x <> t, rest} : Wr.Dec<List<&2, Af.Key>>}:
  match t:
    case Nil{}:
      %pfw.key(x, rest, L.wr_and_l(Laws.afw_key_fits(x), True{}, hf)) : {Wr.get_list.go(~Af.Key, ~FAf.get_key, 0n, _) == Wr.Got{[x], rest} : Wr.Dec<List<&2, Af.Key>>}
      {==}
    case Con{+y, +u}:
      %pfw.key(x, FAf.put_key(y, pfw.key_items(u, rest)), L.wr_and_l(Laws.afw_key_fits(x), Laws.afw_keys_fit(y <> u), hf)) : {Wr.get_list.go(~Af.Key, ~FAf.get_key, 1n+List.length(&2, Af.Key, u), _) == Wr.Got{x <> y <> u, rest} : Wr.Dec<List<&2, Af.Key>>}
      %Equal.sym(Wr.Dec<List<&2, Af.Key>>, Wr.get_list.go(~Af.Key, ~FAf.get_key, List.length(&2, Af.Key, u), FAf.get_key(FAf.put_key(y, pfw.key_items(u, rest)))), Wr.Got{y <> u, rest}, pfw.key_go_rt(u, y, rest, L.wr_and_r(Laws.afw_key_fits(x), Laws.afw_keys_fit(y <> u), hf))) : {Wr.get_list.cons(Af.Key, x, _) == Wr.Got{x <> y <> u, rest} : Wr.Dec<List<&2, Af.Key>>}
      {==}

def Laws.afw_keys_round_trip(xs, rest, h):
  match xs:
    case Nil{}:
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(0n, rest)), Wr.Got{0n, rest}, Laws.wire_nat_round_trip(0n, rest, L.wr_and_l(Laws.wire_fits(0n), True{}, h))) : {Wr.get_list.start(~Af.Key, ~FAf.get_key, _) == Wr.Got{Nil{}, rest} : Wr.Dec<List<&2, Af.Key>>}
      {==}
    case Con{+x, +t}:
      +r = rest
      +hh = h
      %Equal.sym(String, Wr.put_list(~Af.Key, ~FAf.put_key, x <> t, r), Wr.put_nat(List.length(&2, Af.Key, x <> t), pfw.key_items(x <> t, r)), pfw.key_put(x <> t, r)) : {Wr.get_list(~Af.Key, ~FAf.get_key, _) == Wr.Got{x <> t, r} : Wr.Dec<List<&2, Af.Key>>}
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(List.length(&2, Af.Key, x <> t), pfw.key_items(x <> t, r))), Wr.Got{List.length(&2, Af.Key, x <> t), pfw.key_items(x <> t, r)}, Laws.wire_nat_round_trip(List.length(&2, Af.Key, x <> t), pfw.key_items(x <> t, r), L.wr_and_l(Laws.wire_fits(List.length(&2, Af.Key, x <> t)), Laws.afw_keys_fit(x <> t), hh))) : {Wr.get_list.start(~Af.Key, ~FAf.get_key, _) == Wr.Got{x <> t, r} : Wr.Dec<List<&2, Af.Key>>}
      pfw.key_go_rt(t, x, r, L.wr_and_r(Laws.wire_fits(List.length(&2, Af.Key, x <> t)), Laws.afw_keys_fit(x <> t), hh))

# a list that fits reads back (turned around for rewriting)
def pfw.keys(+xs: List<&2, Af.Key>, +rest: String, h: {Bool.and(Laws.wire_fits(List.length(&2, Af.Key, xs)), Laws.afw_keys_fit(xs)) == True{} : Bool}) ->
  {Wr.Got{xs, rest} == Wr.get_list(~Af.Key, ~FAf.get_key, Wr.put_list(~Af.Key, ~FAf.put_key, xs, rest)) : Wr.Dec<List<&2, Af.Key>>}:
  Equal.sym(Wr.Dec<List<&2, Af.Key>>, Wr.get_list(~Af.Key, ~FAf.get_key, Wr.put_list(~Af.Key, ~FAf.put_key, xs, rest)), Wr.Got{xs, rest}, Laws.afw_keys_round_trip(xs, rest, h))

def Laws.afw_route_round_trip(r, rest, h):
  match r:
    case Af.Session{}:
      {==}
    case Af.Routed{}:
      {==}
    case Af.Fallback{+k}:
      %pfw.key(k, rest, h) : {FAf.get_route.fallback(_) == Wr.Got{Af.Fallback{k}, rest} : Wr.Dec<Af.Route>}
      {==}

# a route reads back (turned around for rewriting)
def pfw.route(+r: Af.Route, +rest: String, h: {Laws.afw_route_fits(r) == True{} : Bool}) -> {Wr.Got{r, rest} == FAf.get_route(FAf.put_route(r, rest)) : Wr.Dec<Af.Route>}:
  Equal.sym(Wr.Dec<Af.Route>, FAf.get_route(FAf.put_route(r, rest)), Wr.Got{r, rest}, Laws.afw_route_round_trip(r, rest, h))

def Laws.afw_gate_round_trip(g, rest, h):
  match g:
    case Af.Known{+r}:
      %pfw.route(r, rest, h) : {FAf.get_gate.known(_) == Wr.Got{Af.Known{r}, rest} : Wr.Dec<Af.Gate>}
      {==}
    case Af.Lookup{+p, +s}:
      +z = rest
      +hh = h
      %pfw.nat(p, Wr.put_nat(s, z), L.wr_and_l(Laws.wire_fits(p), Laws.wire_fits(s), hh)) : {FAf.get_gate.p(_) == Wr.Got{Af.Lookup{p, s}, z} : Wr.Dec<Af.Gate>}
      %pfw.nat(s, z, L.wr_and_r(Laws.wire_fits(p), Laws.wire_fits(s), hh)) : {FAf.get_gate.s(p, _) == Wr.Got{Af.Lookup{p, s}, z} : Wr.Dec<Af.Gate>}
      {==}

# a gate reads back (turned around for rewriting)
def pfw.gate(+g: Af.Gate, +rest: String, h: {Laws.afw_gate_fits(g) == True{} : Bool}) -> {Wr.Got{g, rest} == FAf.get_gate(FAf.put_gate(g, rest)) : Wr.Dec<Af.Gate>}:
  Equal.sym(Wr.Dec<Af.Gate>, FAf.get_gate(FAf.put_gate(g, rest)), Wr.Got{g, rest}, Laws.afw_gate_round_trip(g, rest, h))

def Laws.afw_sel_round_trip(x, rest, h):
  match x:
    case Af.Unset{}:
      {==}
    case Af.Same{}:
      {==}
    case Af.Other{+s}:
      %pfw.nat(s, rest, h) : {FAf.get_sel.other(_) == Wr.Got{Af.Other{s}, rest} : Wr.Dec<Af.Sel>}
      {==}

# a sel reads back (turned around for rewriting)
def pfw.sel(+x: Af.Sel, +rest: String, h: {Laws.afw_sel_fits(x) == True{} : Bool}) -> {Wr.Got{x, rest} == FAf.get_sel(FAf.put_sel(x, rest)) : Wr.Dec<Af.Sel>}:
  Equal.sym(Wr.Dec<Af.Sel>, FAf.get_sel(FAf.put_sel(x, rest)), Wr.Got{x, rest}, Laws.afw_sel_round_trip(x, rest, h))

def Laws.afw_look_round_trip(x, rest, h):
  match x:
    case Af.Miss{+r}:
      %pfw.nat(r, rest, h) : {FAf.get_look.tag(_, 0n) == Wr.Got{Af.Miss{r}, rest} : Wr.Dec<Af.Look>}
      {==}
    case Af.Hit{+w}:
      %pfw.nat(w, rest, h) : {FAf.get_look.tag(_, 1n) == Wr.Got{Af.Hit{w}, rest} : Wr.Dec<Af.Look>}
      {==}

# a look reads back (turned around for rewriting)
def pfw.look(+x: Af.Look, +rest: String, h: {Laws.afw_look_fits(x) == True{} : Bool}) -> {Wr.Got{x, rest} == FAf.get_look(FAf.put_look(x, rest)) : Wr.Dec<Af.Look>}:
  Equal.sym(Wr.Dec<Af.Look>, FAf.get_look(FAf.put_look(x, rest)), Wr.Got{x, rest}, Laws.afw_look_round_trip(x, rest, h))

def Laws.afw_req_round_trip(x, rest, h):
  match x:
    case FAf.GateReq{+p, +sel, +ok}:
      +z = rest
      +hh = h
      %pfw.nat(p, FAf.put_sel(sel, Wr.put_bool(ok, z)), L.wr_and_l(Laws.wire_fits(p), Laws.afw_sel_fits(sel), hh)) : {FAf.get_req.gate(_) == Wr.Got{FAf.GateReq{p, sel, ok}, z} : Wr.Dec<FAf.Req>}
      %pfw.sel(sel, Wr.put_bool(ok, z), L.wr_and_r(Laws.wire_fits(p), Laws.afw_sel_fits(sel), hh)) : {FAf.get_req.sel(p, _) == Wr.Got{FAf.GateReq{p, sel, ok}, z} : Wr.Dec<FAf.Req>}
      %pfw.bool(ok, z) : {FAf.get_req.ok(p, sel, _) == Wr.Got{FAf.GateReq{p, sel, ok}, z} : Wr.Dec<FAf.Req>}
      {==}
    case FAf.SettleReq{+g, +look, +need}:
      +z = rest
      +hh = h
      +h1 = L.wr_and_r(Laws.afw_gate_fits(g), Bool.and(Laws.afw_look_fits(look), Laws.wire_fits(need)), hh)
      %pfw.gate(g, FAf.put_look(look, Wr.put_nat(need, z)), L.wr_and_l(Laws.afw_gate_fits(g), Bool.and(Laws.afw_look_fits(look), Laws.wire_fits(need)), hh)) : {FAf.get_req.settle(_) == Wr.Got{FAf.SettleReq{g, look, need}, z} : Wr.Dec<FAf.Req>}
      %pfw.look(look, Wr.put_nat(need, z), L.wr_and_l(Laws.afw_look_fits(look), Laws.wire_fits(need), h1)) : {FAf.get_req.look(g, _) == Wr.Got{FAf.SettleReq{g, look, need}, z} : Wr.Dec<FAf.Req>}
      %pfw.nat(need, z, L.wr_and_r(Laws.afw_look_fits(look), Laws.wire_fits(need), h1)) : {FAf.get_req.need(g, look, _) == Wr.Got{FAf.SettleReq{g, look, need}, z} : Wr.Dec<FAf.Req>}
      {==}
    case FAf.PassReq{+r, +sh}:
      +z = rest
      +hh = h
      +lt = Bool.and(Laws.wire_fits(List.length(&2, Af.Key, sh)), Laws.afw_keys_fit(sh))
      %pfw.route(r, Wr.put_list(~Af.Key, ~FAf.put_key, sh, z), L.wr_and_l(Laws.afw_route_fits(r), lt, hh)) : {FAf.get_req.pass(_) == Wr.Got{FAf.PassReq{r, sh}, z} : Wr.Dec<FAf.Req>}
      %pfw.keys(sh, z, L.wr_and_r(Laws.afw_route_fits(r), lt, hh)) : {FAf.get_req.shown(r, _) == Wr.Got{FAf.PassReq{r, sh}, z} : Wr.Dec<FAf.Req>}
      {==}

# a req reads back (turned around for rewriting)
def pfw.req(+x: FAf.Req, +rest: String, h: {Laws.afw_req_fits(x) == True{} : Bool}) -> {Wr.Got{x, rest} == FAf.get_req(FAf.put_req(x, rest)) : Wr.Dec<FAf.Req>}:
  Equal.sym(Wr.Dec<FAf.Req>, FAf.get_req(FAf.put_req(x, rest)), Wr.Got{x, rest}, Laws.afw_req_round_trip(x, rest, h))
