# eukhe: lemmas of the entry proofs of area context_order: spelled
# requests read back
#
# Each decoder of bend/ffi_context_order.bend reads the spec's spelling
# (laws/context_order.bend spell_*) of a value whose numbers fit back,
# and leaves the rest untouched: the facts, the lists (one loop per item
# type, cot.<l>.go_rt), the questions (cot.req).

import Base
import ../../../bend/context_order.bend as Co
import ../../../bend/ffi_context_order.bend as FCo
import ../../../bend/wire.bend as Wr
import ../../../laws/base.bend as LawsBase
import ../../../laws/wire.bend as Wire
import ../../../laws/context_order.bend as ContextOrder
import ../base.bend as LACo

def cot.nat(+n: Nat, +rest: String, h: {LawsBase.wire_fits(n) == True{} : Bool}) -> {Wr.Got{n, rest} == Wr.get_nat(Wr.put_nat(n, rest)) : Wr.Dec<Nat>}:
  Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(n, rest)), Wr.Got{n, rest}, Wire.wire_nat_round_trip(n, rest, h))

def cot.bool(+b: Bool, +rest: String) -> {Wr.Got{b, rest} == Wr.get_bool(Wr.put_bool(b, rest)) : Wr.Dec<Bool>}:
  Equal.sym(Wr.Dec<Bool>, Wr.get_bool(Wr.put_bool(b, rest)), Wr.Got{b, rest}, Wire.wire_bool_round_trip(b, rest))

def cot.stop(s: Co.Stop, +rest: String) -> {FCo.get_stop(ContextOrder.spell_stop(s, rest)) == Wr.Got{s, rest} : Wr.Dec<Co.Stop>}:
  match s:
    case Co.SPending{}:
      %cot.nat(0n, rest, {==}) : {FCo.get_stop.tag(_) == Wr.Got{Co.SPending{}, rest} : Wr.Dec<Co.Stop>}
      {==}
    case Co.SStop{}:
      %cot.nat(1n, rest, {==}) : {FCo.get_stop.tag(_) == Wr.Got{Co.SStop{}, rest} : Wr.Dec<Co.Stop>}
      {==}
    case Co.SLength{}:
      %cot.nat(2n, rest, {==}) : {FCo.get_stop.tag(_) == Wr.Got{Co.SLength{}, rest} : Wr.Dec<Co.Stop>}
      {==}
    case Co.SToolUse{}:
      %cot.nat(3n, rest, {==}) : {FCo.get_stop.tag(_) == Wr.Got{Co.SToolUse{}, rest} : Wr.Dec<Co.Stop>}
      {==}
    case Co.SError{}:
      %cot.nat(4n, rest, {==}) : {FCo.get_stop.tag(_) == Wr.Got{Co.SError{}, rest} : Wr.Dec<Co.Stop>}
      {==}
    case Co.SAborted{}:
      %cot.nat(5n, rest, {==}) : {FCo.get_stop.tag(_) == Wr.Got{Co.SAborted{}, rest} : Wr.Dec<Co.Stop>}
      {==}
    case Co.SDeferred{}:
      %cot.nat(6n, rest, {==}) : {FCo.get_stop.tag(_) == Wr.Got{Co.SDeferred{}, rest} : Wr.Dec<Co.Stop>}
      {==}

def cot.role(x: Co.Role, +rest: String) -> {FCo.get_role(ContextOrder.spell_role(x, rest)) == Wr.Got{x, rest} : Wr.Dec<Co.Role>}:
  match x:
    case Co.RUser{}:
      %cot.nat(0n, rest, {==}) : {FCo.get_role.tag(_) == Wr.Got{Co.RUser{}, rest} : Wr.Dec<Co.Role>}
      {==}
    case Co.RSystem{}:
      %cot.nat(1n, rest, {==}) : {FCo.get_role.tag(_) == Wr.Got{Co.RSystem{}, rest} : Wr.Dec<Co.Role>}
      {==}
    case Co.RAsst{}:
      %cot.nat(2n, rest, {==}) : {FCo.get_role.tag(_) == Wr.Got{Co.RAsst{}, rest} : Wr.Dec<Co.Role>}
      {==}
    case Co.RRes{}:
      %cot.nat(3n, rest, {==}) : {FCo.get_role.tag(_) == Wr.Got{Co.RRes{}, rest} : Wr.Dec<Co.Role>}
      {==}

def cot.msg(m: Co.Msg, +rest: String, +h: {ContextOrder.msg_fits(m) == True{} : Bool}) -> {FCo.get_msg(ContextOrder.spell_msg(m, rest)) == Wr.Got{m, rest} : Wr.Dec<Co.Msg>}:
  match m:
    case Co.MUser{}:
      %cot.nat(0n, rest, {==}) : {FCo.get_msg.tag(_) == Wr.Got{Co.MUser{}, rest} : Wr.Dec<Co.Msg>}
      {==}
    case Co.MSystem{}:
      %cot.nat(1n, rest, {==}) : {FCo.get_msg.tag(_) == Wr.Got{Co.MSystem{}, rest} : Wr.Dec<Co.Msg>}
      {==}
    case Co.MAsst{+s, +cs}:
      %cot.nat(2n, ContextOrder.spell_stop(s, LawsBase.wire_spell_nats(cs, rest)), {==}) : {FCo.get_msg.tag(_) == Wr.Got{Co.MAsst{s, cs}, rest} : Wr.Dec<Co.Msg>}
      %Equal.sym(Wr.Dec<Co.Stop>, FCo.get_stop(ContextOrder.spell_stop(s, LawsBase.wire_spell_nats(cs, rest))), Wr.Got{s, LawsBase.wire_spell_nats(cs, rest)}, cot.stop(s, LawsBase.wire_spell_nats(cs, rest))) : {FCo.get_msg.stop(_) == Wr.Got{Co.MAsst{s, cs}, rest} : Wr.Dec<Co.Msg>}
      %Wire.wire_nats_spells(cs, rest) : {FCo.get_msg.calls(s, Wr.get_list(~Nat, ~Wr.get_nat, _)) == Wr.Got{Co.MAsst{s, cs}, rest} : Wr.Dec<Co.Msg>}
      %Equal.sym(Wr.Dec<List<&2, Nat>>, Wr.get_list(~Nat, ~Wr.get_nat, Wr.put_list(~Nat, ~Wr.put_nat, cs, rest)), Wr.Got{cs, rest}, Wire.wire_list_round_trip(cs, rest, h)) : {FCo.get_msg.calls(s, _) == Wr.Got{Co.MAsst{s, cs}, rest} : Wr.Dec<Co.Msg>}
      {==}
    case Co.MRes{+c}:
      %cot.nat(3n, Wr.put_nat(c, rest), {==}) : {FCo.get_msg.tag(_) == Wr.Got{Co.MRes{c}, rest} : Wr.Dec<Co.Msg>}
      %cot.nat(c, rest, h) : {FCo.get_msg.res(_) == Wr.Got{Co.MRes{c}, rest} : Wr.Dec<Co.Msg>}
      {==}

# a spelled list of Co.Msg whose count and items fit reads back
def cot.ml.go_rt(+t: List<&2, Co.Msg>, +x: Co.Msg, +rest: String, +h: {ContextOrder.msgs_all(x <> t) == True{} : Bool}) -> {Wr.get_list.go(~Co.Msg, ~FCo.get_msg, List.length(&2, Co.Msg, t), FCo.get_msg(ContextOrder.spell_msg(x, ContextOrder.spell_msgs.items(t, rest)))) == Wr.Got{x <> t, rest} : Wr.Dec<List<&2, Co.Msg>>}:
  match t:
    case Nil{}:
      %Equal.sym(Wr.Dec<Co.Msg>, FCo.get_msg(ContextOrder.spell_msg(x, rest)), Wr.Got{x, rest}, cot.msg(x, rest, LACo.co.and_l(ContextOrder.msg_fits(x), ContextOrder.msgs_all([]), h))) : {Wr.get_list.go(~Co.Msg, ~FCo.get_msg, 0n, _) == Wr.Got{[x], rest} : Wr.Dec<List<&2, Co.Msg>>}
      {==}
    case Con{+y, +u}:
      +r2 = ContextOrder.spell_msg(y, ContextOrder.spell_msgs.items(u, rest))
      %Equal.sym(Wr.Dec<Co.Msg>, FCo.get_msg(ContextOrder.spell_msg(x, r2)), Wr.Got{x, r2}, cot.msg(x, r2, LACo.co.and_l(ContextOrder.msg_fits(x), ContextOrder.msgs_all(y <> u), h))) : {Wr.get_list.go(~Co.Msg, ~FCo.get_msg, 1n+List.length(&2, Co.Msg, u), _) == Wr.Got{x <> y <> u, rest} : Wr.Dec<List<&2, Co.Msg>>}
      %Equal.sym(Wr.Dec<List<&2, Co.Msg>>, Wr.get_list.go(~Co.Msg, ~FCo.get_msg, List.length(&2, Co.Msg, u), FCo.get_msg(r2)), Wr.Got{y <> u, rest}, cot.ml.go_rt(u, y, rest, LACo.co.and_r(ContextOrder.msg_fits(x), ContextOrder.msgs_all(y <> u), h))) : {Wr.get_list.cons(Co.Msg, x, _) == Wr.Got{x <> y <> u, rest} : Wr.Dec<List<&2, Co.Msg>>}
      {==}

def cot.ml.rt(+xs: List<&2, Co.Msg>, +r: String, +h: {Bool.and(LawsBase.wire_fits(List.length(&2, Co.Msg, xs)), ContextOrder.msgs_all(xs)) == True{} : Bool}) -> {Wr.get_list(~Co.Msg, ~FCo.get_msg, Wr.put_nat(List.length(&2, Co.Msg, xs), ContextOrder.spell_msgs.items(xs, r))) == Wr.Got{xs, r} : Wr.Dec<List<&2, Co.Msg>>}:
  match xs:
    case Nil{}:
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(0n, r)), Wr.Got{0n, r}, Wire.wire_nat_round_trip(0n, r, {==})) : {Wr.get_list.start(~Co.Msg, ~FCo.get_msg, _) == Wr.Got{Nil{}, r} : Wr.Dec<List<&2, Co.Msg>>}
      {==}
    case Con{+x, +t}:
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(List.length(&2, Co.Msg, x <> t), ContextOrder.spell_msgs.items(x <> t, r))), Wr.Got{List.length(&2, Co.Msg, x <> t), ContextOrder.spell_msgs.items(x <> t, r)}, Wire.wire_nat_round_trip(List.length(&2, Co.Msg, x <> t), ContextOrder.spell_msgs.items(x <> t, r), LACo.co.and_l(LawsBase.wire_fits(List.length(&2, Co.Msg, x <> t)), ContextOrder.msgs_all(x <> t), h))) : {Wr.get_list.start(~Co.Msg, ~FCo.get_msg, _) == Wr.Got{x <> t, r} : Wr.Dec<List<&2, Co.Msg>>}
      cot.ml.go_rt(t, x, r, LACo.co.and_r(LawsBase.wire_fits(List.length(&2, Co.Msg, x <> t)), ContextOrder.msgs_all(x <> t), h))

# a spelled list of roles whose count fits reads back
def cot.rl.go_rt(+t: List<&2, Co.Role>, +x: Co.Role, +rest: String) -> {Wr.get_list.go(~Co.Role, ~FCo.get_role, List.length(&2, Co.Role, t), FCo.get_role(ContextOrder.spell_role(x, ContextOrder.spell_roles.items(t, rest)))) == Wr.Got{x <> t, rest} : Wr.Dec<List<&2, Co.Role>>}:
  match t:
    case Nil{}:
      %Equal.sym(Wr.Dec<Co.Role>, FCo.get_role(ContextOrder.spell_role(x, rest)), Wr.Got{x, rest}, cot.role(x, rest)) : {Wr.get_list.go(~Co.Role, ~FCo.get_role, 0n, _) == Wr.Got{[x], rest} : Wr.Dec<List<&2, Co.Role>>}
      {==}
    case Con{+y, +u}:
      +r2 = ContextOrder.spell_role(y, ContextOrder.spell_roles.items(u, rest))
      %Equal.sym(Wr.Dec<Co.Role>, FCo.get_role(ContextOrder.spell_role(x, r2)), Wr.Got{x, r2}, cot.role(x, r2)) : {Wr.get_list.go(~Co.Role, ~FCo.get_role, 1n+List.length(&2, Co.Role, u), _) == Wr.Got{x <> y <> u, rest} : Wr.Dec<List<&2, Co.Role>>}
      %Equal.sym(Wr.Dec<List<&2, Co.Role>>, Wr.get_list.go(~Co.Role, ~FCo.get_role, List.length(&2, Co.Role, u), FCo.get_role(r2)), Wr.Got{y <> u, rest}, cot.rl.go_rt(u, y, rest)) : {Wr.get_list.cons(Co.Role, x, _) == Wr.Got{x <> y <> u, rest} : Wr.Dec<List<&2, Co.Role>>}
      {==}

def cot.rl.rt(+xs: List<&2, Co.Role>, +r: String, +h: {LawsBase.wire_fits(List.length(&2, Co.Role, xs)) == True{} : Bool}) -> {Wr.get_list(~Co.Role, ~FCo.get_role, Wr.put_nat(List.length(&2, Co.Role, xs), ContextOrder.spell_roles.items(xs, r))) == Wr.Got{xs, r} : Wr.Dec<List<&2, Co.Role>>}:
  match xs:
    case Nil{}:
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(0n, r)), Wr.Got{0n, r}, Wire.wire_nat_round_trip(0n, r, {==})) : {Wr.get_list.start(~Co.Role, ~FCo.get_role, _) == Wr.Got{Nil{}, r} : Wr.Dec<List<&2, Co.Role>>}
      {==}
    case Con{+x, +t}:
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(List.length(&2, Co.Role, x <> t), ContextOrder.spell_roles.items(x <> t, r))), Wr.Got{List.length(&2, Co.Role, x <> t), ContextOrder.spell_roles.items(x <> t, r)}, Wire.wire_nat_round_trip(List.length(&2, Co.Role, x <> t), ContextOrder.spell_roles.items(x <> t, r), h)) : {Wr.get_list.start(~Co.Role, ~FCo.get_role, _) == Wr.Got{x <> t, r} : Wr.Dec<List<&2, Co.Role>>}
      cot.rl.go_rt(t, x, r)

def cot.edit(e: Co.Edit, +rest: String, +h: {ContextOrder.edit_fits(e) == True{} : Bool}) -> {FCo.get_edit(ContextOrder.spell_edit(e, rest)) == Wr.Got{e, rest} : Wr.Dec<Co.Edit>}:
  match e:
    case Co.NoEdit{}:
      %cot.nat(0n, rest, {==}) : {FCo.get_edit.tag(_) == Wr.Got{Co.NoEdit{}, rest} : Wr.Dec<Co.Edit>}
      {==}
    case Co.Omit{}:
      %cot.nat(1n, rest, {==}) : {FCo.get_edit.tag(_) == Wr.Got{Co.Omit{}, rest} : Wr.Dec<Co.Edit>}
      {==}
    case Co.Replace{+ms}:
      %cot.nat(2n, ContextOrder.spell_msgs(ms, rest), {==}) : {FCo.get_edit.tag(_) == Wr.Got{Co.Replace{ms}, rest} : Wr.Dec<Co.Edit>}
      %Equal.sym(Wr.Dec<List<&2, Co.Msg>>, FCo.get_msgs(ContextOrder.spell_msgs(ms, rest)), Wr.Got{ms, rest}, cot.ml.rt(ms, rest, h)) : {FCo.get_edit.ms(_) == Wr.Got{Co.Replace{ms}, rest} : Wr.Dec<Co.Edit>}
      {==}

def cot.ent(e: Co.Ent, +rest: String, +h: {ContextOrder.ent_fits(e) == True{} : Bool}) -> {FCo.get_ent(ContextOrder.spell_ent(e, rest)) == Wr.Got{e, rest} : Wr.Dec<Co.Ent>}:
  match e:
    case Co.Ent{+hd, +ed, +own}:
      %cot.bool(hd, ContextOrder.spell_edit(ed, ContextOrder.spell_msgs(own, rest))) : {FCo.get_ent.head(_) == Wr.Got{Co.Ent{hd, ed, own}, rest} : Wr.Dec<Co.Ent>}
      %Equal.sym(Wr.Dec<Co.Edit>, FCo.get_edit(ContextOrder.spell_edit(ed, ContextOrder.spell_msgs(own, rest))), Wr.Got{ed, ContextOrder.spell_msgs(own, rest)}, cot.edit(ed, ContextOrder.spell_msgs(own, rest), LACo.co.and_l(ContextOrder.edit_fits(ed), ContextOrder.msgs_fit(own), h))) : {FCo.get_ent.edit(hd, _) == Wr.Got{Co.Ent{hd, ed, own}, rest} : Wr.Dec<Co.Ent>}
      %Equal.sym(Wr.Dec<List<&2, Co.Msg>>, FCo.get_msgs(ContextOrder.spell_msgs(own, rest)), Wr.Got{own, rest}, cot.ml.rt(own, rest, LACo.co.and_r(ContextOrder.edit_fits(ed), ContextOrder.msgs_fit(own), h))) : {FCo.get_ent.own(hd, ed, _) == Wr.Got{Co.Ent{hd, ed, own}, rest} : Wr.Dec<Co.Ent>}
      {==}

def cot.add(a: Co.Add, +rest: String, +h: {ContextOrder.add_fits(a) == True{} : Bool}) -> {FCo.get_add(ContextOrder.spell_add(a, rest)) == Wr.Got{a, rest} : Wr.Dec<Co.Add>}:
  match a:
    case Co.Add{+x, +hd, +d, +own}:
      %cot.bool(x, Wr.put_bool(hd, Wr.put_bool(d, ContextOrder.spell_msgs(own, rest)))) : {FCo.get_add.edits(_) == Wr.Got{Co.Add{x, hd, d, own}, rest} : Wr.Dec<Co.Add>}
      %cot.bool(hd, Wr.put_bool(d, ContextOrder.spell_msgs(own, rest))) : {FCo.get_add.head(x, _) == Wr.Got{Co.Add{x, hd, d, own}, rest} : Wr.Dec<Co.Add>}
      %cot.bool(d, ContextOrder.spell_msgs(own, rest)) : {FCo.get_add.edited(x, hd, _) == Wr.Got{Co.Add{x, hd, d, own}, rest} : Wr.Dec<Co.Add>}
      %Equal.sym(Wr.Dec<List<&2, Co.Msg>>, FCo.get_msgs(ContextOrder.spell_msgs(own, rest)), Wr.Got{own, rest}, cot.ml.rt(own, rest, h)) : {FCo.get_add.own(x, hd, d, _) == Wr.Got{Co.Add{x, hd, d, own}, rest} : Wr.Dec<Co.Add>}
      {==}

# a spelled list of Co.Ent whose count and items fit reads back
def cot.el.go_rt(+t: List<&2, Co.Ent>, +x: Co.Ent, +rest: String, +h: {ContextOrder.ents_all(x <> t) == True{} : Bool}) -> {Wr.get_list.go(~Co.Ent, ~FCo.get_ent, List.length(&2, Co.Ent, t), FCo.get_ent(ContextOrder.spell_ent(x, ContextOrder.spell_ents.items(t, rest)))) == Wr.Got{x <> t, rest} : Wr.Dec<List<&2, Co.Ent>>}:
  match t:
    case Nil{}:
      %Equal.sym(Wr.Dec<Co.Ent>, FCo.get_ent(ContextOrder.spell_ent(x, rest)), Wr.Got{x, rest}, cot.ent(x, rest, LACo.co.and_l(ContextOrder.ent_fits(x), ContextOrder.ents_all([]), h))) : {Wr.get_list.go(~Co.Ent, ~FCo.get_ent, 0n, _) == Wr.Got{[x], rest} : Wr.Dec<List<&2, Co.Ent>>}
      {==}
    case Con{+y, +u}:
      +r2 = ContextOrder.spell_ent(y, ContextOrder.spell_ents.items(u, rest))
      %Equal.sym(Wr.Dec<Co.Ent>, FCo.get_ent(ContextOrder.spell_ent(x, r2)), Wr.Got{x, r2}, cot.ent(x, r2, LACo.co.and_l(ContextOrder.ent_fits(x), ContextOrder.ents_all(y <> u), h))) : {Wr.get_list.go(~Co.Ent, ~FCo.get_ent, 1n+List.length(&2, Co.Ent, u), _) == Wr.Got{x <> y <> u, rest} : Wr.Dec<List<&2, Co.Ent>>}
      %Equal.sym(Wr.Dec<List<&2, Co.Ent>>, Wr.get_list.go(~Co.Ent, ~FCo.get_ent, List.length(&2, Co.Ent, u), FCo.get_ent(r2)), Wr.Got{y <> u, rest}, cot.el.go_rt(u, y, rest, LACo.co.and_r(ContextOrder.ent_fits(x), ContextOrder.ents_all(y <> u), h))) : {Wr.get_list.cons(Co.Ent, x, _) == Wr.Got{x <> y <> u, rest} : Wr.Dec<List<&2, Co.Ent>>}
      {==}

def cot.el.rt(+xs: List<&2, Co.Ent>, +r: String, +h: {Bool.and(LawsBase.wire_fits(List.length(&2, Co.Ent, xs)), ContextOrder.ents_all(xs)) == True{} : Bool}) -> {Wr.get_list(~Co.Ent, ~FCo.get_ent, Wr.put_nat(List.length(&2, Co.Ent, xs), ContextOrder.spell_ents.items(xs, r))) == Wr.Got{xs, r} : Wr.Dec<List<&2, Co.Ent>>}:
  match xs:
    case Nil{}:
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(0n, r)), Wr.Got{0n, r}, Wire.wire_nat_round_trip(0n, r, {==})) : {Wr.get_list.start(~Co.Ent, ~FCo.get_ent, _) == Wr.Got{Nil{}, r} : Wr.Dec<List<&2, Co.Ent>>}
      {==}
    case Con{+x, +t}:
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(List.length(&2, Co.Ent, x <> t), ContextOrder.spell_ents.items(x <> t, r))), Wr.Got{List.length(&2, Co.Ent, x <> t), ContextOrder.spell_ents.items(x <> t, r)}, Wire.wire_nat_round_trip(List.length(&2, Co.Ent, x <> t), ContextOrder.spell_ents.items(x <> t, r), LACo.co.and_l(LawsBase.wire_fits(List.length(&2, Co.Ent, x <> t)), ContextOrder.ents_all(x <> t), h))) : {Wr.get_list.start(~Co.Ent, ~FCo.get_ent, _) == Wr.Got{x <> t, r} : Wr.Dec<List<&2, Co.Ent>>}
      cot.el.go_rt(t, x, r, LACo.co.and_r(LawsBase.wire_fits(List.length(&2, Co.Ent, x <> t)), ContextOrder.ents_all(x <> t), h))

# a spelled list of Co.Add whose count and items fit reads back
def cot.al.go_rt(+t: List<&2, Co.Add>, +x: Co.Add, +rest: String, +h: {ContextOrder.adds_all(x <> t) == True{} : Bool}) -> {Wr.get_list.go(~Co.Add, ~FCo.get_add, List.length(&2, Co.Add, t), FCo.get_add(ContextOrder.spell_add(x, ContextOrder.spell_adds.items(t, rest)))) == Wr.Got{x <> t, rest} : Wr.Dec<List<&2, Co.Add>>}:
  match t:
    case Nil{}:
      %Equal.sym(Wr.Dec<Co.Add>, FCo.get_add(ContextOrder.spell_add(x, rest)), Wr.Got{x, rest}, cot.add(x, rest, LACo.co.and_l(ContextOrder.add_fits(x), ContextOrder.adds_all([]), h))) : {Wr.get_list.go(~Co.Add, ~FCo.get_add, 0n, _) == Wr.Got{[x], rest} : Wr.Dec<List<&2, Co.Add>>}
      {==}
    case Con{+y, +u}:
      +r2 = ContextOrder.spell_add(y, ContextOrder.spell_adds.items(u, rest))
      %Equal.sym(Wr.Dec<Co.Add>, FCo.get_add(ContextOrder.spell_add(x, r2)), Wr.Got{x, r2}, cot.add(x, r2, LACo.co.and_l(ContextOrder.add_fits(x), ContextOrder.adds_all(y <> u), h))) : {Wr.get_list.go(~Co.Add, ~FCo.get_add, 1n+List.length(&2, Co.Add, u), _) == Wr.Got{x <> y <> u, rest} : Wr.Dec<List<&2, Co.Add>>}
      %Equal.sym(Wr.Dec<List<&2, Co.Add>>, Wr.get_list.go(~Co.Add, ~FCo.get_add, List.length(&2, Co.Add, u), FCo.get_add(r2)), Wr.Got{y <> u, rest}, cot.al.go_rt(u, y, rest, LACo.co.and_r(ContextOrder.add_fits(x), ContextOrder.adds_all(y <> u), h))) : {Wr.get_list.cons(Co.Add, x, _) == Wr.Got{x <> y <> u, rest} : Wr.Dec<List<&2, Co.Add>>}
      {==}

def cot.al.rt(+xs: List<&2, Co.Add>, +r: String, +h: {Bool.and(LawsBase.wire_fits(List.length(&2, Co.Add, xs)), ContextOrder.adds_all(xs)) == True{} : Bool}) -> {Wr.get_list(~Co.Add, ~FCo.get_add, Wr.put_nat(List.length(&2, Co.Add, xs), ContextOrder.spell_adds.items(xs, r))) == Wr.Got{xs, r} : Wr.Dec<List<&2, Co.Add>>}:
  match xs:
    case Nil{}:
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(0n, r)), Wr.Got{0n, r}, Wire.wire_nat_round_trip(0n, r, {==})) : {Wr.get_list.start(~Co.Add, ~FCo.get_add, _) == Wr.Got{Nil{}, r} : Wr.Dec<List<&2, Co.Add>>}
      {==}
    case Con{+x, +t}:
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(List.length(&2, Co.Add, x <> t), ContextOrder.spell_adds.items(x <> t, r))), Wr.Got{List.length(&2, Co.Add, x <> t), ContextOrder.spell_adds.items(x <> t, r)}, Wire.wire_nat_round_trip(List.length(&2, Co.Add, x <> t), ContextOrder.spell_adds.items(x <> t, r), LACo.co.and_l(LawsBase.wire_fits(List.length(&2, Co.Add, x <> t)), ContextOrder.adds_all(x <> t), h))) : {Wr.get_list.start(~Co.Add, ~FCo.get_add, _) == Wr.Got{x <> t, r} : Wr.Dec<List<&2, Co.Add>>}
      cot.al.go_rt(t, x, r, LACo.co.and_r(LawsBase.wire_fits(List.length(&2, Co.Add, x <> t)), ContextOrder.adds_all(x <> t), h))

# a spelled request whose numbers fit reads back
def cot.req(q: FCo.Req, +rest: String, +h: {ContextOrder.req_fits(q) == True{} : Bool}) -> {FCo.get_req(ContextOrder.spell_req(q, rest)) == Wr.Got{q, rest} : Wr.Dec<FCo.Req>}:
  match q:
    case FCo.QOrder{+ms}:
      %cot.nat(0n, ContextOrder.spell_msgs(ms, rest), {==}) : {FCo.get_req.tag(_) == Wr.Got{FCo.QOrder{ms}, rest} : Wr.Dec<FCo.Req>}
      %Equal.sym(Wr.Dec<List<&2, Co.Msg>>, FCo.get_msgs(ContextOrder.spell_msgs(ms, rest)), Wr.Got{ms, rest}, cot.ml.rt(ms, rest, h)) : {FCo.get_order(_) == Wr.Got{FCo.QOrder{ms}, rest} : Wr.Dec<FCo.Req>}
      {==}
    case FCo.QDerive{+mk, +es}:
      +r2 = Wr.put_nat(List.length(&2, Co.Ent, es), ContextOrder.spell_ents.items(es, rest))
      %cot.nat(1n, Wr.put_bool(mk, r2), {==}) : {FCo.get_req.tag(_) == Wr.Got{FCo.QDerive{mk, es}, rest} : Wr.Dec<FCo.Req>}
      %cot.bool(mk, r2) : {FCo.get_derive(_) == Wr.Got{FCo.QDerive{mk, es}, rest} : Wr.Dec<FCo.Req>}
      %Equal.sym(Wr.Dec<List<&2, Co.Ent>>, Wr.get_list(~Co.Ent, ~FCo.get_ent, r2), Wr.Got{es, rest}, cot.el.rt(es, rest, h)) : {FCo.get_derive.es(mk, _) == Wr.Got{FCo.QDerive{mk, es}, rest} : Wr.Dec<FCo.Req>}
      {==}
    case FCo.QExtend{+ads, +open}:
      +r2 = ContextOrder.spell_msgs(open, rest)
      +ha = LACo.co.and_l(LawsBase.wire_fits(List.length(&2, Co.Add, ads)), Bool.and(ContextOrder.adds_all(ads), ContextOrder.msgs_fit(open)), h)
      +hb = LACo.co.and_r(LawsBase.wire_fits(List.length(&2, Co.Add, ads)), Bool.and(ContextOrder.adds_all(ads), ContextOrder.msgs_fit(open)), h)
      %cot.nat(2n, Wr.put_nat(List.length(&2, Co.Add, ads), ContextOrder.spell_adds.items(ads, r2)), {==}) : {FCo.get_req.tag(_) == Wr.Got{FCo.QExtend{ads, open}, rest} : Wr.Dec<FCo.Req>}
      %Equal.sym(Wr.Dec<List<&2, Co.Add>>, Wr.get_list(~Co.Add, ~FCo.get_add, Wr.put_nat(List.length(&2, Co.Add, ads), ContextOrder.spell_adds.items(ads, r2))), Wr.Got{ads, r2}, cot.al.rt(ads, r2, LACo.co.and_tt(LawsBase.wire_fits(List.length(&2, Co.Add, ads)), ContextOrder.adds_all(ads), ha, LACo.co.and_l(ContextOrder.adds_all(ads), ContextOrder.msgs_fit(open), hb)))) : {FCo.get_extend(_) == Wr.Got{FCo.QExtend{ads, open}, rest} : Wr.Dec<FCo.Req>}
      %Equal.sym(Wr.Dec<List<&2, Co.Msg>>, FCo.get_msgs(r2), Wr.Got{open, rest}, cot.ml.rt(open, rest, LACo.co.and_r(ContextOrder.adds_all(ads), ContextOrder.msgs_fit(open), hb))) : {FCo.get_extend.open(ads, _) == Wr.Got{FCo.QExtend{ads, open}, rest} : Wr.Dec<FCo.Req>}
      {==}
    case FCo.QLead{+rs}:
      %cot.nat(3n, Wr.put_nat(List.length(&2, Co.Role, rs), ContextOrder.spell_roles.items(rs, rest)), {==}) : {FCo.get_req.tag(_) == Wr.Got{FCo.QLead{rs}, rest} : Wr.Dec<FCo.Req>}
      %Equal.sym(Wr.Dec<List<&2, Co.Role>>, Wr.get_list(~Co.Role, ~FCo.get_role, Wr.put_nat(List.length(&2, Co.Role, rs), ContextOrder.spell_roles.items(rs, rest))), Wr.Got{rs, rest}, cot.rl.rt(rs, rest, h)) : {FCo.get_lead(_) == Wr.Got{FCo.QLead{rs}, rest} : Wr.Dec<FCo.Req>}
      {==}
