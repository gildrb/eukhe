# eukhe: lemmas shared by the proofs of area privacy, section ip: the
# reader over the items an IPv6 writes (groups joined by `:`, an IPv4
# last, a `::` between the groups before it and after it)

import Base
import ../../../bend/privacy/ip.bend as Ip
import ../../../bend/privacy/context.bend as Cx
import ../../../spec/harness/privacy.bend as S
import ./chars.bend as LIp
import ./read.bend as LRd
import ./quad.bend as LQd

# Lists of groups
# ---------------

def pit.app_one(xs: List<&2, String>, -g: String, -ys: List<&2, String>) -> {List.append(&2, String, List.append(&2, String, xs, [g]), ys) == List.append(&2, String, xs, g <> ys) : List<&2, String>}:
  match xs:
    case Nil{}:
      {==}
    case x <> rest:
      %pit.app_one(rest, g, ys) : {x <> List.append(&2, String, List.append(&2, String, rest, [g]), ys) == x <> _ : List<&2, String>}
      {==}

# the groups gs pushed one by one
def pit.pushes(gs: List<&2, String>, acc: Ip.Acc) -> Ip.Acc:
  match gs:
    case Nil{}:
      acc
    case +g <> rest:
      pit.pushes(rest, Ip.Acc.push(acc, g))

def pit.app_nil(xs: List<&2, String>) -> {List.append(&2, String, xs, Nil{}) == xs : List<&2, String>}:
  match xs:
    case Nil{}:
      {==}
    case x <> rest:
      %pit.app_nil(rest) : {x <> List.append(&2, String, rest, Nil{}) == x <> _ : List<&2, String>}
      {==}

def pit.pushes_l(gs: List<&2, String>, +l: List<&2, String>, -r: List<&2, String>) -> {pit.pushes(gs, Ip.Acc{False{}, l, r}) == Ip.Acc{False{}, List.append(&2, String, l, gs), r} : Ip.Acc}:
  match gs:
    case Nil{}:
      %Equal.sym(List<&2, String>, List.append(&2, String, l, Nil{}), l, pit.app_nil(l)) : {Ip.Acc{False{}, l, r} == Ip.Acc{False{}, _, r} : Ip.Acc}
      {==}
    case +g <> +rest:
      %pit.app_one(l, g, rest) : {pit.pushes(rest, Ip.Acc{False{}, List.append(&2, String, l, [g]), r}) == Ip.Acc{False{}, _, r} : Ip.Acc}
      pit.pushes_l(rest, List.append(&2, String, l, [g]), r)

def pit.pushes_r(gs: List<&2, String>, -l: List<&2, String>, +r: List<&2, String>) -> {pit.pushes(gs, Ip.Acc{True{}, l, r}) == Ip.Acc{True{}, l, List.append(&2, String, r, gs)} : Ip.Acc}:
  match gs:
    case Nil{}:
      %Equal.sym(List<&2, String>, List.append(&2, String, r, Nil{}), r, pit.app_nil(r)) : {Ip.Acc{True{}, l, r} == Ip.Acc{True{}, l, _} : Ip.Acc}
      {==}
    case +g <> +rest:
      %pit.app_one(r, g, rest) : {pit.pushes(rest, Ip.Acc{True{}, l, List.append(&2, String, r, [g])}) == Ip.Acc{True{}, l, _} : Ip.Acc}
      pit.pushes_r(rest, l, List.append(&2, String, r, [g]))

# Joins
# -----

def pit.jtail(y: String, ys: List<&2, String>, t: String) -> String:
  match ys:
    case Nil{}:
      String.append(y, t)
    case z <> zs:
      String.append(y, SCon{':', S.join(z <> zs, t)})

# items whose first starts with c
def pit.join_cons(-c: Char, -y: String, ys: List<&2, String>, -t: String) -> {S.join(SCon{c, y} <> ys, t) == SCon{c, pit.jtail(y, ys, t)} : String}:
  match ys:
    case Nil{}:
      {==}
    case z <> zs:
      {==}

# a group, `:`, then a hex digit c, read from where a group may start
def pit.sep_open(+g: String, +c: Char, +J: String, +acc: Ip.Acc, +hg: {S.group(g) == True{} : Bool}, +hc: {S.hex(c) == True{} : Bool}) -> {Ip.read(Ip.Sym.list(String.append(g, SCon{':', SCon{c, J}})), Ip.Open{}, acc) == Ip.read(Ip.Sym.of(c) <> Ip.Sym.list(J), Ip.Open{}, Ip.Acc.push(acc, g)) : Ip.Read}:
  +hx = LIp.pip.and_l(S.all_hex(g), Bool.and(Nat.is_le(1n, String.length(g)), Nat.is_le(String.length(g), 4n)), hg)
  +X = {Ip.Col{} <> (Ip.Sym.of(c) <> Ip.Sym.list(J)) : List<&2, Ip.Sym>}
  +st = List.append(&2, Ip.Sym, Ip.Sym.list(g), X)
  %Equal.sym(List<&2, Ip.Sym>, Ip.Sym.list(String.append(g, SCon{':', SCon{c, J}})), st, LRd.prd.sym_app(g, SCon{':', SCon{c, J}})) : {Ip.read(_, Ip.Open{}, acc) == Ip.read(Ip.Sym.of(c) <> Ip.Sym.list(J), Ip.Open{}, Ip.Acc.push(acc, g)) : Ip.Read}
  %Equal.sym(Ip.Read, Ip.read(st, Ip.Open{}, acc), Ip.read(X, Ip.Grp{st, LRd.prd.room(g)}, acc), LRd.prd.group_open(g, X, acc, hg)) : {_ == Ip.read(Ip.Sym.of(c) <> Ip.Sym.list(J), Ip.Open{}, Ip.Acc.push(acc, g)) : Ip.Read}
  %Equal.sym(Ip.Read, Ip.read(X, Ip.Grp{st, LRd.prd.room(g)}, acc), Ip.read(Ip.Sym.of(c) <> Ip.Sym.list(J), Ip.Open{}, Ip.Acc.push(acc, Ip.group(st))), LRd.prd.grp_sep(c, LRd.prd.hex_sym(c, hc), Ip.Sym.list(J), st, LRd.prd.room(g), acc)) : {_ == Ip.read(Ip.Sym.of(c) <> Ip.Sym.list(J), Ip.Open{}, Ip.Acc.push(acc, g)) : Ip.Read}
  %Equal.sym(String, Ip.group(st), g, LRd.prd.group_is(g, X, hx, {==})) : {Ip.read(Ip.Sym.of(c) <> Ip.Sym.list(J), Ip.Open{}, Ip.Acc.push(acc, _)) == Ip.read(Ip.Sym.of(c) <> Ip.Sym.list(J), Ip.Open{}, Ip.Acc.push(acc, g)) : Ip.Read}
  {==}

# a group, `:`, then a hex digit c, read from the start of the text
def pit.sep_begin(+g: String, +c: Char, +J: String, +acc: Ip.Acc, +hg: {S.group(g) == True{} : Bool}, +hc: {S.hex(c) == True{} : Bool}) -> {Ip.read(Ip.Sym.list(String.append(g, SCon{':', SCon{c, J}})), Ip.Begin{}, acc) == Ip.read(Ip.Sym.of(c) <> Ip.Sym.list(J), Ip.Open{}, Ip.Acc.push(acc, g)) : Ip.Read}:
  +hx = LIp.pip.and_l(S.all_hex(g), Bool.and(Nat.is_le(1n, String.length(g)), Nat.is_le(String.length(g), 4n)), hg)
  +X = {Ip.Col{} <> (Ip.Sym.of(c) <> Ip.Sym.list(J)) : List<&2, Ip.Sym>}
  +st = List.append(&2, Ip.Sym, Ip.Sym.list(g), X)
  %Equal.sym(List<&2, Ip.Sym>, Ip.Sym.list(String.append(g, SCon{':', SCon{c, J}})), st, LRd.prd.sym_app(g, SCon{':', SCon{c, J}})) : {Ip.read(_, Ip.Begin{}, acc) == Ip.read(Ip.Sym.of(c) <> Ip.Sym.list(J), Ip.Open{}, Ip.Acc.push(acc, g)) : Ip.Read}
  %Equal.sym(Ip.Read, Ip.read(st, Ip.Begin{}, acc), Ip.read(X, Ip.Grp{st, LRd.prd.room(g)}, acc), LRd.prd.group_begin(g, X, acc, hg)) : {_ == Ip.read(Ip.Sym.of(c) <> Ip.Sym.list(J), Ip.Open{}, Ip.Acc.push(acc, g)) : Ip.Read}
  %Equal.sym(Ip.Read, Ip.read(X, Ip.Grp{st, LRd.prd.room(g)}, acc), Ip.read(Ip.Sym.of(c) <> Ip.Sym.list(J), Ip.Open{}, Ip.Acc.push(acc, Ip.group(st))), LRd.prd.grp_sep(c, LRd.prd.hex_sym(c, hc), Ip.Sym.list(J), st, LRd.prd.room(g), acc)) : {_ == Ip.read(Ip.Sym.of(c) <> Ip.Sym.list(J), Ip.Open{}, Ip.Acc.push(acc, g)) : Ip.Read}
  %Equal.sym(String, Ip.group(st), g, LRd.prd.group_is(g, X, hx, {==})) : {Ip.read(Ip.Sym.of(c) <> Ip.Sym.list(J), Ip.Open{}, Ip.Acc.push(acc, _)) == Ip.read(Ip.Sym.of(c) <> Ip.Sym.list(J), Ip.Open{}, Ip.Acc.push(acc, g)) : Ip.Read}
  {==}


# one group, then t, read from where a group may start
def pit.single_open(+g: String, +t: String, +acc: Ip.Acc, +hg: {S.group(g) == True{} : Bool}, +ht: {S.stops6(t) == True{} : Bool}) -> {Ip.read(Ip.Sym.list(String.append(g, t)), Ip.Open{}, acc) == Ip.finish(Ip.Acc.push(acc, g), None{}, Ip.Sym.list(t)) : Ip.Read}:
  +hx = LIp.pip.and_l(S.all_hex(g), Bool.and(Nat.is_le(1n, String.length(g)), Nat.is_le(String.length(g), 4n)), hg)
  +st = List.append(&2, Ip.Sym, Ip.Sym.list(g), Ip.Sym.list(t))
  %Equal.sym(List<&2, Ip.Sym>, Ip.Sym.list(String.append(g, t)), st, LRd.prd.sym_app(g, t)) : {Ip.read(_, Ip.Open{}, acc) == Ip.finish(Ip.Acc.push(acc, g), None{}, Ip.Sym.list(t)) : Ip.Read}
  %Equal.sym(Ip.Read, Ip.read(st, Ip.Open{}, acc), Ip.read(Ip.Sym.list(t), Ip.Grp{st, LRd.prd.room(g)}, acc), LRd.prd.group_open(g, Ip.Sym.list(t), acc, hg)) : {_ == Ip.finish(Ip.Acc.push(acc, g), None{}, Ip.Sym.list(t)) : Ip.Read}
  %Equal.sym(Ip.Read, Ip.read(Ip.Sym.list(t), Ip.Grp{st, LRd.prd.room(g)}, acc), Ip.finish(Ip.Acc.push(acc, Ip.group(st)), None{}, Ip.Sym.list(t)), LRd.prd.grp_end(t, st, LRd.prd.room(g), acc, ht)) : {_ == Ip.finish(Ip.Acc.push(acc, g), None{}, Ip.Sym.list(t)) : Ip.Read}
  %Equal.sym(String, Ip.group(st), g, LRd.prd.group_is(g, Ip.Sym.list(t), hx, LRd.prd.run_end(t, ht))) : {Ip.finish(Ip.Acc.push(acc, _), None{}, Ip.Sym.list(t)) == Ip.finish(Ip.Acc.push(acc, g), None{}, Ip.Sym.list(t)) : Ip.Read}
  {==}

# one group, then t, read from the start of the text
def pit.single_begin(+g: String, +t: String, +acc: Ip.Acc, +hg: {S.group(g) == True{} : Bool}, +ht: {S.stops6(t) == True{} : Bool}) -> {Ip.read(Ip.Sym.list(String.append(g, t)), Ip.Begin{}, acc) == Ip.finish(Ip.Acc.push(acc, g), None{}, Ip.Sym.list(t)) : Ip.Read}:
  +hx = LIp.pip.and_l(S.all_hex(g), Bool.and(Nat.is_le(1n, String.length(g)), Nat.is_le(String.length(g), 4n)), hg)
  +st = List.append(&2, Ip.Sym, Ip.Sym.list(g), Ip.Sym.list(t))
  %Equal.sym(List<&2, Ip.Sym>, Ip.Sym.list(String.append(g, t)), st, LRd.prd.sym_app(g, t)) : {Ip.read(_, Ip.Begin{}, acc) == Ip.finish(Ip.Acc.push(acc, g), None{}, Ip.Sym.list(t)) : Ip.Read}
  %Equal.sym(Ip.Read, Ip.read(st, Ip.Begin{}, acc), Ip.read(Ip.Sym.list(t), Ip.Grp{st, LRd.prd.room(g)}, acc), LRd.prd.group_begin(g, Ip.Sym.list(t), acc, hg)) : {_ == Ip.finish(Ip.Acc.push(acc, g), None{}, Ip.Sym.list(t)) : Ip.Read}
  %Equal.sym(Ip.Read, Ip.read(Ip.Sym.list(t), Ip.Grp{st, LRd.prd.room(g)}, acc), Ip.finish(Ip.Acc.push(acc, Ip.group(st)), None{}, Ip.Sym.list(t)), LRd.prd.grp_end(t, st, LRd.prd.room(g), acc, ht)) : {_ == Ip.finish(Ip.Acc.push(acc, g), None{}, Ip.Sym.list(t)) : Ip.Read}
  %Equal.sym(String, Ip.group(st), g, LRd.prd.group_is(g, Ip.Sym.list(t), hx, LRd.prd.run_end(t, ht))) : {Ip.finish(Ip.Acc.push(acc, _), None{}, Ip.Sym.list(t)) == Ip.finish(Ip.Acc.push(acc, g), None{}, Ip.Sym.list(t)) : Ip.Read}
  {==}

# an IPv4 alone, then t, read from where a group may start
def pit.items_q(q: Maybe<&2, Ip.Quad>, +acc: Ip.Acc, +t: String, +hq: {S.mquad_ok(q) == True{} : Bool}, +ht: {S.stops6(t) == True{} : Bool}) -> {Ip.read(Ip.Sym.list(S.join(S.quad_items(q), t)), Ip.Open{}, acc) == Ip.finish(acc, q, Ip.Sym.list(t)) : Ip.Read}:
  match q:
    case None{}:
      LRd.prd.open_end(t, acc, ht)
    case Some{+x}:
      %Equal.sym(String, String.append(S.quad_text(x, ""), t), S.quad_text(x, t), LQd.pqd.qt_app(x, t)) : {Ip.read(Ip.Sym.list(_), Ip.Open{}, acc) == Ip.finish(acc, Some{x}, Ip.Sym.list(t)) : Ip.Read}
      LQd.pqd.quad_open(x, t, acc, hq, LRd.prd.drun_end4(t, LRd.prd.stops6_4(t, ht)))

# a group g, then the items of rest and q, read from where a group may start
def pit.more_open(rest: List<&2, String>, +q: Maybe<&2, Ip.Quad>, +g: String, +acc: Ip.Acc, +t: String, +hg: {S.group(g) == True{} : Bool}, +hr: {S.groups(rest) == True{} : Bool}, +hq: {S.mquad_ok(q) == True{} : Bool}, +ht: {S.stops6(t) == True{} : Bool},
  ih: @acc2: Ip.Acc -> {Ip.read(Ip.Sym.list(S.join(List.append(&2, String, rest, S.quad_items(q)), t)), Ip.Open{}, acc2) == Ip.finish(pit.pushes(rest, acc2), q, Ip.Sym.list(t)) : Ip.Read}) ->
  {Ip.read(Ip.Sym.list(S.join(List.append(&2, String, g <> rest, S.quad_items(q)), t)), Ip.Open{}, acc) == Ip.finish(pit.pushes(g <> rest, acc), q, Ip.Sym.list(t)) : Ip.Read}:
  match rest:
    case Nil{}:
      match q:
        case None{}:
          pit.single_open(g, t, acc, hg, ht)
        case Some{+x}:
          match x:
            case Ip.Quad{+a, +b, +c, +d}:
              match a:
                case SNil{}:
                  LIp.pip.absurd_ft({Ip.read(Ip.Sym.list(S.join(List.append(&2, String, [g], [S.quad_text(Ip.Quad{SNil{}, b, c, d}, "")]), t)), Ip.Open{}, acc) == Ip.finish(pit.pushes([g], acc), Some{Ip.Quad{SNil{}, b, c, d}}, Ip.Sym.list(t)) : Ip.Read}, hq)
                case SCon{+c2, +a2}:
                  +ha = LIp.pip.and_l(S.octet(SCon{c2, a2}), S.octet(b), LIp.pip.and_l(Bool.and(S.octet(SCon{c2, a2}), S.octet(b)), Bool.and(S.octet(c), S.octet(d)), hq))
                  +hd = LIp.pip.and_l(S.dec(c2), S.all_dec(a2), LQd.pqd.f_dec(SCon{c2, a2}, LQd.pqd.facts(SCon{c2, a2}, ha)))
                  +J = String.append(String.append(a2, SCon{'.', String.append(b, SCon{'.', String.append(c, SCon{'.', String.append(d, "")})})}), t)
                  Equal.trans(Ip.Read, Ip.read(Ip.Sym.list(String.append(g, SCon{':', SCon{c2, J}})), Ip.Open{}, acc), Ip.read(Ip.Sym.of(c2) <> Ip.Sym.list(J), Ip.Open{}, Ip.Acc.push(acc, g)), Ip.finish(pit.pushes(Nil{}, Ip.Acc.push(acc, g)), Some{Ip.Quad{SCon{c2, a2}, b, c, d}}, Ip.Sym.list(t)), pit.sep_open(g, c2, J, acc, hg, LQd.pqd.dec_hex(c2, hd)), ih(Ip.Acc.push(acc, g)))
    case g2 <> +rest2:
      match g2:
        case SNil{}:
          LIp.pip.absurd_ft({Ip.read(Ip.Sym.list(S.join(List.append(&2, String, g <> (SNil{} <> rest2), S.quad_items(q)), t)), Ip.Open{}, acc) == Ip.finish(pit.pushes(g <> (SNil{} <> rest2), acc), q, Ip.Sym.list(t)) : Ip.Read}, hr)
        case SCon{+c2, +y}:
          +hg2 = LIp.pip.and_l(S.group(SCon{c2, y}), S.groups(rest2), hr)
          +hc = LIp.pip.and_l(S.hex(c2), S.all_hex(y), LIp.pip.and_l(S.all_hex(SCon{c2, y}), Bool.and(Nat.is_le(1n, String.length(SCon{c2, y})), Nat.is_le(String.length(SCon{c2, y}), 4n)), hg2))
          +ys = List.append(&2, String, rest2, S.quad_items(q))
          +J = pit.jtail(y, ys, t)
          %Equal.sym(String, S.join(SCon{c2, y} <> ys, t), SCon{c2, J}, pit.join_cons(c2, y, ys, t)) : {Ip.read(Ip.Sym.list(String.append(g, SCon{':', _})), Ip.Open{}, acc) == Ip.finish(pit.pushes(rest2, Ip.Acc.push(Ip.Acc.push(acc, g), SCon{c2, y})), q, Ip.Sym.list(t)) : Ip.Read}
          %Equal.sym(Ip.Read, Ip.read(Ip.Sym.list(String.append(g, SCon{':', SCon{c2, J}})), Ip.Open{}, acc), Ip.read(Ip.Sym.of(c2) <> Ip.Sym.list(J), Ip.Open{}, Ip.Acc.push(acc, g)), pit.sep_open(g, c2, J, acc, hg, hc)) : {_ == Ip.finish(pit.pushes(rest2, Ip.Acc.push(Ip.Acc.push(acc, g), SCon{c2, y})), q, Ip.Sym.list(t)) : Ip.Read}
          %pit.join_cons(c2, y, ys, t) : {Ip.read(Ip.Sym.list(_), Ip.Open{}, Ip.Acc.push(acc, g)) == Ip.finish(pit.pushes(rest2, Ip.Acc.push(Ip.Acc.push(acc, g), SCon{c2, y})), q, Ip.Sym.list(t)) : Ip.Read}
          ih(Ip.Acc.push(acc, g))

# the items of gs and q, then t, read from where a group may start
def pit.items_open(gs: List<&2, String>, +q: Maybe<&2, Ip.Quad>, +acc: Ip.Acc, +t: String, +hg: {S.groups(gs) == True{} : Bool}, +hq: {S.mquad_ok(q) == True{} : Bool}, +ht: {S.stops6(t) == True{} : Bool}) -> {Ip.read(Ip.Sym.list(S.join(List.append(&2, String, gs, S.quad_items(q)), t)), Ip.Open{}, acc) == Ip.finish(pit.pushes(gs, acc), q, Ip.Sym.list(t)) : Ip.Read}:
  match gs:
    case Nil{}:
      pit.items_q(q, acc, t, hq, ht)
    case +g <> +rest:
      +hgg = LIp.pip.and_l(S.group(g), S.groups(rest), hg)
      +hgr = LIp.pip.and_r(S.group(g), S.groups(rest), hg)
      pit.more_open(rest, q, g, acc, t, hgg, hgr, hq, ht, acc2 => pit.items_open(rest, q, acc2, t, hgr, hq, ht))

# a group g, then the items of rest and q, read from the start of the text
def pit.more_begin(rest: List<&2, String>, +q: Maybe<&2, Ip.Quad>, +g: String, +acc: Ip.Acc, +t: String, +hg: {S.group(g) == True{} : Bool}, +hr: {S.groups(rest) == True{} : Bool}, +hq: {S.mquad_ok(q) == True{} : Bool}, +ht: {S.stops6(t) == True{} : Bool},
  ih: @acc2: Ip.Acc -> {Ip.read(Ip.Sym.list(S.join(List.append(&2, String, rest, S.quad_items(q)), t)), Ip.Open{}, acc2) == Ip.finish(pit.pushes(rest, acc2), q, Ip.Sym.list(t)) : Ip.Read}) ->
  {Ip.read(Ip.Sym.list(S.join(List.append(&2, String, g <> rest, S.quad_items(q)), t)), Ip.Begin{}, acc) == Ip.finish(pit.pushes(g <> rest, acc), q, Ip.Sym.list(t)) : Ip.Read}:
  match rest:
    case Nil{}:
      match q:
        case None{}:
          pit.single_begin(g, t, acc, hg, ht)
        case Some{+x}:
          match x:
            case Ip.Quad{+a, +b, +c, +d}:
              match a:
                case SNil{}:
                  LIp.pip.absurd_ft({Ip.read(Ip.Sym.list(S.join(List.append(&2, String, [g], [S.quad_text(Ip.Quad{SNil{}, b, c, d}, "")]), t)), Ip.Begin{}, acc) == Ip.finish(pit.pushes([g], acc), Some{Ip.Quad{SNil{}, b, c, d}}, Ip.Sym.list(t)) : Ip.Read}, hq)
                case SCon{+c2, +a2}:
                  +ha = LIp.pip.and_l(S.octet(SCon{c2, a2}), S.octet(b), LIp.pip.and_l(Bool.and(S.octet(SCon{c2, a2}), S.octet(b)), Bool.and(S.octet(c), S.octet(d)), hq))
                  +hd = LIp.pip.and_l(S.dec(c2), S.all_dec(a2), LQd.pqd.f_dec(SCon{c2, a2}, LQd.pqd.facts(SCon{c2, a2}, ha)))
                  +J = String.append(String.append(a2, SCon{'.', String.append(b, SCon{'.', String.append(c, SCon{'.', String.append(d, "")})})}), t)
                  Equal.trans(Ip.Read, Ip.read(Ip.Sym.list(String.append(g, SCon{':', SCon{c2, J}})), Ip.Begin{}, acc), Ip.read(Ip.Sym.of(c2) <> Ip.Sym.list(J), Ip.Open{}, Ip.Acc.push(acc, g)), Ip.finish(pit.pushes(Nil{}, Ip.Acc.push(acc, g)), Some{Ip.Quad{SCon{c2, a2}, b, c, d}}, Ip.Sym.list(t)), pit.sep_begin(g, c2, J, acc, hg, LQd.pqd.dec_hex(c2, hd)), ih(Ip.Acc.push(acc, g)))
    case g2 <> +rest2:
      match g2:
        case SNil{}:
          LIp.pip.absurd_ft({Ip.read(Ip.Sym.list(S.join(List.append(&2, String, g <> (SNil{} <> rest2), S.quad_items(q)), t)), Ip.Begin{}, acc) == Ip.finish(pit.pushes(g <> (SNil{} <> rest2), acc), q, Ip.Sym.list(t)) : Ip.Read}, hr)
        case SCon{+c2, +y}:
          +hg2 = LIp.pip.and_l(S.group(SCon{c2, y}), S.groups(rest2), hr)
          +hc = LIp.pip.and_l(S.hex(c2), S.all_hex(y), LIp.pip.and_l(S.all_hex(SCon{c2, y}), Bool.and(Nat.is_le(1n, String.length(SCon{c2, y})), Nat.is_le(String.length(SCon{c2, y}), 4n)), hg2))
          +ys = List.append(&2, String, rest2, S.quad_items(q))
          +J = pit.jtail(y, ys, t)
          %Equal.sym(String, S.join(SCon{c2, y} <> ys, t), SCon{c2, J}, pit.join_cons(c2, y, ys, t)) : {Ip.read(Ip.Sym.list(String.append(g, SCon{':', _})), Ip.Begin{}, acc) == Ip.finish(pit.pushes(rest2, Ip.Acc.push(Ip.Acc.push(acc, g), SCon{c2, y})), q, Ip.Sym.list(t)) : Ip.Read}
          %Equal.sym(Ip.Read, Ip.read(Ip.Sym.list(String.append(g, SCon{':', SCon{c2, J}})), Ip.Begin{}, acc), Ip.read(Ip.Sym.of(c2) <> Ip.Sym.list(J), Ip.Open{}, Ip.Acc.push(acc, g)), pit.sep_begin(g, c2, J, acc, hg, hc)) : {_ == Ip.finish(pit.pushes(rest2, Ip.Acc.push(Ip.Acc.push(acc, g), SCon{c2, y})), q, Ip.Sym.list(t)) : Ip.Read}
          %pit.join_cons(c2, y, ys, t) : {Ip.read(Ip.Sym.list(_), Ip.Open{}, Ip.Acc.push(acc, g)) == Ip.finish(pit.pushes(rest2, Ip.Acc.push(Ip.Acc.push(acc, g), SCon{c2, y})), q, Ip.Sym.list(t)) : Ip.Read}
          ih(Ip.Acc.push(acc, g))

# the groups g and rest, then `::` and J, read from where a group may start
def pit.left_open(rest: List<&2, String>, +g: String, +J: String, +l0: List<&2, String>, +r0: List<&2, String>, +hg: {S.groups(g <> rest) == True{} : Bool}) -> {Ip.read(Ip.Sym.list(S.join(g <> rest, SCon{':', SCon{':', J}})), Ip.Open{}, Ip.Acc{False{}, l0, r0}) == Ip.read(Ip.Sym.list(J), Ip.Open{}, Ip.Acc{True{}, List.append(&2, String, l0, g <> rest), r0}) : Ip.Read}:
  match rest:
    case Nil{}:
      +hgg = LIp.pip.and_l(S.group(g), S.groups(Nil{}), hg)
      +hx = LIp.pip.and_l(S.all_hex(g), Bool.and(Nat.is_le(1n, String.length(g)), Nat.is_le(String.length(g), 4n)), hgg)
      +X = {Ip.Col{} <> (Ip.Col{} <> Ip.Sym.list(J)) : List<&2, Ip.Sym>}
      +st = List.append(&2, Ip.Sym, Ip.Sym.list(g), X)
      %Equal.sym(List<&2, Ip.Sym>, Ip.Sym.list(String.append(g, SCon{':', SCon{':', J}})), st, LRd.prd.sym_app(g, SCon{':', SCon{':', J}})) : {Ip.read(_, Ip.Open{}, Ip.Acc{False{}, l0, r0}) == Ip.read(Ip.Sym.list(J), Ip.Open{}, Ip.Acc{True{}, List.append(&2, String, l0, [g]), r0}) : Ip.Read}
      %Equal.sym(Ip.Read, Ip.read(st, Ip.Open{}, Ip.Acc{False{}, l0, r0}), Ip.read(X, Ip.Grp{st, LRd.prd.room(g)}, Ip.Acc{False{}, l0, r0}), LRd.prd.group_open(g, X, Ip.Acc{False{}, l0, r0}, hgg)) : {_ == Ip.read(Ip.Sym.list(J), Ip.Open{}, Ip.Acc{True{}, List.append(&2, String, l0, [g]), r0}) : Ip.Read}
      %Equal.sym(String, Ip.group(st), g, LRd.prd.group_is(g, X, hx, {==})) : {Ip.read(Ip.Sym.list(J), Ip.Open{}, Ip.Acc{True{}, List.append(&2, String, l0, [_]), r0}) == Ip.read(Ip.Sym.list(J), Ip.Open{}, Ip.Acc{True{}, List.append(&2, String, l0, [g]), r0}) : Ip.Read}
      {==}
    case g2 <> +rest2:
      match g2:
        case SNil{}:
          LIp.pip.absurd_ft({Ip.read(Ip.Sym.list(S.join(g <> (SNil{} <> rest2), SCon{':', SCon{':', J}})), Ip.Open{}, Ip.Acc{False{}, l0, r0}) == Ip.read(Ip.Sym.list(J), Ip.Open{}, Ip.Acc{True{}, List.append(&2, String, l0, g <> (SNil{} <> rest2)), r0}) : Ip.Read}, LIp.pip.and_l(S.group(SNil{}), S.groups(rest2), LIp.pip.and_r(S.group(g), S.groups(SNil{} <> rest2), hg)))
        case SCon{+c2, +y}:
          +hgg = LIp.pip.and_l(S.group(g), S.groups(SCon{c2, y} <> rest2), hg)
          +hr = LIp.pip.and_r(S.group(g), S.groups(SCon{c2, y} <> rest2), hg)
          +hg2 = LIp.pip.and_l(S.group(SCon{c2, y}), S.groups(rest2), hr)
          +hc = LIp.pip.and_l(S.hex(c2), S.all_hex(y), LIp.pip.and_l(S.all_hex(SCon{c2, y}), Bool.and(Nat.is_le(1n, String.length(SCon{c2, y})), Nat.is_le(String.length(SCon{c2, y}), 4n)), hg2))
          +K = pit.jtail(y, rest2, SCon{':', SCon{':', J}})
          +RHS = Ip.read(Ip.Sym.list(J), Ip.Open{}, Ip.Acc{True{}, List.append(&2, String, l0, g <> (SCon{c2, y} <> rest2)), r0})
          %Equal.sym(String, S.join(SCon{c2, y} <> rest2, SCon{':', SCon{':', J}}), SCon{c2, K}, pit.join_cons(c2, y, rest2, SCon{':', SCon{':', J}})) : {Ip.read(Ip.Sym.list(String.append(g, SCon{':', _})), Ip.Open{}, Ip.Acc{False{}, l0, r0}) == RHS : Ip.Read}
          %Equal.sym(Ip.Read, Ip.read(Ip.Sym.list(String.append(g, SCon{':', SCon{c2, K}})), Ip.Open{}, Ip.Acc{False{}, l0, r0}), Ip.read(Ip.Sym.of(c2) <> Ip.Sym.list(K), Ip.Open{}, Ip.Acc.push(Ip.Acc{False{}, l0, r0}, g)), pit.sep_open(g, c2, K, Ip.Acc{False{}, l0, r0}, hgg, hc)) : {_ == RHS : Ip.Read}
          %pit.join_cons(c2, y, rest2, SCon{':', SCon{':', J}}) : {Ip.read(Ip.Sym.list(_), Ip.Open{}, Ip.Acc{False{}, List.append(&2, String, l0, [g]), r0}) == RHS : Ip.Read}
          %pit.app_one(l0, g, SCon{c2, y} <> rest2) : {Ip.read(Ip.Sym.list(S.join(SCon{c2, y} <> rest2, SCon{':', SCon{':', J}})), Ip.Open{}, Ip.Acc{False{}, List.append(&2, String, l0, [g]), r0}) == Ip.read(Ip.Sym.list(J), Ip.Open{}, Ip.Acc{True{}, _, r0}) : Ip.Read}
          pit.left_open(rest2, SCon{c2, y}, J, List.append(&2, String, l0, [g]), r0, hr)

# the groups g and rest, then `::` and J, read from the start of the text
def pit.left_begin(rest: List<&2, String>, +g: String, +J: String, +l0: List<&2, String>, +r0: List<&2, String>, +hg: {S.groups(g <> rest) == True{} : Bool}) -> {Ip.read(Ip.Sym.list(S.join(g <> rest, SCon{':', SCon{':', J}})), Ip.Begin{}, Ip.Acc{False{}, l0, r0}) == Ip.read(Ip.Sym.list(J), Ip.Open{}, Ip.Acc{True{}, List.append(&2, String, l0, g <> rest), r0}) : Ip.Read}:
  match rest:
    case Nil{}:
      +hgg = LIp.pip.and_l(S.group(g), S.groups(Nil{}), hg)
      +hx = LIp.pip.and_l(S.all_hex(g), Bool.and(Nat.is_le(1n, String.length(g)), Nat.is_le(String.length(g), 4n)), hgg)
      +X = {Ip.Col{} <> (Ip.Col{} <> Ip.Sym.list(J)) : List<&2, Ip.Sym>}
      +st = List.append(&2, Ip.Sym, Ip.Sym.list(g), X)
      %Equal.sym(List<&2, Ip.Sym>, Ip.Sym.list(String.append(g, SCon{':', SCon{':', J}})), st, LRd.prd.sym_app(g, SCon{':', SCon{':', J}})) : {Ip.read(_, Ip.Begin{}, Ip.Acc{False{}, l0, r0}) == Ip.read(Ip.Sym.list(J), Ip.Open{}, Ip.Acc{True{}, List.append(&2, String, l0, [g]), r0}) : Ip.Read}
      %Equal.sym(Ip.Read, Ip.read(st, Ip.Begin{}, Ip.Acc{False{}, l0, r0}), Ip.read(X, Ip.Grp{st, LRd.prd.room(g)}, Ip.Acc{False{}, l0, r0}), LRd.prd.group_begin(g, X, Ip.Acc{False{}, l0, r0}, hgg)) : {_ == Ip.read(Ip.Sym.list(J), Ip.Open{}, Ip.Acc{True{}, List.append(&2, String, l0, [g]), r0}) : Ip.Read}
      %Equal.sym(String, Ip.group(st), g, LRd.prd.group_is(g, X, hx, {==})) : {Ip.read(Ip.Sym.list(J), Ip.Open{}, Ip.Acc{True{}, List.append(&2, String, l0, [_]), r0}) == Ip.read(Ip.Sym.list(J), Ip.Open{}, Ip.Acc{True{}, List.append(&2, String, l0, [g]), r0}) : Ip.Read}
      {==}
    case g2 <> +rest2:
      match g2:
        case SNil{}:
          LIp.pip.absurd_ft({Ip.read(Ip.Sym.list(S.join(g <> (SNil{} <> rest2), SCon{':', SCon{':', J}})), Ip.Begin{}, Ip.Acc{False{}, l0, r0}) == Ip.read(Ip.Sym.list(J), Ip.Open{}, Ip.Acc{True{}, List.append(&2, String, l0, g <> (SNil{} <> rest2)), r0}) : Ip.Read}, LIp.pip.and_l(S.group(SNil{}), S.groups(rest2), LIp.pip.and_r(S.group(g), S.groups(SNil{} <> rest2), hg)))
        case SCon{+c2, +y}:
          +hgg = LIp.pip.and_l(S.group(g), S.groups(SCon{c2, y} <> rest2), hg)
          +hr = LIp.pip.and_r(S.group(g), S.groups(SCon{c2, y} <> rest2), hg)
          +hg2 = LIp.pip.and_l(S.group(SCon{c2, y}), S.groups(rest2), hr)
          +hc = LIp.pip.and_l(S.hex(c2), S.all_hex(y), LIp.pip.and_l(S.all_hex(SCon{c2, y}), Bool.and(Nat.is_le(1n, String.length(SCon{c2, y})), Nat.is_le(String.length(SCon{c2, y}), 4n)), hg2))
          +K = pit.jtail(y, rest2, SCon{':', SCon{':', J}})
          +RHS = Ip.read(Ip.Sym.list(J), Ip.Open{}, Ip.Acc{True{}, List.append(&2, String, l0, g <> (SCon{c2, y} <> rest2)), r0})
          %Equal.sym(String, S.join(SCon{c2, y} <> rest2, SCon{':', SCon{':', J}}), SCon{c2, K}, pit.join_cons(c2, y, rest2, SCon{':', SCon{':', J}})) : {Ip.read(Ip.Sym.list(String.append(g, SCon{':', _})), Ip.Begin{}, Ip.Acc{False{}, l0, r0}) == RHS : Ip.Read}
          %Equal.sym(Ip.Read, Ip.read(Ip.Sym.list(String.append(g, SCon{':', SCon{c2, K}})), Ip.Begin{}, Ip.Acc{False{}, l0, r0}), Ip.read(Ip.Sym.of(c2) <> Ip.Sym.list(K), Ip.Open{}, Ip.Acc.push(Ip.Acc{False{}, l0, r0}, g)), pit.sep_begin(g, c2, K, Ip.Acc{False{}, l0, r0}, hgg, hc)) : {_ == RHS : Ip.Read}
          %pit.join_cons(c2, y, rest2, SCon{':', SCon{':', J}}) : {Ip.read(Ip.Sym.list(_), Ip.Open{}, Ip.Acc{False{}, List.append(&2, String, l0, [g]), r0}) == RHS : Ip.Read}
          %pit.app_one(l0, g, SCon{c2, y} <> rest2) : {Ip.read(Ip.Sym.list(S.join(SCon{c2, y} <> rest2, SCon{':', SCon{':', J}})), Ip.Open{}, Ip.Acc{False{}, List.append(&2, String, l0, [g]), r0}) == Ip.read(Ip.Sym.list(J), Ip.Open{}, Ip.Acc{True{}, _, r0}) : Ip.Read}
          pit.left_open(rest2, SCon{c2, y}, J, List.append(&2, String, l0, [g]), r0, hr)
