# eukhe: lemmas shared by the proofs of area privacy, section ip: what the
# IPv6 reader reads from the text an address writes, and the decision it
# takes on it

import Base
import ../../../bend/privacy/ip.bend as Ip
import ../../../bend/privacy/context.bend as Cx
import ../../../spec/harness/privacy.bend as S
import ./chars.bend as LIp
import ./read.bend as LRd
import ./items.bend as LIt
import ./quad.bend as LQd

# Texts
# -----

# items joined, then Y and t
def pdc.join_app(xs: List<&2, String>, +Y: String, +t: String) -> {S.join(xs, String.append(Y, t)) == String.append(S.join(xs, Y), t) : String}:
  match xs:
    case Nil{}:
      {==}
    case +x <> more:
      match more:
        case Nil{}:
          Equal.sym(String, String.append(String.append(x, Y), t), String.append(x, String.append(Y, t)), LRd.prd.app_assoc(x, Y, t))
        case y <> ys:
          %Equal.sym(String, S.join(y <> ys, String.append(Y, t)), String.append(S.join(y <> ys, Y), t), pdc.join_app(y <> ys, Y, t)) : {String.append(x, SCon{':', _}) == String.append(String.append(x, SCon{':', S.join(y <> ys, Y)}), t) : String}
          Equal.sym(String, String.append(String.append(x, SCon{':', S.join(y <> ys, Y)}), t), String.append(x, String.append(SCon{':', S.join(y <> ys, Y)}, t)), LRd.prd.app_assoc(x, SCon{':', S.join(y <> ys, Y)}, t))

# an IPv6 written, then t, is the IPv6 written alone, then t
def pdc.text6_app(a: Ip.Addr, +t: String) -> {S.text6(a, t) == String.append(S.text6(a, ""), t) : String}:
  match a:
    case Ip.Full{gs, q}:
      pdc.join_app(List.append(&2, String, gs, S.quad_items(q)), "", t)
    case Ip.Gap{l, r, q}:
      +rr = List.append(&2, String, r, S.quad_items(q))
      %Equal.sym(String, S.join(rr, String.append("", t)), String.append(S.join(rr, ""), t), pdc.join_app(rr, "", t)) : {S.join(l, SCon{':', SCon{':', _}}) == String.append(S.text6(Ip.Gap{l, r, q}, ""), t) : String}
      pdc.join_app(l, SCon{':', SCon{':', S.join(rr, "")}}, t)

# the length the reader answers is the length of the address written
def pdc.len6(+a: Ip.Addr, +t: String) -> {Nat.sub(List.length(&2, Ip.Sym, Ip.Sym.list(S.text6(a, t))), List.length(&2, Ip.Sym, Ip.Sym.list(t))) == String.length(S.text6(a, "")) : Nat}:
  %Equal.sym(String, S.text6(a, t), String.append(S.text6(a, ""), t), pdc.text6_app(a, t)) : {Nat.sub(List.length(&2, Ip.Sym, Ip.Sym.list(_)), List.length(&2, Ip.Sym, Ip.Sym.list(t))) == String.length(S.text6(a, "")) : Nat}
  %Equal.sym(List<&2, Ip.Sym>, Ip.Sym.list(String.append(S.text6(a, ""), t)), List.append(&2, Ip.Sym, Ip.Sym.list(S.text6(a, "")), Ip.Sym.list(t)), LRd.prd.sym_app(S.text6(a, ""), t)) : {Nat.sub(List.length(&2, Ip.Sym, _), List.length(&2, Ip.Sym, Ip.Sym.list(t))) == String.length(S.text6(a, "")) : Nat}
  %Equal.sym(Nat, List.length(&2, Ip.Sym, List.append(&2, Ip.Sym, Ip.Sym.list(S.text6(a, "")), Ip.Sym.list(t))), Nat.add(List.length(&2, Ip.Sym, Ip.Sym.list(S.text6(a, ""))), List.length(&2, Ip.Sym, Ip.Sym.list(t))), LRd.prd.list_len_app(Ip.Sym.list(S.text6(a, "")), Ip.Sym.list(t))) : {Nat.sub(_, List.length(&2, Ip.Sym, Ip.Sym.list(t))) == String.length(S.text6(a, "")) : Nat}
  %Equal.sym(Nat, Nat.sub(Nat.add(List.length(&2, Ip.Sym, Ip.Sym.list(S.text6(a, ""))), List.length(&2, Ip.Sym, Ip.Sym.list(t))), List.length(&2, Ip.Sym, Ip.Sym.list(t))), List.length(&2, Ip.Sym, Ip.Sym.list(S.text6(a, ""))), LRd.prd.sub_add(List.length(&2, Ip.Sym, Ip.Sym.list(S.text6(a, ""))), List.length(&2, Ip.Sym, Ip.Sym.list(t)))) : {_ == String.length(S.text6(a, "")) : Nat}
  LRd.prd.len_sym(S.text6(a, ""))

# The decision
# ------------

def pdc.ans(b: Bool, -n: Nat) -> {Ip.ans(b, n) == S.ans(b, n) : Maybe<&2, Nat>}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def pdc.counted(a: Ip.Addr) -> {Ip.counted(a) == S.counted(a) : Bool}:
  match a:
    case Ip.Full{gs, q}:
      match q:
        case None{}:
          {==}
        case Some{x}:
          {==}
    case Ip.Gap{l, r, q}:
      match q:
        case None{}:
          {==}
        case Some{x}:
          {==}

def pdc.dig_char(c: Char) -> {Char.is_digit(c) == S.dec(c) : Bool}:
  match c:
    case Chr{x}:
      {==}

def pdc.dig_in(g: String) -> {Ip.dig_in(g) == S.has_dec(g) : Bool}:
  match g:
    case SNil{}:
      {==}
    case SCon{+c, t}:
      %pdc.dig_char(c) : {Bool.or(Char.is_digit(c), Ip.dig_in(t)) == Bool.or(_, S.has_dec(t)) : Bool}
      %pdc.dig_in(t) : {Bool.or(Char.is_digit(c), Ip.dig_in(t)) == Bool.or(Char.is_digit(c), _) : Bool}
      {==}

def pdc.digs(gs: List<&2, String>) -> {Ip.digs(gs) == S.groups_dec(gs) : Bool}:
  match gs:
    case Nil{}:
      {==}
    case +g <> rest:
      %pdc.dig_in(g) : {Bool.or(Ip.dig_in(g), Ip.digs(rest)) == Bool.or(_, S.groups_dec(rest)) : Bool}
      %pdc.digs(rest) : {Bool.or(Ip.dig_in(g), Ip.digs(rest)) == Bool.or(Ip.dig_in(g), _) : Bool}
      {==}

def pdc.digit(a: Ip.Addr) -> {Ip.digit(a) == S.digit(a) : Bool}:
  match a:
    case Ip.Full{+gs, q}:
      %pdc.digs(gs) : {Bool.or(Ip.digs(gs), Maybe.is_some(&2, Ip.Quad, q)) == Bool.or(_, Maybe.is_some(&2, Ip.Quad, q)) : Bool}
      {==}
    case Ip.Gap{+l, +r, +q}:
      %pdc.digs(l) : {Bool.or(Ip.digs(l), Bool.or(Ip.digs(r), Maybe.is_some(&2, Ip.Quad, q))) == Bool.or(Bool.or(_, S.groups_dec(r)), Maybe.is_some(&2, Ip.Quad, q)) : Bool}
      %pdc.digs(r) : {Bool.or(Ip.digs(l), Bool.or(Ip.digs(r), Maybe.is_some(&2, Ip.Quad, q))) == Bool.or(Bool.or(Ip.digs(l), _), Maybe.is_some(&2, Ip.Quad, q)) : Bool}
      LIp.pip.or_assoc(Ip.digs(l), Ip.digs(r), Maybe.is_some(&2, Ip.Quad, q))

def pdc.after6(t: String) -> {Ip.after6(Ip.Sym.list(t)) == S.free(S.first(t)) : Bool}:
  match t:
    case SNil{}:
      {==}
    case SCon{+c, u}:
      LIp.pip.free_of(c)

def pdc.edge6_m(m: Maybe<&2, Char>) -> {Ip.edge6(m) == S.free(m) : Bool}:
  match m:
    case None{}:
      {==}
    case Some{+c}:
      LIp.pip.free_of(c)

# the last char of q's text, then s, is the spec's
def pdc.lastm_some(t: String, +c: Char) -> {LIp.pip.lastm(t, Some{c}) == S.last(SCon{c, t}) : Maybe<&2, Char>}:
  match t:
    case SNil{}:
      {==}
    case SCon{+d, u}:
      pdc.lastm_some(u, d)

def pdc.last2_snd(s: String, -p: Maybe<&2, Char>, +q: Maybe<&2, Char>) -> {Ip.last.of(Ip.last2(s, p, q)) == LIp.pip.lastm(s, q) : Maybe<&2, Char>}:
  match s:
    case SNil{}:
      {==}
    case SCon{+d, t}:
      pdc.last2_snd(t, q, Some{d})

def pdc.last(s: String) -> {Ip.last(s) == S.last(s) : Maybe<&2, Char>}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      Equal.trans(Maybe<&2, Char>, Ip.last.of(Ip.last2(t, None{}, Some{c})), LIp.pip.lastm(t, Some{c}), S.last(SCon{c, t}), pdc.last2_snd(t, None{}, Some{c}), pdc.lastm_some(t, c))

def pdc.edge6(+b: String) -> {Ip.edge6(Ip.last(b)) == S.free(S.last(b)) : Bool}:
  %Equal.sym(Maybe<&2, Char>, Ip.last(b), S.last(b), pdc.last(b)) : {Ip.edge6(_) == S.free(S.last(b)) : Bool}
  pdc.edge6_m(S.last(b))

def pdc.got.b(b: Bool, +a: Ip.Addr, +before: String, +t: String, +eb: {S.free(S.last(before)) == b : Bool}, +er: {Ip.read(Ip.Sym.list(S.text6(a, t)), Ip.Begin{}, Ip.Acc{False{}, Nil{}, Nil{}}) == Ip.Got{a, Ip.Sym.list(t)} : Ip.Read}) -> {Ip.v6.go(b, S.text6(a, t)) == S.take6(a, before, t) : Maybe<&2, Nat>}:
  match b:
    case False{}:
      %Equal.sym(Bool, S.free(S.last(before)), False{}, eb) : {None{} == S.ans(Bool.and(Bool.and(Bool.and(S.counted(a), S.digit(a)), _), S.free(S.first(t))), String.length(S.text6(a, ""))) : Maybe<&2, Nat>}
      %Equal.sym(Bool, Bool.and(Bool.and(S.counted(a), S.digit(a)), False{}), False{}, LIp.pip.and_false(Bool.and(S.counted(a), S.digit(a)))) : {None{} == S.ans(Bool.and(_, S.free(S.first(t))), String.length(S.text6(a, ""))) : Maybe<&2, Nat>}
      {==}
    case True{}:
      %Equal.sym(Ip.Read, Ip.read(Ip.Sym.list(S.text6(a, t)), Ip.Begin{}, Ip.Acc{False{}, Nil{}, Nil{}}), Ip.Got{a, Ip.Sym.list(t)}, er) : {Ip.v6.got(List.length(&2, Ip.Sym, Ip.Sym.list(S.text6(a, t))), _) == S.take6(a, before, t) : Maybe<&2, Nat>}
      %Equal.sym(Bool, Ip.counted(a), S.counted(a), pdc.counted(a)) : {Ip.ans(Bool.and(Bool.and(_, Ip.digit(a)), Ip.after6(Ip.Sym.list(t))), Nat.sub(List.length(&2, Ip.Sym, Ip.Sym.list(S.text6(a, t))), List.length(&2, Ip.Sym, Ip.Sym.list(t)))) == S.take6(a, before, t) : Maybe<&2, Nat>}
      %Equal.sym(Bool, Ip.digit(a), S.digit(a), pdc.digit(a)) : {Ip.ans(Bool.and(Bool.and(S.counted(a), _), Ip.after6(Ip.Sym.list(t))), Nat.sub(List.length(&2, Ip.Sym, Ip.Sym.list(S.text6(a, t))), List.length(&2, Ip.Sym, Ip.Sym.list(t)))) == S.take6(a, before, t) : Maybe<&2, Nat>}
      %Equal.sym(Bool, Ip.after6(Ip.Sym.list(t)), S.free(S.first(t)), pdc.after6(t)) : {Ip.ans(Bool.and(Bool.and(S.counted(a), S.digit(a)), _), Nat.sub(List.length(&2, Ip.Sym, Ip.Sym.list(S.text6(a, t))), List.length(&2, Ip.Sym, Ip.Sym.list(t)))) == S.take6(a, before, t) : Maybe<&2, Nat>}
      %Equal.sym(Nat, Nat.sub(List.length(&2, Ip.Sym, Ip.Sym.list(S.text6(a, t))), List.length(&2, Ip.Sym, Ip.Sym.list(t))), String.length(S.text6(a, "")), pdc.len6(a, t)) : {Ip.ans(Bool.and(Bool.and(S.counted(a), S.digit(a)), S.free(S.first(t))), _) == S.take6(a, before, t) : Maybe<&2, Nat>}
      %Equal.sym(Bool, S.free(S.last(before)), True{}, eb) : {Ip.ans(Bool.and(Bool.and(S.counted(a), S.digit(a)), S.free(S.first(t))), String.length(S.text6(a, ""))) == S.ans(Bool.and(Bool.and(Bool.and(S.counted(a), S.digit(a)), _), S.free(S.first(t))), String.length(S.text6(a, ""))) : Maybe<&2, Nat>}
      %Equal.sym(Bool, Bool.and(Bool.and(S.counted(a), S.digit(a)), True{}), Bool.and(S.counted(a), S.digit(a)), LIp.pip.and_true(Bool.and(S.counted(a), S.digit(a)))) : {Ip.ans(Bool.and(Bool.and(S.counted(a), S.digit(a)), S.free(S.first(t))), String.length(S.text6(a, ""))) == S.ans(Bool.and(_, S.free(S.first(t))), String.length(S.text6(a, ""))) : Maybe<&2, Nat>}
      pdc.ans(Bool.and(Bool.and(S.counted(a), S.digit(a)), S.free(S.first(t))), String.length(S.text6(a, "")))

# from what the reader reads, the decision is the spec's
def pdc.from_got(+a: Ip.Addr, +before: String, +t: String, +er: {Ip.read(Ip.Sym.list(S.text6(a, t)), Ip.Begin{}, Ip.Acc{False{}, Nil{}, Nil{}}) == Ip.Got{a, Ip.Sym.list(t)} : Ip.Read}) -> {Ip.v6(before, S.text6(a, t)) == S.take6(a, before, t) : Maybe<&2, Nat>}:
  pdc.got.b(Ip.edge6(Ip.last(before)), a, before, t, Equal.sym(Bool, Ip.edge6(Ip.last(before)), S.free(S.last(before)), pdc.edge6(before)), er)

# What the reader reads
# ---------------------

# an IPv6 with groups before its IPv4 (or none), shaped, then t
def pdc.read_full(+g: String, +rest: List<&2, String>, +q: Maybe<&2, Ip.Quad>, +t: String, +hg: {S.groups(g <> rest) == True{} : Bool}, +hq: {S.mquad_ok(q) == True{} : Bool}, +ht: {S.stops6(t) == True{} : Bool}) -> {Ip.read(Ip.Sym.list(S.text6(Ip.Full{g <> rest, q}, t)), Ip.Begin{}, Ip.Acc{False{}, Nil{}, Nil{}}) == Ip.Got{Ip.Full{g <> rest, q}, Ip.Sym.list(t)} : Ip.Read}:
  +hgg = LIp.pip.and_l(S.group(g), S.groups(rest), hg)
  +hgr = LIp.pip.and_r(S.group(g), S.groups(rest), hg)
  +rd = LIt.pit.more_begin(rest, q, g, Ip.Acc{False{}, Nil{}, Nil{}}, t, hgg, hgr, hq, ht, acc2 => LIt.pit.items_open(rest, q, acc2, t, hgr, hq, ht))
  %LIt.pit.pushes_l(rest, [g], Nil{}) : {Ip.read(Ip.Sym.list(S.text6(Ip.Full{g <> rest, q}, t)), Ip.Begin{}, Ip.Acc{False{}, Nil{}, Nil{}}) == Ip.Got{Ip.Acc.addr(_, q), Ip.Sym.list(t)} : Ip.Read}
  rd

# the groups after the `::` and the IPv4, then t, read after the `::`
def pdc.gap_tail(+r: List<&2, String>, +q: Maybe<&2, Ip.Quad>, +l: List<&2, String>, +t: String, +hr: {S.groups(r) == True{} : Bool}, +hq: {S.mquad_ok(q) == True{} : Bool}, +ht: {S.stops6(t) == True{} : Bool}) -> {Ip.read(Ip.Sym.list(S.join(List.append(&2, String, r, S.quad_items(q)), t)), Ip.Open{}, Ip.Acc{True{}, l, Nil{}}) == Ip.Got{Ip.Gap{l, r, q}, Ip.Sym.list(t)} : Ip.Read}:
  %LIt.pit.pushes_r(r, l, Nil{}) : {Ip.read(Ip.Sym.list(S.join(List.append(&2, String, r, S.quad_items(q)), t)), Ip.Open{}, Ip.Acc{True{}, l, Nil{}}) == Ip.Got{Ip.Acc.addr(_, q), Ip.Sym.list(t)} : Ip.Read}
  LIt.pit.items_open(r, q, Ip.Acc{True{}, l, Nil{}}, t, hr, hq, ht)

# an IPv6 with a `::`, shaped, then t
def pdc.read_gap(l: List<&2, String>, +r: List<&2, String>, +q: Maybe<&2, Ip.Quad>, +t: String, +hl: {S.groups(l) == True{} : Bool}, +hr: {S.groups(r) == True{} : Bool}, +hq: {S.mquad_ok(q) == True{} : Bool}, +ht: {S.stops6(t) == True{} : Bool}) -> {Ip.read(Ip.Sym.list(S.text6(Ip.Gap{l, r, q}, t)), Ip.Begin{}, Ip.Acc{False{}, Nil{}, Nil{}}) == Ip.Got{Ip.Gap{l, r, q}, Ip.Sym.list(t)} : Ip.Read}:
  match l:
    case Nil{}:
      pdc.gap_tail(r, q, Nil{}, t, hr, hq, ht)
    case +g <> +rest:
      +J = S.join(List.append(&2, String, r, S.quad_items(q)), t)
      Equal.trans(Ip.Read, Ip.read(Ip.Sym.list(S.join(g <> rest, SCon{':', SCon{':', J}})), Ip.Begin{}, Ip.Acc{False{}, Nil{}, Nil{}}), Ip.read(Ip.Sym.list(J), Ip.Open{}, Ip.Acc{True{}, g <> rest, Nil{}}), Ip.Got{Ip.Gap{g <> rest, r, q}, Ip.Sym.list(t)}, LIt.pit.left_begin(rest, g, J, Nil{}, Nil{}, hl), pdc.gap_tail(r, q, g <> rest, t, hr, hq, ht))

# the reader answers none on a text with no address at its start
def pdc.v6_bad(b: Bool, +t: String, +ht: {S.stops6(t) == True{} : Bool}) -> {Ip.v6.go(b, t) == None{} : Maybe<&2, Nat>}:
  match b:
    case False{}:
      {==}
    case True{}:
      %Equal.sym(Ip.Read, Ip.read(Ip.Sym.list(t), Ip.Begin{}, Ip.Acc{False{}, Nil{}, Nil{}}), Ip.Bad{}, LRd.prd.begin_end(t, Ip.Acc{False{}, Nil{}, Nil{}}, ht)) : {Ip.v6.got(List.length(&2, Ip.Sym, Ip.Sym.list(t)), _) == None{} : Maybe<&2, Nat>}
      {==}

# an IPv4 alone, then t, read from the start of the text
def pdc.read_q(+x: Ip.Quad, +t: String, +hq: {S.quad_ok(x) == True{} : Bool}, +ht: {S.stops6(t) == True{} : Bool}) -> {Ip.read(Ip.Sym.list(S.text6(Ip.Full{Nil{}, Some{x}}, t)), Ip.Begin{}, Ip.Acc{False{}, Nil{}, Nil{}}) == Ip.Got{Ip.Full{Nil{}, Some{x}}, Ip.Sym.list(t)} : Ip.Read}:
  +hs = LRd.prd.drun_end4(t, LRd.prd.stops6_4(t, ht))
  %Equal.sym(String, String.append(S.quad_text(x, ""), t), S.quad_text(x, t), LQd.pqd.qt_app(x, t)) : {Ip.read(Ip.Sym.list(_), Ip.Begin{}, Ip.Acc{False{}, Nil{}, Nil{}}) == Ip.Got{Ip.Full{Nil{}, Some{x}}, Ip.Sym.list(t)} : Ip.Read}
  LQd.pqd.quad_begin(x, t, Ip.Acc{False{}, Nil{}, Nil{}}, hq, hs)

# an IPv6 with no group before its IPv4, then t
def pdc.full_nil(q: Maybe<&2, Ip.Quad>, +before: String, +t: String, +hq: {S.mquad_ok(q) == True{} : Bool}, +ht: {S.stops6(t) == True{} : Bool}) -> {Ip.v6(before, S.text6(Ip.Full{Nil{}, q}, t)) == S.take6(Ip.Full{Nil{}, q}, before, t) : Maybe<&2, Nat>}:
  match q:
    case None{}:
      pdc.v6_bad(Ip.edge6(Ip.last(before)), t, ht)
    case Some{+x}:
      pdc.from_got(Ip.Full{Nil{}, Some{x}}, before, t, pdc.read_q(x, t, hq, ht))

# every shaped IPv6, then t, is decided as the spec decides
def pdc.decides(a: Ip.Addr, +before: String, +t: String, +sh: {S.shaped(a) == True{} : Bool}, +st: {S.stops6(t) == True{} : Bool}) -> {Ip.v6(before, S.text6(a, t)) == S.take6(a, before, t) : Maybe<&2, Nat>}:
  match a:
    case Ip.Full{gs, +q}:
      match gs:
        case Nil{}:
          pdc.full_nil(q, before, t, sh, st)
        case +g <> +rest:
          +hg = LIp.pip.and_l(S.groups(g <> rest), S.mquad_ok(q), sh)
          +hq = LIp.pip.and_r(S.groups(g <> rest), S.mquad_ok(q), sh)
          pdc.from_got(Ip.Full{g <> rest, q}, before, t, pdc.read_full(g, rest, q, t, hg, hq, st))
    case Ip.Gap{+l, +r, +q}:
      +hlr = LIp.pip.and_l(Bool.and(S.groups(l), S.groups(r)), S.mquad_ok(q), sh)
      +hq = LIp.pip.and_r(Bool.and(S.groups(l), S.groups(r)), S.mquad_ok(q), sh)
      +hl = LIp.pip.and_l(S.groups(l), S.groups(r), hlr)
      +hr = LIp.pip.and_r(S.groups(l), S.groups(r), hlr)
      pdc.from_got(Ip.Gap{l, r, q}, before, t, pdc.read_gap(l, r, q, t, hl, hr, hq, st))
