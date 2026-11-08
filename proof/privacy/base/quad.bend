# eukhe: lemmas shared by the proofs of area privacy, section ip: an
# octet and an IPv4 as the spec writes them, read by the grammar

import Base
import ../../../bend/privacy/ip.bend as Ip
import ../../../bend/privacy/context.bend as Cx
import ../../../spec/harness/privacy.bend as S
import ./chars.bend as LIp
import ./read.bend as LRd

def pqd.and_i(a: Bool, -b: Bool, +ea: {a == True{} : Bool}, +eb: {b == True{} : Bool}) -> {Bool.and(a, b) == True{} : Bool}:
  match a:
    case True{}:
      eb
    case False{}:
      LIp.pip.absurd_ft({Bool.and(False{}, b) == True{} : Bool}, ea)

# a decimal digit is a hex digit
def pqd.dec_hex(c: Char, +h: {S.dec(c) == True{} : Bool}) -> {S.hex(c) == True{} : Bool}:
  match c:
    case Chr{+x}:
      %Equal.sym(Bool, S.in(x, 48, 57), True{}, h) : {Bool.or(_, Bool.or(S.in(x, 97, 102), S.in(x, 65, 70))) == True{} : Bool}
      {==}

# what an octet the spec writes is: the grammar's octet, decimal digits,
# a group
def pqd.Facts(o: String) -> Type:
  {Ip.oct_ok(o) == True{} : Bool} & ({S.all_dec(o) == True{} : Bool} & {S.group(o) == True{} : Bool})

def pqd.facts3(+a: Char, +b: Char, +c: Char, +h: {S.octet(SCon{a, SCon{b, SCon{c, SNil{}}}}) == True{} : Bool}) -> pqd.Facts(SCon{a, SCon{b, SCon{c, SNil{}}}}):
  match a b c:
    case Chr{+x} Chr{+y} Chr{+z}:
      +h1 = LIp.pip.and_l(Bool.and(Bool.and(S.dec(Chr{x}), S.dec(Chr{y})), Bool.and(S.dec(Chr{z}), Bool.not(Char.is_eq(Chr{x}, '0')))), Ip.le255(Chr{x}, Chr{y}, Chr{z}), h)
      +hle = LIp.pip.and_r(Bool.and(Bool.and(S.dec(Chr{x}), S.dec(Chr{y})), Bool.and(S.dec(Chr{z}), Bool.not(Char.is_eq(Chr{x}, '0')))), Ip.le255(Chr{x}, Chr{y}, Chr{z}), h)
      +hab = LIp.pip.and_l(Bool.and(S.dec(Chr{x}), S.dec(Chr{y})), Bool.and(S.dec(Chr{z}), Bool.not(Char.is_eq(Chr{x}, '0'))), h1)
      +hc0 = LIp.pip.and_r(Bool.and(S.dec(Chr{x}), S.dec(Chr{y})), Bool.and(S.dec(Chr{z}), Bool.not(Char.is_eq(Chr{x}, '0'))), h1)
      +ha = LIp.pip.and_l(S.dec(Chr{x}), S.dec(Chr{y}), hab)
      +hb = LIp.pip.and_r(S.dec(Chr{x}), S.dec(Chr{y}), hab)
      +hc = LIp.pip.and_l(S.dec(Chr{z}), Bool.not(Char.is_eq(Chr{x}, '0')), hc0)
      +h0 = LIp.pip.and_r(S.dec(Chr{z}), Bool.not(Char.is_eq(Chr{x}, '0')), hc0)
      (pqd.and_i(Bool.not(Char.is_eq(Chr{x}, '0')), Ip.le255(Chr{x}, Chr{y}, Chr{z}), h0, hle), (pqd.and_i(S.dec(Chr{x}), Bool.and(S.dec(Chr{y}), Bool.and(S.dec(Chr{z}), True{})), ha, pqd.and_i(S.dec(Chr{y}), Bool.and(S.dec(Chr{z}), True{}), hb, pqd.and_i(S.dec(Chr{z}), True{}, hc, {==}))), pqd.and_i(S.all_hex(SCon{Chr{x}, SCon{Chr{y}, SCon{Chr{z}, SNil{}}}}), True{}, pqd.and_i(S.hex(Chr{x}), Bool.and(S.hex(Chr{y}), Bool.and(S.hex(Chr{z}), True{})), pqd.dec_hex(Chr{x}, ha), pqd.and_i(S.hex(Chr{y}), Bool.and(S.hex(Chr{z}), True{}), pqd.dec_hex(Chr{y}, hb), pqd.and_i(S.hex(Chr{z}), True{}, pqd.dec_hex(Chr{z}, hc), {==}))), {==})))

def pqd.facts(o: String, +h: {S.octet(o) == True{} : Bool}) -> pqd.Facts(o):
  match o:
    case SNil{}:
      LIp.pip.absurd_ft(pqd.Facts(SNil{}), h)
    case SCon{+a, t1}:
      match t1:
        case SNil{}:
          ({==}, (pqd.and_i(S.dec(a), True{}, h, {==}), pqd.and_i(S.all_hex(SCon{a, SNil{}}), True{}, pqd.and_i(S.hex(a), True{}, pqd.dec_hex(a, h), {==}), {==})))
        case SCon{+b, t2}:
          match t2:
            case SNil{}:
              +hab = LIp.pip.and_l(Bool.and(S.dec(a), S.dec(b)), Bool.not(Char.is_eq(a, '0')), h)
              +h0 = LIp.pip.and_r(Bool.and(S.dec(a), S.dec(b)), Bool.not(Char.is_eq(a, '0')), h)
              +ha = LIp.pip.and_l(S.dec(a), S.dec(b), hab)
              +hb = LIp.pip.and_r(S.dec(a), S.dec(b), hab)
              (h0, (pqd.and_i(S.dec(a), Bool.and(S.dec(b), True{}), ha, pqd.and_i(S.dec(b), True{}, hb, {==})), pqd.and_i(S.all_hex(SCon{a, SCon{b, SNil{}}}), True{}, pqd.and_i(S.hex(a), Bool.and(S.hex(b), True{}), pqd.dec_hex(a, ha), pqd.and_i(S.hex(b), True{}, pqd.dec_hex(b, hb), {==})), {==})))
            case SCon{+c, t3}:
              match t3:
                case SNil{}:
                  pqd.facts3(a, b, c, h)
                case SCon{d, t4}:
                  LIp.pip.absurd_ft(pqd.Facts(SCon{a, SCon{b, SCon{c, SCon{d, t4}}}}), h)

def pqd.app_nil_cut(+o: String, +X: List<&2, Ip.Sym>, +hx: {Ip.drun(X) == Ip.Cut{SNil{}, X} : Ip.Cut}) -> {Ip.Cut{String.append(o, LRd.prd.cut_s(Ip.drun(X))), LRd.prd.cut_rest(Ip.drun(X))} == Ip.Cut{o, X} : Ip.Cut}:
  %Equal.sym(Ip.Cut, Ip.drun(X), Ip.Cut{SNil{}, X}, hx) : {Ip.Cut{String.append(o, LRd.prd.cut_s(_)), LRd.prd.cut_rest(_)} == Ip.Cut{o, X} : Ip.Cut}
  %Equal.sym(String, String.append(o, SNil{}), o, LRd.prd.app_nil(o)) : {Ip.Cut{_, X} == Ip.Cut{o, X} : Ip.Cut}
  {==}

def pqd.f_ok(-o: String, f: pqd.Facts(o)) -> {Ip.oct_ok(o) == True{} : Bool}:
  (a, r) = f
  a

def pqd.f_dec(-o: String, f: pqd.Facts(o)) -> {S.all_dec(o) == True{} : Bool}:
  (a, r) = f
  (b, c) = r
  b

def pqd.f_grp(-o: String, f: pqd.Facts(o)) -> {S.group(o) == True{} : Bool}:
  (a, r) = f
  (b, c) = r
  c

# an octet the spec writes, then X (no digit next): the grammar's octet
def pqd.oct_read(+o: String, +X: List<&2, Ip.Sym>, +h: {S.octet(o) == True{} : Bool}, +hx: {Ip.drun(X) == Ip.Cut{SNil{}, X} : Ip.Cut}) -> {Ip.oct(List.append(&2, Ip.Sym, Ip.Sym.list(o), X)) == Some{Ip.Cut{o, X}} : Maybe<&2, Ip.Cut>}:
  +ok = pqd.f_ok(o, pqd.facts(o, h))
  +dc = pqd.f_dec(o, pqd.facts(o, h))
  %Equal.sym(Ip.Cut, Ip.drun(List.append(&2, Ip.Sym, Ip.Sym.list(o), X)), Ip.Cut{String.append(o, LRd.prd.cut_s(Ip.drun(X))), LRd.prd.cut_rest(Ip.drun(X))}, LRd.prd.drun_dec(o, X, dc)) : {Ip.oct.of(_) == Some{Ip.Cut{o, X}} : Maybe<&2, Ip.Cut>}
  %Equal.sym(Ip.Cut, Ip.Cut{String.append(o, LRd.prd.cut_s(Ip.drun(X))), LRd.prd.cut_rest(Ip.drun(X))}, Ip.Cut{o, X}, pqd.app_nil_cut(o, X, hx)) : {Ip.oct.of(_) == Some{Ip.Cut{o, X}} : Maybe<&2, Ip.Cut>}
  %Equal.sym(Bool, Ip.oct_ok(o), True{}, ok) : {Ip.oct.ok(_, o, X) == Some{Ip.Cut{o, X}} : Maybe<&2, Ip.Cut>}
  {==}

# the IPv4 the spec writes, then t (no digit next): the grammar's quad
def pqd.quad_read(q: Ip.Quad, +t: String, +h: {S.quad_ok(q) == True{} : Bool}, +hs: {Ip.drun(Ip.Sym.list(t)) == Ip.Cut{SNil{}, Ip.Sym.list(t)} : Ip.Cut}) -> {Ip.quad(Ip.Sym.list(S.quad_text(q, t))) == Some{Ip.QCut{q, Ip.Sym.list(t)}} : Maybe<&2, Ip.QCut>}:
  match q:
    case Ip.Quad{+a, +b, +c, +d}:
      +hab = LIp.pip.and_l(Bool.and(S.octet(a), S.octet(b)), Bool.and(S.octet(c), S.octet(d)), h)
      +hcd = LIp.pip.and_r(Bool.and(S.octet(a), S.octet(b)), Bool.and(S.octet(c), S.octet(d)), h)
      +ha = LIp.pip.and_l(S.octet(a), S.octet(b), hab)
      +hb = LIp.pip.and_r(S.octet(a), S.octet(b), hab)
      +hc = LIp.pip.and_l(S.octet(c), S.octet(d), hcd)
      +hd = LIp.pip.and_r(S.octet(c), S.octet(d), hcd)
      %Equal.sym(List<&2, Ip.Sym>, Ip.Sym.list(String.append(a, SCon{'.', String.append(b, SCon{'.', String.append(c, SCon{'.', String.append(d, t)})})})), List.append(&2, Ip.Sym, Ip.Sym.list(a), Ip.Sym.list(SCon{'.', String.append(b, SCon{'.', String.append(c, SCon{'.', String.append(d, t)})})})), LRd.prd.sym_app(a, SCon{'.', String.append(b, SCon{'.', String.append(c, SCon{'.', String.append(d, t)})})})) : {Ip.quad.a(Ip.oct(_)) == Some{Ip.QCut{Ip.Quad{a, b, c, d}, Ip.Sym.list(t)}} : Maybe<&2, Ip.QCut>}
      %Equal.sym(Maybe<&2, Ip.Cut>, Ip.oct(List.append(&2, Ip.Sym, Ip.Sym.list(a), Ip.Sym.list(SCon{'.', String.append(b, SCon{'.', String.append(c, SCon{'.', String.append(d, t)})})}))), Some{Ip.Cut{a, Ip.Sym.list(SCon{'.', String.append(b, SCon{'.', String.append(c, SCon{'.', String.append(d, t)})})})}}, pqd.oct_read(a, Ip.Sym.list(SCon{'.', String.append(b, SCon{'.', String.append(c, SCon{'.', String.append(d, t)})})}), ha, {==})) : {Ip.quad.a(_) == Some{Ip.QCut{Ip.Quad{a, b, c, d}, Ip.Sym.list(t)}} : Maybe<&2, Ip.QCut>}
      %Equal.sym(List<&2, Ip.Sym>, Ip.Sym.list(String.append(b, SCon{'.', String.append(c, SCon{'.', String.append(d, t)})})), List.append(&2, Ip.Sym, Ip.Sym.list(b), Ip.Sym.list(SCon{'.', String.append(c, SCon{'.', String.append(d, t)})})), LRd.prd.sym_app(b, SCon{'.', String.append(c, SCon{'.', String.append(d, t)})})) : {Ip.quad.b(a, Ip.oct(_)) == Some{Ip.QCut{Ip.Quad{a, b, c, d}, Ip.Sym.list(t)}} : Maybe<&2, Ip.QCut>}
      %Equal.sym(Maybe<&2, Ip.Cut>, Ip.oct(List.append(&2, Ip.Sym, Ip.Sym.list(b), Ip.Sym.list(SCon{'.', String.append(c, SCon{'.', String.append(d, t)})}))), Some{Ip.Cut{b, Ip.Sym.list(SCon{'.', String.append(c, SCon{'.', String.append(d, t)})})}}, pqd.oct_read(b, Ip.Sym.list(SCon{'.', String.append(c, SCon{'.', String.append(d, t)})}), hb, {==})) : {Ip.quad.b(a, _) == Some{Ip.QCut{Ip.Quad{a, b, c, d}, Ip.Sym.list(t)}} : Maybe<&2, Ip.QCut>}
      %Equal.sym(List<&2, Ip.Sym>, Ip.Sym.list(String.append(c, SCon{'.', String.append(d, t)})), List.append(&2, Ip.Sym, Ip.Sym.list(c), Ip.Sym.list(SCon{'.', String.append(d, t)})), LRd.prd.sym_app(c, SCon{'.', String.append(d, t)})) : {Ip.quad.c(a, b, Ip.oct(_)) == Some{Ip.QCut{Ip.Quad{a, b, c, d}, Ip.Sym.list(t)}} : Maybe<&2, Ip.QCut>}
      %Equal.sym(Maybe<&2, Ip.Cut>, Ip.oct(List.append(&2, Ip.Sym, Ip.Sym.list(c), Ip.Sym.list(SCon{'.', String.append(d, t)}))), Some{Ip.Cut{c, Ip.Sym.list(SCon{'.', String.append(d, t)})}}, pqd.oct_read(c, Ip.Sym.list(SCon{'.', String.append(d, t)}), hc, {==})) : {Ip.quad.c(a, b, _) == Some{Ip.QCut{Ip.Quad{a, b, c, d}, Ip.Sym.list(t)}} : Maybe<&2, Ip.QCut>}
      %Equal.sym(List<&2, Ip.Sym>, Ip.Sym.list(String.append(d, t)), List.append(&2, Ip.Sym, Ip.Sym.list(d), Ip.Sym.list(t)), LRd.prd.sym_app(d, t)) : {Ip.quad.d(a, b, c, Ip.oct(_)) == Some{Ip.QCut{Ip.Quad{a, b, c, d}, Ip.Sym.list(t)}} : Maybe<&2, Ip.QCut>}
      %Equal.sym(Maybe<&2, Ip.Cut>, Ip.oct(List.append(&2, Ip.Sym, Ip.Sym.list(d), Ip.Sym.list(t))), Some{Ip.Cut{d, Ip.Sym.list(t)}}, pqd.oct_read(d, Ip.Sym.list(t), hd, hs)) : {Ip.quad.d(a, b, c, _) == Some{Ip.QCut{Ip.Quad{a, b, c, d}, Ip.Sym.list(t)}} : Maybe<&2, Ip.QCut>}
      {==}

# the IPv4 the spec writes, then t, read from where a group may start
def pqd.quad_open(q: Ip.Quad, +t: String, +acc: Ip.Acc, +h: {S.quad_ok(q) == True{} : Bool}, +hs: {Ip.drun(Ip.Sym.list(t)) == Ip.Cut{SNil{}, Ip.Sym.list(t)} : Ip.Cut}) -> {Ip.read(Ip.Sym.list(S.quad_text(q, t)), Ip.Open{}, acc) == Ip.finish(acc, Some{q}, Ip.Sym.list(t)) : Ip.Read}:
  match q:
    case Ip.Quad{+a, +b, +c, +d}:
      +ha = LIp.pip.and_l(S.octet(a), S.octet(b), LIp.pip.and_l(Bool.and(S.octet(a), S.octet(b)), Bool.and(S.octet(c), S.octet(d)), h))
      +gp = pqd.f_grp(a, pqd.facts(a, ha))
      +qr = pqd.quad_read(Ip.Quad{a, b, c, d}, t, h, hs)
      %Equal.sym(List<&2, Ip.Sym>, Ip.Sym.list(String.append(a, SCon{'.', String.append(b, SCon{'.', String.append(c, SCon{'.', String.append(d, t)})})})), List.append(&2, Ip.Sym, Ip.Sym.list(a), Ip.Sym.list(SCon{'.', String.append(b, SCon{'.', String.append(c, SCon{'.', String.append(d, t)})})})), LRd.prd.sym_app(a, SCon{'.', String.append(b, SCon{'.', String.append(c, SCon{'.', String.append(d, t)})})})) : {Ip.read(_, Ip.Open{}, acc) == Ip.finish(acc, Some{Ip.Quad{a, b, c, d}}, Ip.Sym.list(t)) : Ip.Read}
      %Equal.sym(Ip.Read, Ip.read(List.append(&2, Ip.Sym, Ip.Sym.list(a), Ip.Sym.list(SCon{'.', String.append(b, SCon{'.', String.append(c, SCon{'.', String.append(d, t)})})})), Ip.Open{}, acc), Ip.read(Ip.Sym.list(SCon{'.', String.append(b, SCon{'.', String.append(c, SCon{'.', String.append(d, t)})})}), Ip.Grp{List.append(&2, Ip.Sym, Ip.Sym.list(a), Ip.Sym.list(SCon{'.', String.append(b, SCon{'.', String.append(c, SCon{'.', String.append(d, t)})})})), LRd.prd.room(a)}, acc), LRd.prd.group_open(a, Ip.Sym.list(SCon{'.', String.append(b, SCon{'.', String.append(c, SCon{'.', String.append(d, t)})})}), acc, gp)) : {_ == Ip.finish(acc, Some{Ip.Quad{a, b, c, d}}, Ip.Sym.list(t)) : Ip.Read}
      %LRd.prd.sym_app(a, SCon{'.', String.append(b, SCon{'.', String.append(c, SCon{'.', String.append(d, t)})})}) : {Ip.quad_end(acc, Ip.quad(_)) == Ip.finish(acc, Some{Ip.Quad{a, b, c, d}}, Ip.Sym.list(t)) : Ip.Read}
      %Equal.sym(Maybe<&2, Ip.QCut>, Ip.quad(Ip.Sym.list(String.append(a, SCon{'.', String.append(b, SCon{'.', String.append(c, SCon{'.', String.append(d, t)})})}))), Some{Ip.QCut{Ip.Quad{a, b, c, d}, Ip.Sym.list(t)}}, qr) : {Ip.quad_end(acc, _) == Ip.finish(acc, Some{Ip.Quad{a, b, c, d}}, Ip.Sym.list(t)) : Ip.Read}
      {==}

# the IPv4 the spec writes, then t, read from the start of the text
def pqd.quad_begin(q: Ip.Quad, +t: String, +acc: Ip.Acc, +h: {S.quad_ok(q) == True{} : Bool}, +hs: {Ip.drun(Ip.Sym.list(t)) == Ip.Cut{SNil{}, Ip.Sym.list(t)} : Ip.Cut}) -> {Ip.read(Ip.Sym.list(S.quad_text(q, t)), Ip.Begin{}, acc) == Ip.finish(acc, Some{q}, Ip.Sym.list(t)) : Ip.Read}:
  match q:
    case Ip.Quad{+a, +b, +c, +d}:
      +ha = LIp.pip.and_l(S.octet(a), S.octet(b), LIp.pip.and_l(Bool.and(S.octet(a), S.octet(b)), Bool.and(S.octet(c), S.octet(d)), h))
      +gp = pqd.f_grp(a, pqd.facts(a, ha))
      +qr = pqd.quad_read(Ip.Quad{a, b, c, d}, t, h, hs)
      %Equal.sym(List<&2, Ip.Sym>, Ip.Sym.list(String.append(a, SCon{'.', String.append(b, SCon{'.', String.append(c, SCon{'.', String.append(d, t)})})})), List.append(&2, Ip.Sym, Ip.Sym.list(a), Ip.Sym.list(SCon{'.', String.append(b, SCon{'.', String.append(c, SCon{'.', String.append(d, t)})})})), LRd.prd.sym_app(a, SCon{'.', String.append(b, SCon{'.', String.append(c, SCon{'.', String.append(d, t)})})})) : {Ip.read(_, Ip.Begin{}, acc) == Ip.finish(acc, Some{Ip.Quad{a, b, c, d}}, Ip.Sym.list(t)) : Ip.Read}
      %Equal.sym(Ip.Read, Ip.read(List.append(&2, Ip.Sym, Ip.Sym.list(a), Ip.Sym.list(SCon{'.', String.append(b, SCon{'.', String.append(c, SCon{'.', String.append(d, t)})})})), Ip.Begin{}, acc), Ip.read(Ip.Sym.list(SCon{'.', String.append(b, SCon{'.', String.append(c, SCon{'.', String.append(d, t)})})}), Ip.Grp{List.append(&2, Ip.Sym, Ip.Sym.list(a), Ip.Sym.list(SCon{'.', String.append(b, SCon{'.', String.append(c, SCon{'.', String.append(d, t)})})})), LRd.prd.room(a)}, acc), LRd.prd.group_begin(a, Ip.Sym.list(SCon{'.', String.append(b, SCon{'.', String.append(c, SCon{'.', String.append(d, t)})})}), acc, gp)) : {_ == Ip.finish(acc, Some{Ip.Quad{a, b, c, d}}, Ip.Sym.list(t)) : Ip.Read}
      %LRd.prd.sym_app(a, SCon{'.', String.append(b, SCon{'.', String.append(c, SCon{'.', String.append(d, t)})})}) : {Ip.quad_end(acc, Ip.quad(_)) == Ip.finish(acc, Some{Ip.Quad{a, b, c, d}}, Ip.Sym.list(t)) : Ip.Read}
      %Equal.sym(Maybe<&2, Ip.QCut>, Ip.quad(Ip.Sym.list(String.append(a, SCon{'.', String.append(b, SCon{'.', String.append(c, SCon{'.', String.append(d, t)})})}))), Some{Ip.QCut{Ip.Quad{a, b, c, d}, Ip.Sym.list(t)}}, qr) : {Ip.quad_end(acc, _) == Ip.finish(acc, Some{Ip.Quad{a, b, c, d}}, Ip.Sym.list(t)) : Ip.Read}
      {==}

# an IPv4 written alone, then t, is the IPv4 written before t
def pqd.qt_app(q: Ip.Quad, +t: String) -> {String.append(S.quad_text(q, ""), t) == S.quad_text(q, t) : String}:
  match q:
    case Ip.Quad{+a, +b, +c, +d}:
      %Equal.sym(String, String.append(String.append(a, SCon{'.', String.append(b, SCon{'.', String.append(c, SCon{'.', String.append(d, "")})})}), t), String.append(a, String.append(SCon{'.', String.append(b, SCon{'.', String.append(c, SCon{'.', String.append(d, "")})})}, t)), LRd.prd.app_assoc(a, SCon{'.', String.append(b, SCon{'.', String.append(c, SCon{'.', String.append(d, "")})})}, t)) : {_ == S.quad_text(Ip.Quad{a, b, c, d}, t) : String}
      %Equal.sym(String, String.append(String.append(b, SCon{'.', String.append(c, SCon{'.', String.append(d, "")})}), t), String.append(b, String.append(SCon{'.', String.append(c, SCon{'.', String.append(d, "")})}, t)), LRd.prd.app_assoc(b, SCon{'.', String.append(c, SCon{'.', String.append(d, "")})}, t)) : {String.append(a, SCon{'.', _}) == S.quad_text(Ip.Quad{a, b, c, d}, t) : String}
      %Equal.sym(String, String.append(String.append(c, SCon{'.', String.append(d, "")}), t), String.append(c, String.append(SCon{'.', String.append(d, "")}, t)), LRd.prd.app_assoc(c, SCon{'.', String.append(d, "")}, t)) : {String.append(a, SCon{'.', String.append(b, SCon{'.', _})}) == S.quad_text(Ip.Quad{a, b, c, d}, t) : String}
      %Equal.sym(String, String.append(String.append(d, ""), t), String.append(d, String.append("", t)), LRd.prd.app_assoc(d, "", t)) : {String.append(a, SCon{'.', String.append(b, SCon{'.', String.append(c, SCon{'.', _})})}) == S.quad_text(Ip.Quad{a, b, c, d}, t) : String}
      {==}
